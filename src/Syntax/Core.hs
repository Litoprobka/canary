{-# LANGUAGE DerivingVia #-}

module Syntax.Core where

import Common (
    Index (..),
    Level (..),
    Literal,
    Name,
    Name_ (ConsName, NilName, TypeName),
    PrettyAnsi (..),
    SimpleName_,
    UnAnnotate (..),
    UniVar,
    conColor,
    keyword,
    specSym,
    typeColor,
    pattern L,
 )
import Data.List ((!!))
import Data.Row (ExtRow (..), OpenName, Row, prettyRecord, prettyVariant, sortedRow)
import Data.Vector qualified as Vec
import LangPrelude
import Prettyprinter
import Prettyprinter.Render.Terminal (AnsiStyle)
import Syntax.Term (Erasure (..), Quantifier (..), Visibility (..), withVis)

data CorePattern
    = VarP SimpleName_
    | ConstructorP Name_ [(Visibility, SimpleName_)]
    | VariantP OpenName SimpleName_
    | RecordP (Row SimpleName_)
    | SigmaP Visibility SimpleName_ SimpleName_
    | LiteralP Literal

instance PrettyAnsi CorePattern where
    prettyAnsi opts = \case
        VarP name -> prettyAnsi opts name
        ConstructorP name [] -> prettyCon name
        ConstructorP name args -> parens $ hsep (prettyCon name : map (\(vis, arg) -> withVis vis (prettyAnsi opts arg)) args)
        VariantP name arg -> parens $ prettyCon name <+> prettyAnsi opts arg
        RecordP row -> braces . sep . punctuate comma . map recordField $ sortedRow row
        SigmaP vis lhs rhs -> parens $ withVis vis (pretty lhs) <+> "**" <+> pretty rhs
        LiteralP lit -> prettyAnsi opts lit
      where
        prettyCon name = conColor $ prettyAnsi opts name
        recordField (name, pat) = prettyAnsi opts name <+> "=" <+> prettyAnsi opts pat

type CoreType = CoreTerm

data CoreTerm
    = Var Index
    | Name Name
    | -- TyCon and Con are treated more or less the same way everywhere
      -- it could have made sense to merge them, except an optimised representation of Con
      -- would probably store a constructor tag (e.g. 0 for False, 1 for True) instead of a global name
      -- I guess, for now it's easier to keep the redundant TyCon
      TyCon Name (Vector (Visibility, CoreTerm))
    | Con Name (Vector (Visibility, CoreTerm))
    | Variant OpenName CoreTerm
    | Lambda Visibility SimpleName_ CoreTerm
    | App Visibility CoreTerm CoreTerm
    | Case CoreTerm [(CorePattern, CoreTerm)]
    | Let SimpleName_ CoreTerm CoreTerm
    | Literal Literal
    | Record (Row CoreTerm)
    | Sigma CoreTerm CoreTerm
    | -- types
      Q Quantifier Visibility Erasure SimpleName_ CoreType CoreTerm
    | VariantT (ExtRow CoreType)
    | RecordT (ExtRow CoreType)
    | UniVar UniVar
    | AppPruning CoreTerm Pruning
    deriving (Pretty, Show) via (UnAnnotate CoreTerm)

newtype Pruning = Pruning {getPruning :: [Maybe Visibility]}
newtype ReversedPruning = ReversedPruning [Maybe Visibility]

reversedPruning :: Pruning -> ReversedPruning
reversedPruning = ReversedPruning . reverse . (.getPruning)

instance PrettyAnsi CoreTerm where
    prettyAnsi opts = go 0 []
      where
        go :: Int -> [Doc AnsiStyle] -> CoreTerm -> Doc AnsiStyle
        go n env term = case term of
            Var index
                | index.getIndex >= length env || index.getIndex < 0 -> "#" <> pretty index.getIndex
                | otherwise -> env !! index.getIndex
            Name name -> prettyAnsi opts name
            TyCon name Nil -> typeColor $ prettyAnsi opts name
            TyCon name args -> parensWhen 3 $ hsep (typeColor (prettyAnsi opts name) : map (\(vis, t) -> withVis vis (go 3 env t)) (Vec.toList args))
            -- list sugar doesn't really make sense with explicit type applications, perhaps I should remove it
            -- another option is `[a, b, c] @ty`
            Con (L ConsName) (_ty :< (_, x) :< (_, Con (L NilName) Nil) :< Nil) -> brackets $ go 0 env x
            Con (L ConsName) (_ty :< (_, x) :< (_, xs) :< Nil) | Just output <- prettyConsNil xs -> brackets $ go 0 env x <> output
            Con (L NilName) (_ty :< Nil) -> "[]"
            Con name Nil -> conColor $ prettyAnsi opts name
            Con name args -> parensWhen 3 $ hsep (conColor (prettyAnsi opts name) : map (\(vis, t) -> withVis vis (go 3 env t)) (Vec.toList args))
            lambda@Lambda{} -> parensWhen 1 $ specSym "λ" <> compressLambda env lambda
            App vis lhs rhs -> parensWhen 3 $ go 2 env lhs <+> withVis vis (go 3 env rhs)
            Record row -> prettyRecord "=" (prettyAnsi opts) (go 0 env) (NoExtRow row)
            Sigma x y -> parensWhen 1 $ go 0 env x <+> specSym "**" <+> go 0 env y
            Variant name arg -> parensWhen 3 $ conColor (prettyAnsi opts name) <+> go 3 env arg
            Case arg matches ->
                nest
                    4
                    ( vsep $
                        (keyword "case" <+> go 0 env arg <+> keyword "of" :) $
                            matches <&> \(pat, body) -> prettyAnsi opts pat <+> specSym "->" <+> go 0 (patternVars pat <> env) body
                    )
            Let name body expr -> keyword "let" <+> prettyAnsi opts name <+> specSym "=" <+> go 0 env body <> ";" <+> go 0 env expr
            Literal lit -> prettyAnsi opts lit
            -- checking for variable occurances here is not ideal (potentially O(n^2) in AST size),
            Q Forall Visible _e var ty body | not (occurs (Index 0) body) -> parensWhen 1 $ go 1 env ty <+> "->" <+> go 0 (prettyAnsi opts var : env) body
            qq@(Q q vis er _ _ _) -> parensWhen 1 $ kw q er <+> compressQ env q vis er qq
            VariantT row -> prettyVariant (prettyAnsi opts) (go 0 env) row
            RecordT row -> prettyRecord ":" (prettyAnsi opts) (go 0 env) row
            UniVar uni -> prettyAnsi opts uni
            AppPruning lhs pruning -> parensWhen 3 $ go 2 env lhs <> prettyPruning env pruning.getPruning
          where
            parensWhen minPrec
                | n >= minPrec = parens
                | otherwise = id

            kw Forall Erased = keyword "∀"
            kw Forall Retained = keyword "Π"
            kw Exists Erased = keyword "∃"
            kw Exists Retained = keyword "Σ"

            prettyConsNil = \case
                Con (L ConsName) (_ty :< (_, x') :< (_, xs') :< Nil) -> (("," <+> go 0 env x') <>) <$> prettyConsNil xs'
                Con (L NilName) (_ty :< Nil) -> Just ""
                _ -> Nothing

        compressLambda env term = case term of
            Lambda vis name body -> withVis vis (prettyAnsi opts name) <+> compressLambda (prettyAnsi opts name : env) body
            other -> specSym "->" <+> go 0 env other

        compressQ :: [Doc AnsiStyle] -> Quantifier -> Visibility -> Erasure -> CoreTerm -> Doc AnsiStyle
        compressQ env Forall Visible e (Q Forall Visible e' name ty body)
            | e == e' && not (occurs (Index 0) body) = "->" <+> go 1 env ty <+> "->" <+> go 0 (prettyAnsi opts name : env) body
        compressQ env q vis e term = case term of
            Q q' vis' e' name ty body
                | q == q' && vis == vis' && e == e' ->
                    prettyBinder env name ty <+> compressQ (prettyAnsi opts name : env) q vis e body
            other -> arrOrDot q vis <+> go 0 env other

        prettyBinder env name ty
            | endsInType ty = prettyAnsi opts name
            | otherwise = parens $ prettyAnsi opts name <+> specSym ":" <+> go 0 env ty
          where
            -- if the of a binder has the shape '... -> ... -> Type', it is probably used
            -- like a scoped type parameter, so its actual type is not that important and can be omitted in pretty-printing
            endsInType = \case
                TyCon (L TypeName) v | Vec.null v -> True
                Q _ _ _ _ _ body -> endsInType body
                _ -> False

        arrOrDot Forall Visible = specSym "->"
        arrOrDot Exists Visible = specSym "**"
        arrOrDot _ _ = specSym "."

        -- this mirrors the logic in 'evalAppPruning'
        prettyPruning = \cases
            (var : rest) (Just vis : pruning) -> prettyPruning rest pruning <+> withVis vis var
            (_ : rest) (Nothing : pruning) -> prettyPruning rest pruning
            _ _ -> ""

        patternVars = \case
            var@VarP{} -> [prettyAnsi opts var]
            ConstructorP _ args -> map (prettyAnsi opts . snd) $ reverse args
            VariantP _ arg -> [prettyAnsi opts arg]
            RecordP row -> map (prettyAnsi opts) . reverse $ toList row
            SigmaP _vis lhs rhs -> [prettyAnsi opts rhs, prettyAnsi opts lhs]
            LiteralP{} -> []

-- check whether a variable occurs in a term
occurs :: Index -> CoreTerm -> Bool
occurs var = getAny . getConst . go 0
  where
    go :: Int -> CoreTerm -> Const Any CoreTerm
    go n = \case
        Var ix -> Const $ Any $ ix.getIndex == var.getIndex + n
        l@Lambda{} -> coreTraversal (go $ succ n) l
        Q _ _ _ _ ty body -> go n ty *> go (succ n) body
        Let _ defn body -> go n defn *> go (succ n) body
        -- todo: case
        other -> coreTraversal (go n) other

coreTraversalWithLevel :: Applicative f => (Level -> CoreTerm -> f CoreTerm) -> Level -> CoreTerm -> f CoreTerm
coreTraversalWithLevel recur lvl = \case
    Con name args -> Con name <$> (traverse . traverse) (recur lvl) args
    TyCon name args -> TyCon name <$> (traverse . traverse) (recur lvl) args
    Variant name arg -> Variant name <$> recur lvl arg
    Lambda vis var body -> Lambda vis var <$> recur (succ lvl) body
    App vis lhs rhs -> App vis <$> recur lvl lhs <*> recur lvl rhs
    Case arg matches ->
        Case <$> recur lvl arg <*> traverse (\(pat, body) -> (pat,) <$> recur (Level $ lvl.getLevel + patternArity pat) body) matches
    Let name defn body -> Let name <$> recur lvl defn <*> recur (succ lvl) body
    Record row -> Record <$> traverse (recur lvl) row
    RecordT row -> RecordT <$> traverse (recur lvl) row
    VariantT row -> VariantT <$> traverse (recur lvl) row
    Sigma x y -> Sigma <$> recur lvl x <*> recur lvl y
    Q q v e name ty body -> Q q v e name <$> recur lvl ty <*> recur (succ lvl) body
    Var index -> pure $ Var index
    Name name -> pure $ Name name
    Literal lit -> pure $ Literal lit
    UniVar uni -> pure $ UniVar uni
    AppPruning lhs pruning -> pure $ AppPruning lhs pruning

coreTraversal :: Applicative f => (CoreTerm -> f CoreTerm) -> CoreTerm -> f CoreTerm
coreTraversal recur = coreTraversalWithLevel (const recur) (Level 0)

coreTraversalPureWithLevel :: (Level -> CoreTerm -> CoreTerm) -> Level -> CoreTerm -> CoreTerm
coreTraversalPureWithLevel recur lvl = runIdentity . coreTraversalWithLevel (\lvl -> pure . recur lvl) lvl

coreTraversalPure :: (CoreTerm -> CoreTerm) -> CoreTerm -> CoreTerm
coreTraversalPure recur = runIdentity . coreTraversal (pure . recur)

{- | lift a term through N lambda binders, adjusting local variable indices

I don't think it should traverse univars, since they are not supposed to reference any local variables
-}
lift :: Int -> CoreTerm -> CoreTerm
lift n = go (Level 0)
  where
    go depth = \case
        Var (Index index)
            | index >= depth.getLevel -> Var (Index $ index + n)
            | otherwise -> Var (Index index)
        other -> coreTraversalPureWithLevel go depth other

-- | How many new variables (including wildcards) does a pattern bind?
patternArity :: CorePattern -> Int
patternArity = \case
    VarP{} -> 1
    ConstructorP _ args -> length args
    VariantP{} -> 1
    RecordP row -> length row
    SigmaP{} -> 2
    LiteralP{} -> 0

-- invariant: the term must not contain unsolved univars in tail position
functionTypeArity :: CoreTerm -> Vector Visibility
functionTypeArity = fromList . go
  where
    go = \case
        Q Forall vis _ _ _ body -> vis : go body
        UniVar{} -> error "functionTypeArity called on a term with unsolved univars"
        _ -> []
