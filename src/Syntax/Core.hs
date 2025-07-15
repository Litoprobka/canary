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
    pattern L,
 )
import Data.List ((!!))
import LangPrelude
import Prettyprinter
import Prettyprinter.Render.Terminal (AnsiStyle)
import Syntax.Row (ExtRow (..), OpenName, Row, prettyRecord, prettyVariant, sortedRow)
import Syntax.Term (Erasure (..), Quantifier (..), Visibility (..), withVis)

data CorePattern
    = VarP SimpleName_
    | WildcardP Text
    | ConstructorP Name [SimpleName_]
    | VariantP OpenName SimpleName_
    | RecordP (Row SimpleName_)
    | SigmaP SimpleName_ SimpleName_
    | LiteralP Literal

instance PrettyAnsi CorePattern where
    prettyAnsi opts = \case
        VarP name -> prettyAnsi opts name
        WildcardP txt -> "_" <> pretty txt
        ConstructorP name [] -> prettyCon name
        ConstructorP name args -> parens $ hsep (prettyCon name : map (prettyAnsi opts) args)
        VariantP name arg -> parens $ prettyCon name <+> prettyAnsi opts arg
        RecordP row -> braces . sep . punctuate comma . map recordField $ sortedRow row
        SigmaP lhs rhs -> parens $ pretty lhs <+> "**" <+> pretty rhs
        LiteralP lit -> prettyAnsi opts lit
      where
        prettyCon name = conColor $ prettyAnsi opts name
        recordField (name, pat) = prettyAnsi opts name <+> "=" <+> prettyAnsi opts pat

type CoreType = CoreTerm

data CoreTerm
    = Var Index
    | Name Name
    | TyCon Name
    | Con Name [CoreTerm] -- a fully-applied constructor. may only be produced by `quote`
    | Lambda Visibility SimpleName_ CoreTerm
    | App Visibility CoreTerm CoreTerm
    | Case CoreTerm [(CorePattern, CoreTerm)]
    | Let SimpleName_ CoreTerm CoreTerm
    | Literal Literal
    | Record (Row CoreTerm)
    | Sigma CoreTerm CoreTerm
    | Variant OpenName
    | -- types
      Q Quantifier Visibility Erasure SimpleName_ CoreType CoreTerm
    | VariantT (ExtRow CoreType)
    | RecordT (ExtRow CoreType)
    | UniVar UniVar
    | AppPruning CoreTerm Pruning
    deriving (Pretty) via (UnAnnotate CoreTerm)

newtype Pruning = Pruning {getPruning :: [Maybe Visibility]}
newtype ReversedPruning = ReversedPruning [Maybe Visibility]

instance PrettyAnsi CoreTerm where
    prettyAnsi opts = go 0 []
      where
        go :: Int -> [Doc AnsiStyle] -> CoreTerm -> Doc AnsiStyle
        go n env term = case term of
            Var index
                | index.getIndex >= length env || index.getIndex < 0 -> "#" <> pretty index.getIndex
                | otherwise -> env !! index.getIndex
            Name name -> prettyAnsi opts name
            TyCon name -> prettyAnsi opts name
            Con (L ConsName) [x, Con (L NilName) []] -> brackets $ go 0 env x
            Con (L ConsName) [x, xs] | Just output <- prettyConsNil xs -> brackets $ go 0 env x <> output
            Con (L NilName) [] -> "[]"
            Con name [] -> prettyAnsi opts name
            Con name args -> parensWhen 3 $ hsep (prettyAnsi opts name : map (go 3 env) args)
            lambda@Lambda{} -> parensWhen 1 $ specSym "λ" <> compressLambda env lambda
            App vis lhs rhs -> parensWhen 3 $ go 2 env lhs <+> withVis vis (go 3 env rhs)
            Record row -> prettyRecord "=" (prettyAnsi opts) (go 0 env) (NoExtRow row)
            Sigma x y -> parensWhen 1 $ go 0 env x <+> specSym "**" <+> go 0 env y
            Variant name -> prettyAnsi opts name
            Case arg matches ->
                nest
                    4
                    ( vsep $
                        (keyword "case" <+> go 0 env arg <+> keyword "of" :) $
                            matches <&> \(pat, body) -> prettyAnsi opts pat <+> specSym "->" <+> go 0 env body
                    )
            Let name body expr -> keyword "let" <+> prettyAnsi opts name <+> specSym "=" <+> go 0 env body <> ";" <+> go 0 env expr
            Literal lit -> prettyAnsi opts lit
            -- checking for variable occurances here is not ideal (potentially O(n^2) in AST size),
            Q Forall Visible _e var ty body | not (occurs (Index 0) body) -> parensWhen 1 $ go 1 env ty <+> "->" <+> go 0 (prettyAnsi opts var : env) body
            qq@(Q q vis er _ _ _) -> parensWhen 1 $ kw q er <+> compressQ env q vis er qq
            VariantT row -> prettyVariant (prettyAnsi opts) (go 0 env) row
            RecordT row -> prettyRecord ":" (prettyAnsi opts) (go 0 env) row
            UniVar uni -> prettyAnsi opts uni
            AppPruning{} -> "<pruning, idk>"
          where
            parensWhen minPrec
                | n >= minPrec = parens
                | otherwise = id

            kw Forall Erased = keyword "∀"
            kw Forall Retained = keyword "Π"
            kw Exists Erased = keyword "∃"
            kw Exists Retained = keyword "Σ"

            prettyConsNil = \case
                Con (L ConsName) [x', xs'] -> (("," <+> go 0 env x') <>) <$> prettyConsNil xs'
                Con (L NilName) [] -> Just ""
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

        prettyBinder _ name (TyCon (L TypeName)) = prettyAnsi opts name
        prettyBinder env name ty = parens $ prettyAnsi opts name <+> specSym ":" <+> go 0 env ty

        arrOrDot Forall Visible = specSym "->"
        arrOrDot Exists Visible = specSym "**"
        arrOrDot _ _ = specSym "."

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

coreTraversal :: Applicative f => (CoreTerm -> f CoreTerm) -> CoreTerm -> f CoreTerm
coreTraversal recur = \case
    Con name args -> Con name <$> traverse recur args
    Lambda vis var body -> Lambda vis var <$> recur body
    App vis lhs rhs -> App vis <$> recur lhs <*> recur rhs
    Case arg matches -> Case <$> recur arg <*> (traverse . traverse) recur matches
    Let name defn body -> Let name <$> recur defn <*> recur body
    Record row -> Record <$> traverse recur row
    RecordT row -> RecordT <$> traverse recur row
    VariantT row -> VariantT <$> traverse recur row
    Sigma x y -> Sigma <$> recur x <*> recur y
    Q q v e name ty body -> Q q v e name <$> recur ty <*> recur body
    Var index -> pure $ Var index
    Name name -> pure $ Name name
    TyCon name -> pure $ TyCon name
    Literal lit -> pure $ Literal lit
    Variant name -> pure $ Variant name
    UniVar uni -> pure $ UniVar uni
    AppPruning lhs pruning -> pure $ AppPruning lhs pruning

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
        Lambda vis var body -> Lambda vis var $ go (succ depth) body
        other -> coreTraversalPure (go depth) other

-- | How many new variables does a pattern bind?
patternArity :: CorePattern -> Int
patternArity = go
  where
    go = \case
        VarP{} -> 1
        WildcardP{} -> 1 -- should it also be 0?
        ConstructorP _ args -> length args
        VariantP{} -> 1
        RecordP row -> length row
        SigmaP{} -> 2
        LiteralP{} -> 0
