{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE ImplicitParams #-}

module Syntax.Core where

import Common (
    Index (..),
    Level (..),
    Literal,
    Name_ (ConsName, NilName, RecordName, TypeName, VariantName),
    PrettyAnsi (..),
    PrettyOptions (..),
    SimpleName_,
    UnAnnotate (..),
    UniVar,
    conColor,
    defaultPrettyOptions,
    incLevel,
    keyword,
    specSym,
    typeColor,
    pattern L,
 )
import Data.List ((!!))
import Data.Row (ExtRow (..), OpenName, Row, prettyRecord, prettyRow, prettyVariant)
import Data.Vector qualified as Vec
import LangPrelude
import Prettyprinter
import Prettyprinter.Render.Terminal (AnsiStyle)
import Syntax.Term (Erasure (..), Quantifier (..), Visibility (..), withVis)

data CorePattern
    = VarP SimpleName_
    | ConstructorP Name_ [(Visibility, SimpleName_)]
    | TypeP Name_ [(Visibility, SimpleName_)]
    | VariantP OpenName SimpleName_
    | RecordP (Vector (OpenName, SimpleName_))
    | SigmaP Visibility SimpleName_ SimpleName_
    | LiteralP Literal

instance PrettyAnsi CorePattern where
    prettyAnsi = \case
        VarP name -> prettyAnsi name
        ConstructorP name [] -> prettyCon name
        ConstructorP name args -> parens $ hsep (prettyCon name : map (\(vis, arg) -> withVis vis (prettyAnsi arg)) args)
        TypeP name [] -> prettyType name
        TypeP name args -> parens $ hsep (prettyType name : map (\(vis, arg) -> withVis vis (prettyAnsi arg)) args)
        VariantP name arg -> parens $ prettyCon name <+> prettyAnsi arg
        RecordP row -> braces . sep . punctuate comma . map recordField $ toList row
        SigmaP vis lhs rhs -> parens $ withVis vis (pretty lhs) <+> "**" <+> pretty rhs
        LiteralP lit -> prettyAnsi lit
      where
        prettyCon name = conColor $ prettyAnsi name
        prettyType name = typeColor $ prettyAnsi name
        recordField (L name, var) | name == var = prettyAnsi name
        recordField (name, pat) = prettyAnsi name <+> "=" <+> prettyAnsi pat

type CoreType = CoreTerm

data CoreTerm
    = Var Index
    | Name Name_
    | -- TyCon and Con are treated more or less the same way everywhere
      -- it could have made sense to merge them, except an optimised representation of Con
      -- would probably store a constructor tag (e.g. 0 for False, 1 for True) instead of a global name
      -- I guess, for now it's easier to keep the redundant TyCon
      TyCon Name_ (Vector (Visibility, CoreTerm))
    | Con Name_ (Vector (Visibility, CoreTerm))
    | Variant OpenName CoreTerm
    | Lambda Visibility SimpleName_ CoreTerm
    | App Visibility CoreTerm CoreTerm
    | Case CoreTerm [(CorePattern, CoreTerm)]
    | Let SimpleName_ CoreTerm CoreTerm
    | Literal Literal
    | Record (Row CoreTerm)
    | Sigma CoreTerm CoreTerm
    | Q Quantifier Visibility Erasure SimpleName_ CoreType CoreTerm
    | Row (ExtRow CoreType)
    | UniVar UniVar
    | AppPruning CoreTerm Pruning
    deriving (Pretty, Show) via (UnAnnotate CoreTerm)

newtype Pruning = Pruning {getPruning :: [Maybe Visibility]}
newtype ReversedPruning = ReversedPruning [Maybe Visibility]

reversedPruning :: Pruning -> ReversedPruning
reversedPruning = ReversedPruning . reverse . (.getPruning)

prettyEnvDef :: [Name_] -> CoreTerm -> Doc AnsiStyle
prettyEnvDef = let ?opts = defaultPrettyOptions in prettyEnv

-- | pretty-print a core term with a list of known bindings
prettyEnv :: (?opts :: PrettyOptions) => [Name_] -> CoreTerm -> Doc AnsiStyle
prettyEnv = go 0 . map prettyAnsi
  where
    go :: Int -> [Doc AnsiStyle] -> CoreTerm -> Doc AnsiStyle
    go n env term = case term of
        Var index
            | index.getIndex >= length env || index.getIndex < 0 -> "#" <> pretty index.getIndex
            | ?opts.printIds -> env !! index.getIndex <> "#" <> pretty (length env - index.getIndex)
            | otherwise -> env !! index.getIndex
        Name name -> prettyAnsi name
        TyCon name Nil -> typeColor $ prettyAnsi name
        TyCon VariantName ((_, Row row) :< Nil) -> prettyVariant prettyAnsi (go 0 env) row
        TyCon VariantName ((_, nonRow) :< Nil) -> brackets $ "|" <+> go 0 env nonRow
        TyCon RecordName ((_, Row row) :< Nil) -> prettyRecord ":" prettyAnsi (go 0 env) row
        TyCon RecordName ((_, nonRow) :< Nil) -> braces $ "|" <+> go 0 env nonRow
        TyCon name args -> parensWhen 3 $ hsep (typeColor (prettyAnsi name) : map (\(vis, t) -> withVis vis (go 3 env t)) (Vec.toList args))
        -- list sugar doesn't really make sense with explicit type applications, perhaps I should remove it
        -- another option is `[a, b, c] @ty`
        Con ConsName (_ty :< (_, x) :< (_, Con NilName Nil) :< Nil) -> brackets $ go 0 env x
        Con ConsName (_ty :< (_, x) :< (_, xs) :< Nil) | Just output <- prettyConsNil xs -> brackets $ go 0 env x <> output
        Con NilName (_ty :< Nil) -> "[]"
        Con name Nil -> conColor $ prettyAnsi name
        Con name args -> parensWhen 3 $ hsep (conColor (prettyAnsi name) : map (\(vis, t) -> withVis vis (go 3 env t)) (Vec.toList args))
        lambda@Lambda{} -> parensWhen 1 $ specSym "λ" <> compressLambda env lambda
        App vis lhs rhs -> parensWhen 3 $ go 2 env lhs <+> withVis vis (go 3 env rhs)
        Record row -> prettyRecord "=" prettyAnsi (go 0 env) (NoExtRow row)
        Sigma x y -> parensWhen 1 $ go 0 env x <+> specSym "**" <+> go 0 env y
        Variant name arg -> parensWhen 3 $ conColor (prettyAnsi name) <+> go 3 env arg
        Case arg [(RecordP ((field, _) :< Nil), Var (Index 0))] -> go 3 env arg <> "." <> prettyAnsi field
        Case arg matches ->
            nest
                4
                ( vsep $
                    (keyword "case" <+> go 0 env arg <+> keyword "of" :) $
                        matches <&> \(pat, body) -> prettyAnsi pat <+> specSym "->" <+> go 0 (patternVars pat <> env) body
                )
        Let name body expr -> keyword "let" <+> prettyAnsi name <+> specSym "=" <+> go 0 env body <> ";" <+> go 0 env expr
        Literal lit -> prettyAnsi lit
        -- checking for variable occurances here is not ideal (potentially O(n^2) in AST size),
        Q Forall Visible _e var ty body | not (occurs (Index 0) body) -> parensWhen 1 $ go 1 env ty <+> specSym "->" <+> go 0 (prettyAnsi var : env) body
        qq@(Q q vis er _ _ _) -> parensWhen 1 $ kw q er <+> compressQ env q vis er qq
        Row row -> prettyRow prettyAnsi (go 0 env) row
        UniVar uni -> prettyAnsi uni
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
            Con ConsName (_ty :< (_, x') :< (_, xs') :< Nil) -> (("," <+> go 0 env x') <>) <$> prettyConsNil xs'
            Con NilName (_ty :< Nil) -> Just ""
            _ -> Nothing

    compressLambda env term = case term of
        Lambda vis name body -> withVis vis (prettyAnsi name) <+> compressLambda (prettyAnsi name : env) body
        other -> specSym "->" <+> go 0 env other

    compressQ :: [Doc AnsiStyle] -> Quantifier -> Visibility -> Erasure -> CoreTerm -> Doc AnsiStyle
    compressQ env Forall Visible e (Q Forall Visible e' name ty body)
        | e == e' && not (occurs (Index 0) body) = specSym "->" <+> go 1 env ty <+> specSym "->" <+> go 0 (prettyAnsi name : env) body
    compressQ env q vis e term = case term of
        Q q' vis' e' name ty body
            | q == q' && vis == vis' && e == e' ->
                prettyBinder env name ty <+> compressQ (prettyAnsi name : env) q vis e body
        other -> arrOrDot q vis <+> go 0 env other

    prettyBinder env name ty
        | endsInType ty = prettyAnsi name
        | otherwise = parens $ prettyAnsi name <+> specSym ":" <+> go 0 env ty
      where
        -- if the of a binder has the shape '... -> ... -> Type', it is probably used
        -- like a scoped type parameter, so its actual type is not that important and can be omitted in pretty-printing
        endsInType = \case
            TyCon TypeName v | Vec.null v -> True
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
        var@VarP{} -> [prettyAnsi var]
        ConstructorP _ args -> map (prettyAnsi . snd) $ reverse args
        TypeP _ args -> map (prettyAnsi . snd) $ reverse args
        VariantP _ arg -> [prettyAnsi arg]
        RecordP row -> map (prettyAnsi . snd) . reverse $ toList row
        SigmaP _vis lhs rhs -> [prettyAnsi rhs, prettyAnsi lhs]
        LiteralP{} -> []

instance PrettyAnsi CoreTerm where
    prettyAnsi = prettyEnv []

-- check whether a variable occurs in a term
occurs :: Index -> CoreTerm -> Bool
occurs var = getAny . getConst . go (Level 0)
  where
    go :: Level -> CoreTerm -> Const Any CoreTerm
    go depth = \case
        Var ix -> Const $ Any $ ix.getIndex == var.getIndex + depth.getLevel
        other -> coreTraversalWithLevel go depth other

coreTraversalWithLevel :: Applicative f => (Level -> CoreTerm -> f CoreTerm) -> Level -> CoreTerm -> f CoreTerm
coreTraversalWithLevel recur lvl = \case
    Con name args -> Con name <$> (traverse . traverse) (recur lvl) args
    TyCon name args -> TyCon name <$> (traverse . traverse) (recur lvl) args
    Variant name arg -> Variant name <$> recur lvl arg
    Lambda vis var body -> Lambda vis var <$> recur (succ lvl) body
    App vis lhs rhs -> App vis <$> recur lvl lhs <*> recur lvl rhs
    Case arg matches ->
        Case <$> recur lvl arg <*> traverse (\(pat, body) -> (pat,) <$> recur (lvl `incLevel` patternArity pat) body) matches
    Let name defn body -> Let name <$> recur lvl defn <*> recur (succ lvl) body
    Record row -> Record <$> traverse (recur lvl) row
    Row row -> Row <$> traverse (recur lvl) row
    Sigma x y -> Sigma <$> recur lvl x <*> recur lvl y
    Q q v e name ty body -> Q q v e name <$> recur lvl ty <*> recur (succ lvl) body
    Var index -> pure $ Var index
    Name name -> pure $ Name name
    Literal lit -> pure $ Literal lit
    UniVar uni -> pure $ UniVar uni
    AppPruning lhs pruning -> AppPruning <$> recur lvl lhs <*> pure pruning

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
lift n = liftAt n (Level 0)

liftAt :: Int -> Level -> CoreTerm -> CoreTerm
liftAt 0 = \_ term -> term
liftAt n = go
  where
    go depth = \case
        Var (Index index)
            | index >= depth.getLevel -> Var (Index $ index + n)
            | otherwise -> Var (Index index)
        -- the length of the pruning must match the current level, so if we change the level, we must also
        -- add new Nothing masks in the right place
        AppPruning lhs pruning ->
            let (newer, older) = splitAt depth.getLevel pruning.getPruning
             in AppPruning (go depth lhs) (Pruning $ newer <> replicate n Nothing <> older)
        other -> coreTraversalPureWithLevel go depth other

-- | How many new variables (including wildcards) does a pattern bind?
patternArity :: CorePattern -> Int
patternArity = \case
    VarP{} -> 1
    ConstructorP _ args -> length args
    TypeP _ args -> length args
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
