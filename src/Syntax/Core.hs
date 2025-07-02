module Syntax.Core where

import Common (
    Index (..),
    Level (..),
    Literal,
    Name,
    Name_ (ConsName, NilName, TypeName),
    PrettyAnsi (..),
    SimpleName_,
    UniVar,
    conColor,
    keyword,
    specSym,
    pattern L,
 )
import LangPrelude
import Prettyprinter
import Prettyprinter.Render.Terminal (AnsiStyle)
import Syntax.Row (ExtRow (..), OpenName, Row, prettyRecord, prettyVariant, sortedRow)
import Syntax.Term (Erasure (..), Quantifier (..), Visibility (..))

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
    | Lambda SimpleName_ CoreTerm
    | App CoreTerm CoreTerm
    | Case CoreTerm [(CorePattern, CoreTerm)]
    | Let SimpleName_ CoreTerm CoreTerm
    | Literal Literal
    | Record (Row CoreTerm)
    | Sigma CoreTerm CoreTerm
    | Variant OpenName
    | -- types
      Function CoreTerm CoreTerm
    | Q Quantifier Visibility Erasure SimpleName_ CoreType CoreTerm
    | VariantT (ExtRow CoreType)
    | RecordT (ExtRow CoreType)
    | UniVar UniVar
    | InsertedUniVar UniVar [BoundDefined]

data BoundDefined = Bound | Defined

instance PrettyAnsi CoreTerm where
    prettyAnsi opts = go 0
      where
        go :: Int -> CoreTerm -> Doc AnsiStyle
        go n term = case term of
            Var index -> "#" <> pretty index.getIndex
            Name name -> prettyAnsi opts name
            TyCon name -> prettyAnsi opts name
            Con (L ConsName) [x, Con (L NilName) []] -> brackets $ go 0 x
            Con (L ConsName) [x, xs] | Just output <- prettyConsNil xs -> brackets $ go 0 x <> output
            Con (L NilName) [] -> "[]"
            Con name [] -> prettyAnsi opts name
            Con name args -> parensWhen 3 $ hsep (prettyAnsi opts name : map (go 3) args)
            Lambda name body -> parensWhen 1 $ specSym "λ" <> prettyAnsi opts name <+> compressLambda body
            App lhs rhs -> parensWhen 3 $ go 2 lhs <+> go 3 rhs
            Record row -> prettyRecord "=" (prettyAnsi opts) (go 0) (NoExtRow row)
            Sigma x y -> parensWhen 1 $ go 0 x <+> specSym "**" <+> go 0 y
            Variant name -> prettyAnsi opts name
            Case arg matches ->
                nest
                    4
                    ( vsep $
                        (keyword "case" <+> go 0 arg <+> keyword "of" :) $
                            matches <&> \(pat, body) -> prettyAnsi opts pat <+> specSym "->" <+> go 0 body
                    )
            Let name body expr -> keyword "let" <+> prettyAnsi opts name <+> specSym "=" <+> go 0 body <> ";" <+> go 0 expr
            Literal lit -> prettyAnsi opts lit
            Function from to -> parensWhen 2 $ go 2 from <+> specSym "->" <+> go 0 to
            Q q vis er name ty body -> parensWhen 1 $ kw q er <+> prettyBinder name ty <+> compressQ q vis er body
            VariantT row -> prettyVariant (prettyAnsi opts) (go 0) row
            RecordT row -> prettyRecord ":" (prettyAnsi opts) (go 0) row
            UniVar uni -> prettyAnsi opts uni
            InsertedUniVar uni _ -> "<" <> prettyAnsi opts uni <> ">"
          where
            parensWhen minPrec
                | n >= minPrec = parens
                | otherwise = id

            kw Forall Erased = keyword "∀"
            kw Forall Retained = keyword "Π"
            kw Exists Erased = keyword "∃"
            kw Exists Retained = keyword "Σ"

        compressLambda term = case term of
            Lambda name body -> prettyAnsi opts name <+> compressLambda body
            other -> specSym "->" <+> prettyAnsi opts other
        compressQ q vis e term = case term of
            Q q' vis' e' name ty body
                | q == q' && vis == vis' && e == e' ->
                    prettyBinder name ty <+> compressQ q vis e body
            other -> arrOrDot q vis <+> prettyAnsi opts other

        prettyBinder name (TyCon (L TypeName)) = prettyAnsi opts name
        prettyBinder name ty = parens $ prettyAnsi opts name <+> specSym ":" <+> go 0 ty

        arrOrDot Forall Visible = specSym "->"
        arrOrDot Exists Visible = specSym "**"
        arrOrDot _ _ = specSym "."

        prettyConsNil = \case
            Con (L ConsName) [x', xs'] -> (("," <+> go 0 x') <>) <$> prettyConsNil xs'
            Con (L NilName) [] -> Just ""
            _ -> Nothing

coreTraversal :: Applicative f => (CoreTerm -> f CoreTerm) -> CoreTerm -> f CoreTerm
coreTraversal recur = \case
    Con name args -> Con name <$> traverse recur args
    Lambda var body -> Lambda var <$> recur body
    App lhs rhs -> App <$> recur lhs <*> recur rhs
    Case arg matches -> Case <$> recur arg <*> (traverse . traverse) recur matches
    Let name defn body -> Let name <$> recur defn <*> recur body
    Record row -> Record <$> traverse recur row
    RecordT row -> RecordT <$> traverse recur row
    VariantT row -> VariantT <$> traverse recur row
    Sigma x y -> Sigma <$> recur x <*> recur y
    Function from to -> Function <$> recur from <*> recur to
    Q q v e name ty body -> Q q v e name <$> recur ty <*> recur body
    Var index -> pure $ Var index
    Name name -> pure $ Name name
    TyCon name -> pure $ TyCon name
    Literal lit -> pure $ Literal lit
    Variant name -> pure $ Variant name
    UniVar uni -> pure $ UniVar uni
    InsertedUniVar uni bds -> pure $ InsertedUniVar uni bds

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
        Lambda var body -> Lambda var $ go (succ depth) body
        other -> coreTraversalPure (go depth) other
