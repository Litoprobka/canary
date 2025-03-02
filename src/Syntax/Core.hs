module Syntax.Core where

import Common (Literal, Literal_, Loc, Name, Skolem, UniVar)
import LangPrelude
import Prettyprinter
import Syntax.Row (ExtRow (..), OpenName, Row, extension, sortedRow)
import Syntax.Term (Quantifier (..), Visibility (..), Erased (..))

data CorePattern
    = VarP Name
    | WildcardP Text
    | ConstructorP Name [Name]
    | VariantP OpenName Name
    | LiteralP Literal_

instance Pretty CorePattern where
    pretty = \case
        VarP name -> pretty name
        WildcardP txt -> "_" <> pretty txt
        ConstructorP name args -> parens $ hsep (pretty name : map pretty args)
        VariantP name arg -> parens $ pretty name <+> pretty arg
        LiteralP lit -> pretty lit

type CoreType = CoreTerm

data CoreTerm
    = Name Name
    | TyCon Name
    | Con Name [CoreTerm] -- a fully-applied constructor. may only be produced by `quote`
    | Lambda Name CoreTerm
    | App CoreTerm CoreTerm
    | Case CoreTerm [(CorePattern, CoreTerm)]
    | Let Name CoreTerm CoreTerm
    | Literal Literal
    | Record (Row CoreTerm)
    | Variant OpenName
    | -- types
      Function Loc CoreTerm CoreTerm
    | Q Loc Quantifier Visibility Erased Name CoreTerm CoreTerm
    | VariantT Loc (ExtRow CoreTerm)
    | RecordT Loc (ExtRow CoreTerm)
    | -- typechecking metavars
      -- it might be a good idea to split terms-for-typecheck
      -- from normal desugared terms
      -- actually, it should be cleaner to implement standalone prettyprinting for Value
      -- instead of using `quote` and keeping CoreTerm and Value in sync. This way will do for now, though
      UniVar Loc UniVar
    | Skolem Skolem

instance Pretty CoreTerm where
    pretty = go (0 :: Int)
      where
        go n = \case
            Name name -> pretty name
            TyCon name -> pretty name
            Con name [] -> pretty name
            Con name args -> parensWhen 3 $ hsep (pretty name : map (go 3) args)
            Lambda name body -> parensWhen 1 $ "λ" <> pretty name <+> compressLambda body
            App lhs rhs -> parensWhen 3 $ go 2 lhs <+> go 3 rhs
            Record row -> braces . sep . punctuate comma . map recordField $ sortedRow row
            Variant name -> pretty name
            -- RecordLens lens -> foldMap (("." <>) . pretty) lens
            Case arg matches -> nest 4 (vsep $ ("case" <+> pretty arg <+> "of" :) $ matches <&> \(pat, body) -> pretty pat <+> "->" <+> pretty body)
            Let name body expr -> "let" <+> pretty name <+> "=" <+> pretty body <> ";" <+> pretty expr
            Literal lit -> pretty lit
            Function _ from to -> parensWhen 2 $ go 2 from <+> "->" <+> pretty to
            Q _ q vis er name ty body -> parensWhen 1 $ kw q er <+> parens (pretty name <+> ":" <+> pretty ty) <+> compressQ q vis er body
            VariantT _ row -> brackets . withExt row . sep . punctuate comma . map variantItem $ sortedRow row.row
            RecordT _ row -> braces . withExt row . sep . punctuate comma . map recordTyField $ sortedRow row.row
            Skolem skolem -> pretty skolem
            UniVar _ uni -> pretty uni
          where
            parensWhen minPrec
                | n >= minPrec = parens
                | otherwise = id
            recordField (name, body) = pretty name <+> "=" <+> pretty body
            withExt row = maybe id (\r doc -> doc <+> "|" <+> pretty r) (extension row)

            kw Forall Erased = "∀"
            kw Forall Retained = "Π"
            kw Exists Erased = "∃"
            kw Exists Retained = "Σ"

            variantItem (name, ty) = pretty name <+> pretty ty
            recordTyField (name, ty) = pretty name <+> ":" <+> pretty ty
        compressLambda = \case
            Lambda name body -> pretty name <+> compressLambda body
            other -> "->" <+> pretty other
        compressQ q vis e = \case
            Q _ q' vis' e' name ty body | q == q' && vis == vis' && e == e' ->
              parens (pretty name <+> ":" <+> pretty ty) <+> compressQ q vis e body
            other -> arrOrDot q vis <+> pretty other

        arrOrDot Forall Visible = "->"
        arrOrDot Exists Visible = "**"
        arrOrDot _ _ = "."
