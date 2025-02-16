module Syntax.Core where

import Common (Literal_, Name)
import LangPrelude
import Prettyprinter
import Syntax.Row (ExtRow (..), OpenName, Row, extension, sortedRow)

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

data CoreTerm
    = Name Name
    | Lambda Name CoreTerm
    | App CoreTerm CoreTerm
    | Case CoreTerm [(CorePattern, CoreTerm)]
    | Let Name CoreTerm CoreTerm
    | Literal Literal_
    | Record (Row CoreTerm)
    | Variant OpenName
    | -- types
      Function CoreTerm CoreTerm
    | Forall Name CoreTerm
    | Exists Name CoreTerm
    | VariantT (ExtRow CoreTerm)
    | RecordT (ExtRow CoreTerm)

instance Pretty CoreTerm where
    pretty = go (0 :: Int)
      where
        go n = \case
            Name name -> pretty name
            Lambda name body -> parensWhen 1 $ "λ" <> pretty name <+> compressLambda body
            App lhs rhs -> parensWhen 3 $ go 2 lhs <+> go 3 rhs
            Record row -> braces . sep . punctuate comma . map recordField $ sortedRow row
            Variant name -> pretty name
            -- RecordLens lens -> foldMap (("." <>) . pretty) lens
            Case arg matches -> nest 4 (vsep $ ("case" <+> pretty arg <+> "of" :) $ matches <&> \(pat, body) -> pretty pat <+> "->" <+> pretty body)
            Let name body expr -> "let" <+> pretty name <+> "=" <+> pretty body <> ";" <+> pretty expr
            Literal lit -> pretty lit
            Function from to -> parensWhen 2 $ go 2 from <+> "->" <+> pretty to
            Forall var body -> parensWhen 1 $ "∀" <> pretty var <> "." <+> compressForall body
            Exists var body -> parensWhen 1 $ "∃" <> pretty var <> "." <+> compressExists body
            VariantT row -> brackets . withExt row . sep . punctuate comma . map variantItem $ sortedRow row.row
            RecordT row -> braces . withExt row . sep . punctuate comma . map recordTyField $ sortedRow row.row
          where
            parensWhen minPrec
                | n >= minPrec = parens
                | otherwise = id
            recordField (name, body) = pretty name <+> "=" <+> pretty body
            withExt row = maybe id (\r doc -> doc <+> "|" <+> pretty r) (extension row)

            variantItem (name, ty) = pretty name <+> pretty ty
            recordTyField (name, ty) = pretty name <+> ":" <+> pretty ty
        compressLambda = \case
            Lambda name body -> pretty name <+> compressLambda body
            other -> "->" <+> pretty other
        compressForall = \case
            Forall name body -> " " <> pretty name <> compressForall body
            other -> "." <+> pretty other
        compressExists = \case
            Exists name body -> " " <> pretty name <> compressExists body
            other -> "." <+> pretty other
