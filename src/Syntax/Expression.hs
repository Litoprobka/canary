{-# LANGUAGE LambdaCase #-}
module Syntax.Expression (Expression (..), Binding (..)) where

import Relude

import Syntax.Pattern (Pattern)
import Syntax.Type (Type')
import Syntax.Row
import Prettyprinter (Pretty, pretty, (<+>), concatWith, parens, sep, nest, vsep, encloseSep, brackets, comma, punctuate, braces, dquotes, line)

data Binding n
    = ValueBinding (Pattern n) (Expression n)
    | FunctionBinding n (NonEmpty (Pattern n)) (Expression n)
    deriving (Show, Eq, Functor, Foldable, Traversable)

data Expression n
    = Lambda (Pattern n) (Expression n)
    | Application (Expression n) (Expression n)
    | Let (Binding n) (Expression n)
    | Case (Expression n) [(Pattern n, Expression n)]
    | -- | Haskell's \cases
      Match [([Pattern n], Expression n)]
    | If (Expression n) (Expression n) (Expression n)
    | -- | value : Type
      Annotation (Expression n) (Type' n)
    | Name n
    | -- | .field.otherField.thirdField
      RecordLens (NonEmpty OpenName)
    | Constructor n
    | -- | 'Constructor
      -- unlike the rest of the cases, variant tags and record fields
      -- don't need any kind of name resolution
      Variant OpenName
    | Record (Row (Expression n))
    | List [Expression n]
    | IntLiteral Int
    | TextLiteral Text
    | CharLiteral Text
    deriving (Show, Eq, Functor, Foldable, Traversable)

instance Pretty n => Pretty (Binding n) where
    pretty = \case
        ValueBinding pat body -> pretty pat <+> "=" <+> pretty body
        FunctionBinding name args body -> pretty name <+> concatWith (<+>) (pretty <$> args) <+> "=" <+> pretty body

instance Pretty n => Pretty (Expression n) where
    pretty = go (0 :: Int) where
        go n = \case
            Lambda arg body -> parensWhen 1 $ "λ" <> pretty arg <+> "->" <+> pretty body
            Application lhs rhs -> parensWhen 3 $ go 2 lhs <+> go 3 rhs
            Let binding body -> "let" <+> pretty binding <> ";" <+> pretty body
            Case arg matches -> nest 4 (vsep $ ("case" <+> pretty arg <+> "of" :) $ matches <&> \(pat, body) -> pretty pat <+> "->" <+> pretty body)
            Match matches -> nest 4 (vsep $ ("match" :) $ matches <&> \(pats, body) -> sep (parens . pretty <$> pats) <+> "->" <+> pretty body)
            If cond true false -> "if" <+> pretty cond <+> "then" <+> pretty true <+> "else" <+> pretty false
            Annotation expr ty -> parensWhen 1 $ pretty expr <+> ":" <+> pretty ty
            Name name -> pretty name
            RecordLens fields -> encloseSep "." "" "." $ toList $ pretty <$> fields
            Constructor name -> pretty name
            Variant name -> pretty name
            Record row -> braces . sep . punctuate comma . map recordField $ sortedRow row
            List xs -> brackets . sep . punctuate comma $ pretty <$> xs
            IntLiteral num -> pretty num
            TextLiteral txt -> dquotes $ pretty txt
            CharLiteral c -> "'" <> pretty c <> "'"
          where
            parensWhen minPrec
                | n >= minPrec = parens
                | otherwise = id
            recordField (name, body) = pretty name <+> "=" <+> pretty body
