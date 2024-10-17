{-# LANGUAGE LambdaCase #-}
module Syntax.Expression (Expression (..), Binding (..), getLoc) where

import Relude

import Syntax.Pattern (Pattern)
import Syntax.Type (Type', Loc)
import Syntax.Row
import Prettyprinter (Pretty, pretty, (<+>), concatWith, parens, sep, nest, vsep, encloseSep, brackets, comma, punctuate, braces, dquotes)

data Binding n
    = ValueBinding Loc (Pattern n) (Expression n)
    | FunctionBinding Loc n (NonEmpty (Pattern n)) (Expression n)
    deriving (Show, Eq, Functor, Foldable, Traversable)

data Expression n
    = Lambda Loc (Pattern n) (Expression n)
    | Application Loc (Expression n) (Expression n)
    | Let Loc (Binding n) (Expression n)
    | Case Loc (Expression n) [(Pattern n, Expression n)]
    | -- | Haskell's \cases
      Match Loc [([Pattern n], Expression n)]
    | If Loc (Expression n) (Expression n) (Expression n)
    | -- | value : Type
      Annotation Loc (Expression n) (Type' n)
    | Name Loc n
    | -- | .field.otherField.thirdField
      RecordLens Loc (NonEmpty OpenName)
    | Constructor Loc n
    | -- | 'Constructor
      -- unlike the rest of the cases, variant tags and record fields
      -- don't need any kind of name resolution
      Variant Loc OpenName
    | Record Loc (Row (Expression n))
    | List Loc [Expression n]
    | IntLiteral Loc Int
    | TextLiteral Loc Text
    | CharLiteral Loc Text
    deriving (Show, Eq, Functor, Foldable, Traversable)

instance Pretty n => Pretty (Binding n) where
    pretty = \case
        ValueBinding _ pat body -> pretty pat <+> "=" <+> pretty body
        FunctionBinding _ name args body -> pretty name <+> concatWith (<+>) (pretty <$> args) <+> "=" <+> pretty body

instance Pretty n => Pretty (Expression n) where
    pretty = go (0 :: Int) where
        go n = \case
            Lambda _ arg body -> parensWhen 1 $ "λ" <> pretty arg <+> "->" <+> pretty body
            Application _ lhs rhs -> parensWhen 3 $ go 2 lhs <+> go 3 rhs
            Let _ binding body -> "let" <+> pretty binding <> ";" <+> pretty body
            Case _ arg matches -> nest 4 (vsep $ ("case" <+> pretty arg <+> "of" :) $ matches <&> \(pat, body) -> pretty pat <+> "->" <+> pretty body)
            Match _ matches -> nest 4 (vsep $ ("match" :) $ matches <&> \(pats, body) -> sep (parens . pretty <$> pats) <+> "->" <+> pretty body)
            If _ cond true false -> "if" <+> pretty cond <+> "then" <+> pretty true <+> "else" <+> pretty false
            Annotation _ expr ty -> parensWhen 1 $ pretty expr <+> ":" <+> pretty ty
            Name _ name -> pretty name
            RecordLens _ fields -> encloseSep "." "" "." $ toList $ pretty <$> fields
            Constructor _ name -> pretty name
            Variant _ name -> pretty name
            Record _ row -> braces . sep . punctuate comma . map recordField $ sortedRow row
            List _ xs -> brackets . sep . punctuate comma $ pretty <$> xs
            IntLiteral _ num -> pretty num
            TextLiteral _ txt -> dquotes $ pretty txt
            CharLiteral _ c -> "'" <> pretty c <> "'"
          where
            parensWhen minPrec
                | n >= minPrec = parens
                | otherwise = id
            recordField (name, body) = pretty name <+> "=" <+> pretty body

getLoc :: Expression n -> Loc
getLoc = \case
  Lambda loc _ _ -> loc
  Application loc _ _ -> loc
  Let loc _ _ -> loc
  Case loc _ _ -> loc
  Match loc _ -> loc
  If loc _ _ _ -> loc
  Annotation loc _ _ -> loc
  Name loc _ -> loc
  RecordLens loc _ -> loc
  Constructor loc _ -> loc
  Variant loc _ -> loc
  Record loc _ -> loc
  List loc _ -> loc
  IntLiteral loc _ -> loc
  TextLiteral loc _ -> loc
  CharLiteral loc _ -> loc
