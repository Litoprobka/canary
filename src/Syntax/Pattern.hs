{-# LANGUAGE LambdaCase #-}
module Syntax.Pattern (Pattern (..)) where

import Relude
import Syntax.Row
import Prettyprinter (Pretty, pretty, Doc, braces, parens, sep, (<+>), punctuate, comma, dquotes, brackets)
import Syntax.Type (Type')
import CheckerTypes (Loc)

data Pattern n
    = Var n
    | Annotation Loc (Pattern n) (Type' n)
    | Constructor Loc n [Pattern n]
    | Variant Loc OpenName (Pattern n) -- Loc is redundant
    | Record Loc (Row (Pattern n))
    | List Loc [Pattern n]
    | IntLiteral Loc Int
    | TextLiteral Loc Text
    | CharLiteral Loc Text
    deriving (Show, Eq, Functor, Foldable, Traversable)

-- note that the Traversable instance generally
-- doesn't do what you want

instance Pretty n => Pretty (Pattern n) where
    pretty = go 0 where
        go :: Int -> Pattern n -> Doc ann
        go n = \case
            Var name -> pretty name
            Annotation _ pat ty -> parens $ pretty pat <+> ":" <+> pretty ty
            Constructor _ name args -> parensWhen 1 $ sep (pretty name : map (go 1) args)
            Variant _ name body -> parensWhen 1 $ pretty name <+> go 1 body -- todo: special case for unit?
            Record _ row -> braces . sep . punctuate comma . map recordField $ sortedRow row
            List _ items -> brackets . sep $ map pretty items
            IntLiteral _ num -> pretty num
            TextLiteral _ txt -> dquotes $ pretty txt
            CharLiteral _ c -> "'" <> pretty c <> "'"
          where
            parensWhen minPrec
                | n >= minPrec = parens
                | otherwise = id
            
            recordField (name, pat) = pretty name <+> "=" <+> pretty pat