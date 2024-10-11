{-# LANGUAGE LambdaCase #-}
module Syntax.Pattern (Pattern (..)) where

import Relude
import Syntax.Row
import Prettyprinter (Pretty, pretty, Doc, braces, parens, sep, (<+>), punctuate, comma, dquotes, brackets)
import Syntax.Type (Type')

data Pattern n
    = Var n
    | Annotation (Pattern n) (Type' n)
    | Constructor n [Pattern n]
    | Variant OpenName (Pattern n)
    | Record (Row (Pattern n))
    | List [Pattern n]
    | IntLiteral Int
    | TextLiteral Text
    | CharLiteral Text
    deriving (Show, Eq, Functor, Foldable, Traversable)

-- note that the Traversable instance generally
-- doesn't do what you want

instance Pretty n => Pretty (Pattern n) where
    pretty = go 0 where
        go :: Int -> Pattern n -> Doc ann
        go n = \case
            Var name -> pretty name
            Annotation pat ty -> parens $ pretty pat <+> ":" <+> pretty ty
            Constructor name args -> parensWhen 1 $ sep (pretty name : map (go 1) args)
            Variant name body -> parensWhen 1 $ pretty name <+> go 1 body -- todo: special case for unit?
            Record row -> braces . sep . punctuate comma . map recordField $ sortedRow row
            List items -> brackets . sep $ map pretty items
            IntLiteral num -> pretty num
            TextLiteral txt -> dquotes $ pretty txt
            CharLiteral c -> "'" <> pretty c <> "'"
          where
            parensWhen minPrec
                | n >= minPrec = parens
                | otherwise = id
            
            recordField (name, pat) = pretty name <+> "=" <+> pretty pat