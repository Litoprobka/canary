{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE UndecidableInstances #-}
module Syntax.Pattern (Pattern (..), cast) where

import Relude
import Syntax.Row
import Prettyprinter (Pretty, pretty, Doc, braces, parens, sep, (<+>), punctuate, comma, dquotes, brackets)
import Syntax.Type (Type')
import Common (Loc, Pass, NameAt, bifix)

data Pattern (p :: Pass)
    = Var (NameAt p)
    | Annotation Loc (Pattern p) (Type' p)
    | Constructor Loc (NameAt p) [Pattern p]
    | Variant Loc OpenName (Pattern p) -- Loc is redundant
    | Record Loc (Row (Pattern p))
    | List Loc [Pattern p]
    | IntLiteral Loc Int
    | TextLiteral Loc Text
    | CharLiteral Loc Text

instance Pretty (NameAt pass) => Pretty (Pattern pass) where
    pretty = go 0 where
        go :: Int -> Pattern pass -> Doc ann
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


-- | a cast template for bifix. Doesn't handle annotations
baseCast :: NameAt p ~ NameAt q => (Pattern p -> Pattern q) -> Pattern p -> Pattern q
baseCast recur = \case
    Var name -> Var name
    Constructor loc name pats -> Constructor loc name (map recur pats)
    Variant loc name pat -> Variant loc name (recur pat)
    Record loc pats -> Record loc (fmap recur pats)
    List loc pats -> List loc (map recur pats)
    IntLiteral loc n -> IntLiteral loc n
    TextLiteral loc txt -> TextLiteral loc txt
    CharLiteral loc c -> CharLiteral loc c
    ann@Annotation{} -> recur ann

cast :: (NameAt p ~ NameAt q) => ((Pattern p -> Pattern q) -> Pattern p -> Pattern q) -> Pattern p -> Pattern q
cast terminals = bifix terminals baseCast