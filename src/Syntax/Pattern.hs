{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE UndecidableInstances #-}
module Syntax.Pattern (Pattern (..), cast) where

import Relude
import Syntax.Row
import Prettyprinter (Pretty, pretty, Doc, braces, parens, sep, (<+>), punctuate, comma, dquotes, brackets)
import Syntax.Type (Type')
import Common (Loc, Pass, NameAt, bifix, HasLoc, getLoc, zipLocOf)

data Pattern (p :: Pass)
    = Var (NameAt p)
    | Annotation (Pattern p) (Type' p)
    | Constructor (NameAt p) [Pattern p]
    | Variant OpenName (Pattern p)
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
            Annotation pat ty -> parens $ pretty pat <+> ":" <+> pretty ty
            Constructor name args -> parensWhen 1 $ sep (pretty name : map (go 1) args)
            Variant name body -> parensWhen 1 $ pretty name <+> go 1 body -- todo: special case for unit?
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

instance HasLoc (NameAt p) => HasLoc (Pattern p) where
    getLoc = \case
        Var name -> getLoc name
        Annotation pat ty -> zipLocOf pat ty
        Constructor name args -> case listToMaybe $ reverse args of
            Nothing -> getLoc name
            Just lastArg -> zipLocOf name lastArg
        Variant name arg -> zipLocOf name arg
        
        Record loc _ -> loc
        List loc _ -> loc
        IntLiteral loc _ -> loc
        TextLiteral loc _ -> loc
        CharLiteral loc _ -> loc

-- | a cast template for bifix. Doesn't handle annotations
baseCast :: NameAt p ~ NameAt q => (Pattern p -> Pattern q) -> Pattern p -> Pattern q
baseCast recur = \case
    Var name -> Var name
    Constructor name pats -> Constructor name (map recur pats)
    Variant name pat -> Variant name (recur pat)
    Record loc pats -> Record loc (fmap recur pats)
    List loc pats -> List loc (map recur pats)
    IntLiteral loc n -> IntLiteral loc n
    TextLiteral loc txt -> TextLiteral loc txt
    CharLiteral loc c -> CharLiteral loc c
    ann@Annotation{} -> recur ann

cast :: (NameAt p ~ NameAt q) => ((Pattern p -> Pattern q) -> Pattern p -> Pattern q) -> Pattern p -> Pattern q
cast terminals = bifix terminals baseCast