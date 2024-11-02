{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE UndecidableInstances #-}
module Syntax.Pattern (Pattern (..), cast) where

import Relude
import Syntax.Row
import Prettyprinter (Pretty, pretty, Doc, braces, parens, sep, (<+>), punctuate, comma, brackets)
import Syntax.Type (Type')
import Common (Loc, Pass, NameAt, bifix, HasLoc, getLoc, zipLocOf, Literal)

data Pattern (p :: Pass)
    = Var (NameAt p)
    | Wildcard Loc Text
    | Annotation (Pattern p) (Type' p)
    | Constructor (NameAt p) [Pattern p]
    | Variant OpenName (Pattern p)
    | Record Loc (Row (Pattern p))
    | List Loc [Pattern p]
    | Literal Literal

instance Pretty (NameAt pass) => Pretty (Pattern pass) where
    pretty = go 0 where
        go :: Int -> Pattern pass -> Doc ann
        go n = \case
            Var name -> pretty name
            Wildcard _ txt -> pretty txt
            Annotation pat ty -> parens $ pretty pat <+> ":" <+> pretty ty
            Constructor name args -> parensWhen 1 $ sep (pretty name : map (go 1) args)
            Variant name body -> parensWhen 1 $ pretty name <+> go 1 body -- todo: special case for unit?
            Record _ row -> braces . sep . punctuate comma . map recordField $ sortedRow row
            List _ items -> brackets . sep $ map pretty items
            Literal lit -> pretty lit
          where
            parensWhen minPrec
                | n >= minPrec = parens
                | otherwise = id
            
            recordField (name, pat) = pretty name <+> "=" <+> pretty pat

instance HasLoc (NameAt p) => HasLoc (Pattern p) where
    getLoc = \case
        Var name -> getLoc name
        Wildcard loc _ -> loc
        Annotation pat ty -> zipLocOf pat ty
        Constructor name args -> case listToMaybe $ reverse args of
            Nothing -> getLoc name
            Just lastArg -> zipLocOf name lastArg
        Variant name arg -> zipLocOf name arg
        
        Record loc _ -> loc
        List loc _ -> loc
        Literal lit -> getLoc lit

-- | a cast template for bifix. Doesn't handle annotations
baseCast :: NameAt p ~ NameAt q => (Pattern p -> Pattern q) -> Pattern p -> Pattern q
baseCast recur = \case
    Var name -> Var name
    Wildcard loc name -> Wildcard loc name
    Constructor name pats -> Constructor name (map recur pats)
    Variant name pat -> Variant name (recur pat)
    Record loc pats -> Record loc (fmap recur pats)
    List loc pats -> List loc (map recur pats)
    Literal lit -> Literal lit
    ann@Annotation{} -> recur ann

cast :: (NameAt p ~ NameAt q) => ((Pattern p -> Pattern q) -> Pattern p -> Pattern q) -> Pattern p -> Pattern q
cast terminals = bifix terminals baseCast