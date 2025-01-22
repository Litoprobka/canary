{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE UndecidableInstances #-}

module Syntax.Pattern (Pattern (..), uniplate, collectNames, collectReferencedNames) where

import Common (HasLoc, Literal, Loc, NameAt, Pass (..), getLoc, zipLocOf)
import LensyUniplate
import Prettyprinter (Doc, Pretty, braces, brackets, comma, parens, pretty, punctuate, sep, (<+>))
import Relude hiding (show)
import Syntax.Row
import Syntax.Type (Type')
import Syntax.Type qualified as T
import Prelude (show)

data Pattern (p :: Pass)
    = Var (NameAt p)
    | Wildcard Loc Text
    | Annotation (Pattern p) (Type' p)
    | Constructor (NameAt p) [Pattern p]
    | Variant OpenName (Pattern p)
    | Record Loc (Row (Pattern p))
    | List Loc [Pattern p]
    | Literal Literal

deriving instance Eq (Pattern 'Parse)

instance Pretty (NameAt pass) => Pretty (Pattern pass) where
    pretty = go 0
      where
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

instance Pretty (NameAt p) => Show (Pattern p) where
    show = show . pretty

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

instance (UniplateCast (Type' p) (Type' q), NameAt p ~ NameAt q) => UniplateCast (Pattern p) (Pattern q) where
    uniplateCast = uniplate' unicast

uniplate :: SelfTraversal Pattern p p
uniplate f = \case
    Var name -> pure $ Var name
    Wildcard loc name -> pure $ Wildcard loc name
    Annotation pat ty -> Annotation <$> f pat <*> pure ty
    Constructor name pats -> Constructor name <$> traverse f pats
    Variant name pat -> Variant name <$> f pat
    Record loc row -> Record loc <$> traverse f row
    List loc pats -> List loc <$> traverse f pats
    Literal lit -> pure $ Literal lit

uniplate' :: NameAt p ~ NameAt q => (Type' p -> Type' q) -> SelfTraversal Pattern p q
uniplate' castTy f = \case
    Var name -> pure $ Var name
    Wildcard loc name -> pure $ Wildcard loc name
    Annotation pat ty -> Annotation <$> f pat <*> pure (castTy ty)
    Constructor name pats -> Constructor name <$> traverse f pats
    Variant name pat -> Variant name <$> f pat
    Record loc row -> Record loc <$> traverse f row
    List loc pats -> List loc <$> traverse f pats
    Literal lit -> pure $ Literal lit

-- | collects all to-be-declared names in a pattern
collectNames :: Pattern p -> [NameAt p]
collectNames = \case
    Var name -> [name]
    Wildcard{} -> []
    Annotation pat _ -> collectNames pat
    Variant _ pat -> collectNames pat
    Constructor _ pats -> foldMap collectNames pats
    List _ pats -> foldMap collectNames pats
    Record _ row -> foldMap collectNames $ toList row
    Literal _ -> []

collectReferencedNames :: Pattern p -> [NameAt p]
collectReferencedNames = go
  where
    go = \case
        Var _ -> []
        Wildcard{} -> []
        Annotation pat ty -> go pat <> T.collectReferencedNames ty
        Variant _ pat -> go pat
        Constructor con pats -> con : foldMap go pats
        List _ pats -> foldMap go pats
        Record _ row -> foldMap go $ toList row
        Literal _ -> []
