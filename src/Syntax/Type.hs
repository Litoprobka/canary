{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE UndecidableInstances #-}

module Syntax.Type (Type' (..), cast, castM) where

import Common (HasLoc, Loc, NameAt, Pass (..), bifix)
import Common qualified as CT
import Prettyprinter (Doc, Pretty, braces, brackets, comma, parens, pretty, punctuate, sep, (<+>))
import Relude
import Syntax.Row

data Type' (p :: Pass) where
    Name :: NameAt p -> Type' p
    Var :: NameAt p -> Type' p
    UniVar :: Loc -> CT.UniVar -> Type' 'DuringTypecheck
    Skolem :: Loc -> CT.Skolem -> Type' 'DuringTypecheck
    Application :: Loc -> Type' p -> Type' p -> Type' p
    Function :: Loc -> Type' p -> Type' p -> Type' p -- doesn't need a Loc, unless it's used in an infix position
    Forall :: Loc -> NameAt p -> Type' p -> Type' p
    Exists :: Loc -> NameAt p -> Type' p -> Type' p
    Variant :: Loc -> ExtRow (Type' p) -> Type' p
    Record :: Loc -> ExtRow (Type' p) -> Type' p

deriving instance Show (Type' 'DuringTypecheck)
deriving instance Show (Type' 'Fixity)
deriving instance Eq (Type' 'DuringTypecheck)

-- >>> pretty $ Function (Var "a") (Record (fromList [("x", Name "Int"), ("x", Name "a")]) Nothing)
-- >>> pretty $ Forall "a" $ Forall "b" $ Forall "c" $ Name "a" `Function` (Name "b" `Function` Name "c")
-- >>> pretty $ Forall "a" $ (Forall "b" $ Name "b" `Function` Name "a") `Function` Name "a"
-- >>> pretty $ Application (Forall "f" $ Name "f") (Name "b") `Function` (Application (Application (Name "c") (Name "a")) $ Application (Name "d") (Name "e"))
-- >>> pretty $ Record (fromList [("x", Name "Bool")]) (Just "r")
-- >>> pretty $ Variant (fromList [("E", Name "Unit")]) (Just "v")
-- a -> {x : Int, x : a}
-- ∀a. ∀b. ∀c. a -> b -> c
-- ∀a. (∀b. b -> a) -> a
-- (∀f. f) b -> c a (d e)
-- {x : Bool | r}
-- [E Unit | v]
instance Pretty (NameAt pass) => Pretty (Type' pass) where
    pretty = prettyPrec 0
      where
        prettyPrec :: Int -> Type' pass -> Doc ann
        prettyPrec prec = \case
            Name name -> pretty name
            Var name -> pretty name
            Skolem _ skolem -> pretty skolem
            UniVar _ uni -> pretty uni
            Application _ lhs rhs -> parensWhen 3 $ prettyPrec 2 lhs <+> prettyPrec 3 rhs
            Function _ from to -> parensWhen 2 $ prettyPrec 2 from <+> "->" <+> pretty to
            Forall _ var body -> parensWhen 1 $ "∀" <> pretty var <> "." <+> pretty body
            Exists _ var body -> parensWhen 1 $ "∃" <> pretty var <> "." <+> pretty body
            Variant _ row -> brackets . withExt row . sep . punctuate comma . map variantItem $ sortedRow row.row
            Record _ row -> braces . withExt row . sep . punctuate comma . map recordField $ sortedRow row.row
          where
            parensWhen minPrec
                | prec >= minPrec = parens
                | otherwise = id

        withExt row = maybe id (\r doc -> doc <+> "|" <+> pretty r) (extension row)

        -- todo: a special case for unit
        variantItem (name, ty) = pretty name <+> pretty ty
        recordField (name, ty) = pretty name <+> ":" <+> pretty ty

instance HasLoc (NameAt pass) => HasLoc (Type' pass) where
    getLoc = \case
        Name name -> CT.getLoc name
        Var name -> CT.getLoc name
        Skolem loc _ -> loc
        UniVar loc _ -> loc
        Application loc _ _ -> loc
        Function loc _ _ -> loc
        Forall loc _ _ -> loc
        Exists loc _ _ -> loc
        Variant loc _ -> loc
        Record loc _ -> loc

-- | this is a cast template to be used with bifix. It doesn't handle univars and skolems
baseCast :: NameAt p ~ NameAt q => (Type' p -> Type' q) -> Type' p -> Type' q
baseCast recur = \case
    Name name -> Name name
    Var name -> Var name
    Application loc lhs rhs -> Application loc (recur lhs) (recur rhs)
    Function loc lhs rhs -> Function loc (recur lhs) (recur rhs)
    Forall loc var body -> Forall loc var (recur body)
    Exists loc var body -> Exists loc var (recur body)
    Variant loc row -> Variant loc (recur <$> row)
    Record loc row -> Record loc (recur <$> row)
    other -> recur other

baseCastM :: Applicative m => NameAt p ~ NameAt q => (Type' p -> m (Type' q)) -> Type' p -> m (Type' q)
baseCastM recur = \case
    Name name -> pure $ Name name
    Var name -> pure $ Var name
    Application loc lhs rhs -> Application loc <$> recur lhs <*> recur rhs
    Function loc lhs rhs -> Function loc <$> recur lhs <*> recur rhs
    Forall loc var body -> Forall loc var <$> recur body
    Exists loc var body -> Exists loc var <$> recur body
    Variant loc row -> Variant loc <$> traverse recur row
    Record loc row -> Record loc <$> traverse recur row
    other -> recur other

cast :: NameAt p ~ NameAt q => ((Type' p -> Type' q) -> Type' p -> Type' q) -> Type' p -> Type' q
cast terminals = bifix terminals baseCast

castM :: Applicative m => NameAt p ~ NameAt q => ((Type' p -> m (Type' q)) -> Type' p -> m (Type' q)) -> Type' p ->  m (Type' q)
castM terminals = bifix terminals baseCastM