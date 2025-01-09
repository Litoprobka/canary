{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE UndecidableInstances #-}

module Syntax.Type (Type' (..), uniplate, uniplate') where

import Common (HasLoc, Loc, NameAt, Pass (..), getLoc, zipLocOf)
import Common qualified as CT
import LensyUniplate
import Prettyprinter (Doc, Pretty, braces, brackets, comma, parens, pretty, punctuate, sep, (<+>))
import Relude hiding (show)
import Syntax.Row
import Prelude (show)

data Type' (p :: Pass) where
    Name :: NameAt p -> Type' p
    Var :: NameAt p -> Type' p
    UniVar :: Loc -> CT.UniVar -> Type' 'DuringTypecheck
    Skolem :: CT.Skolem -> Type' 'DuringTypecheck
    Application :: Type' p -> Type' p -> Type' p
    Function :: Loc -> Type' p -> Type' p -> Type' p -- doesn't need a Loc, unless it's used in an infix position
    Forall :: Loc -> NameAt p -> Type' p -> Type' p
    Exists :: Loc -> NameAt p -> Type' p -> Type' p
    Variant :: Loc -> ExtRow (Type' p) -> Type' p
    Record :: Loc -> ExtRow (Type' p) -> Type' p

deriving instance Eq (Type' 'DuringTypecheck)
deriving instance Eq (Type' 'Parse)

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
            Skolem skolem -> pretty skolem
            UniVar _ uni -> pretty uni
            Application lhs rhs -> parensWhen 3 $ prettyPrec 2 lhs <+> prettyPrec 3 rhs
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

instance Pretty (NameAt p) => Show (Type' p) where
    show = show . pretty

instance HasLoc (NameAt pass) => HasLoc (Type' pass) where
    getLoc = \case
        Name name -> getLoc name
        Var name -> getLoc name
        Skolem skolem -> getLoc skolem
        UniVar loc _ -> loc
        Application lhs rhs -> zipLocOf lhs rhs
        Function loc _ _ -> loc
        Forall loc _ _ -> loc
        Exists loc _ _ -> loc
        Variant loc _ -> loc
        Record loc _ -> loc

uniplate :: Traversal' (Type' p) (Type' p)
uniplate = uniplate' id UniVar Skolem

instance NameAt p ~ CT.Name => UniplateCast (Type' p) (Type' DuringTypecheck) where
    uniplateCast = uniplate' id UniVar Skolem

instance UniplateCast (Type' NameRes) (Type' Fixity) where
    uniplateCast = uniplate' id undefined undefined -- we need some kind of `absurd` here

-- type-changing uniplate
uniplate'
    :: (NameAt p -> NameAt q)
    -> (p ~ DuringTypecheck => Loc -> CT.UniVar -> Type' q)
    -> (p ~ DuringTypecheck => CT.Skolem -> Type' q)
    -> SelfTraversal Type' p q
uniplate' castName castUni castSkolem recur = \case
    Application lhs rhs -> Application <$> recur lhs <*> recur rhs
    Function loc lhs rhs -> Function loc <$> recur lhs <*> recur rhs
    Forall loc var body -> Forall loc (castName var) <$> recur body
    Exists loc var body -> Exists loc (castName var) <$> recur body
    Variant loc row -> Variant loc <$> traverse recur row
    Record loc row -> Record loc <$> traverse recur row
    Name name -> pure $ Name $ castName name
    Var name -> pure $ Var $ castName name
    UniVar loc uni -> pure $ castUni loc uni
    Skolem skolem -> pure $ castSkolem skolem
