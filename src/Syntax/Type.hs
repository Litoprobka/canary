{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE UndecidableInstances #-}

module Syntax.Type (Type' (..), VarBinder (..), uniplate, uniplate', prettyType, plainBinder) where

import Common (Cast (..), HasLoc, Loc, NameAt, Pass (..), getLoc, zipLocOf, type (!=))
import Common qualified as CT
import LensyUniplate hiding (cast)
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
    Forall :: Loc -> VarBinder p -> Type' p -> Type' p
    Exists :: Loc -> VarBinder p -> Type' p -> Type' p
    Variant :: Loc -> ExtRow (Type' p) -> Type' p
    Record :: Loc -> ExtRow (Type' p) -> Type' p

deriving instance Eq (Type' 'DuringTypecheck)
deriving instance Eq (Type' 'Parse)

data VarBinder p = VarBinder {var :: NameAt p, kind :: Maybe (Type' p)}

deriving instance Eq (VarBinder 'DuringTypecheck)
deriving instance Eq (VarBinder 'Parse)

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
    pretty :: Type' pass -> Doc ann
    pretty = prettyType 0

instance Pretty (NameAt pass) => Pretty (VarBinder pass) where
    pretty = prettyBinder

prettyType :: Pretty (NameAt pass) => Int -> Type' pass -> Doc ann
prettyType prec = \case
    Name name -> pretty name
    Var name -> pretty name
    Skolem skolem -> pretty skolem
    UniVar _ uni -> pretty uni
    Application lhs rhs -> parensWhen 3 $ prettyType 2 lhs <+> prettyType 3 rhs
    Function _ from to -> parensWhen 2 $ prettyType 2 from <+> "->" <+> pretty to
    Forall _ var body -> parensWhen 1 $ "∀" <> prettyBinder var <> "." <+> pretty body
    Exists _ var body -> parensWhen 1 $ "∃" <> prettyBinder var <> "." <+> pretty body
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

prettyBinder :: Pretty (NameAt pass) => VarBinder pass -> Doc ann
prettyBinder (VarBinder var Nothing) = pretty var
prettyBinder (VarBinder var (Just kind)) = parens $ pretty var <+> ":" <+> prettyType 0 kind

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

instance HasLoc (NameAt pass) => HasLoc (VarBinder pass) where
    getLoc VarBinder{var, kind = Nothing} = getLoc var
    getLoc VarBinder{var, kind = Just ty} = zipLocOf var ty

uniplate :: Traversal' (Type' p) (Type' p)
uniplate = uniplate' id UniVar Skolem

instance {-# OVERLAPPING #-} NameAt p ~ CT.Name => UniplateCast (Type' p) (Type' DuringTypecheck) where
    uniplateCast = uniplate' id UniVar Skolem

instance (NameAt p ~ NameAt q, p != DuringTypecheck, q != DuringTypecheck) => UniplateCast (Type' p) (Type' q) where
    uniplateCast = uniplate' id undefined undefined -- we need some kind of `absurd` here

instance (Cast Type' p q, NameAt p ~ NameAt q) => Cast VarBinder p q where
    cast VarBinder{var, kind} = VarBinder{var, kind = fmap cast kind}

-- type-changing uniplate
uniplate'
    :: (NameAt p -> NameAt q)
    -> (p ~ DuringTypecheck => Loc -> CT.UniVar -> Type' q)
    -> (p ~ DuringTypecheck => CT.Skolem -> Type' q)
    -> SelfTraversal Type' p q
uniplate' castName castUni castSkolem recur = \case
    Application lhs rhs -> Application <$> recur lhs <*> recur rhs
    Function loc lhs rhs -> Function loc <$> recur lhs <*> recur rhs
    Forall loc var body -> Forall loc <$> castBinder var <*> recur body
    Exists loc var body -> Exists loc <$> castBinder var <*> recur body
    Variant loc row -> Variant loc <$> traverse recur row
    Record loc row -> Record loc <$> traverse recur row
    Name name -> pure $ Name $ castName name
    Var name -> pure $ Var $ castName name
    UniVar loc uni -> pure $ castUni loc uni
    Skolem skolem -> pure $ castSkolem skolem
  where
    castBinder (VarBinder name mbK) = VarBinder (castName name) <$> traverse recur mbK

plainBinder :: NameAt p -> VarBinder p
plainBinder = flip VarBinder Nothing
