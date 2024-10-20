{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedRecordDot #-}

module Syntax.Type (Type' (..)) where

import Prettyprinter (Doc, Pretty, braces, comma, pretty, punctuate, sep, (<+>), parens, brackets)
import Relude
import Syntax.Row
import CheckerTypes qualified as CT
import CheckerTypes (Loc, HasLoc)

--  Note: Functor-Foldable-Traversable instances don't do the right thing with `Forall` and `Exists`
data Type' n
    = Name n
    | Var n
    | UniVar Loc CT.UniVar
    | Skolem Loc CT.Skolem
    | Application Loc (Type' n) (Type' n)
    | Function Loc (Type' n) (Type' n) -- probably doesn't need a Loc
    | Forall Loc n (Type' n)
    | Exists Loc n (Type' n)
    | Variant Loc (ExtRow (Type' n))
    | Record Loc (ExtRow (Type' n))
    deriving (Show, Eq, Functor, Foldable, Traversable)

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
instance Pretty n => Pretty (Type' n) where
    pretty = prettyPrec 0
      where
        prettyPrec :: Int -> Type' n -> Doc ann
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

instance HasLoc n => HasLoc (Type' n) where
  getLoc = \case
    Name name -> CT.getLoc name
    Var name -> CT.getLoc name
    Skolem loc _ -> loc
    UniVar loc _  -> loc
    Application loc _ _ -> loc
    Function loc _ _ -> loc
    Forall loc _ _ -> loc
    Exists loc _ _ -> loc
    Variant loc _ -> loc
    Record loc _ -> loc
