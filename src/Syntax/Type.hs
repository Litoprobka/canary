{-# LANGUAGE LambdaCase #-}

module Syntax.Type (Type' (..)) where

import Prettyprinter (Doc, Pretty, braces, comma, list, pretty, punctuate, sep, (<+>), parens)
import Relude
import Syntax.Row

--  Note: Functor-Foldable-Traversable instances don't do the right thing with `Forall` and `Exists`
data Type' n
    = Name n
    | Var n
    | Application (Type' n) (Type' n)
    | Function (Type' n) (Type' n)
    | Forall n (Type' n)
    | Exists n (Type' n)
    | Variant (Row (Type' n))
    | Record (Row (Type' n))
    deriving (Show, Eq, Functor, Foldable, Traversable)

-- >>> pretty $ Function (Var "a") (Record $ fromList [("x", Name "Int"), ("x", Name "a")])
-- >>> pretty $ Forall "a" $ Forall "b" $ Forall "c" $ Name "a" `Function` (Name "b" `Function` Name "c")
-- >>> pretty $ Forall "a" $ (Forall "b" $ Name "b" `Function` Name "a") `Function` Name "a"
-- >>> pretty $ Application (Forall "f" $ Name "f") (Name "b") `Function` (Application (Application (Name "c") (Name "a")) $ Application (Name "d") (Name "e"))
-- a -> {x : Int, x : a}
-- ∀a. ∀b. ∀c. a -> b -> c
-- ∀a. (∀b. b -> a) -> a
-- (∀f. f) b -> c a (d e)
instance Pretty n => Pretty (Type' n) where
    -- todo: prettyPrec
    pretty = prettyPrec 0
      where
        prettyPrec :: Int -> Type' n -> Doc ann
        prettyPrec prec = \case
            Name name -> pretty name
            Var name -> pretty name
            Application lhs rhs -> parensWhen 3 $ prettyPrec 2 lhs <+> prettyPrec 3 rhs
            Function from to -> parensWhen 2 $ prettyPrec 2 from <+> "->" <+> pretty to
            Forall var body -> parensWhen 1 $ "∀" <> pretty var <> "." <+> pretty body
            Exists var body -> parensWhen 1 $ "∃" <> pretty var <> "." <+> pretty body
            Variant row -> list . map variantItem $ sortedRow row
            Record row -> braces . sep . punctuate comma . map recordField $ sortedRow row
          where
            parensWhen minPrec
                | prec >= minPrec = parens
                | otherwise = id

        -- todo: a special case for unit
        variantItem (name, ty) = pretty name <+> pretty ty
        recordField (name, ty) = pretty name <+> ":" <+> pretty ty
