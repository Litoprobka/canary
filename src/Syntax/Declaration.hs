{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoFieldSelectors #-}

module Syntax.Declaration (Declaration_ (..), Declaration, Constructor (..), GadtConstructor (..)) where

import Common (
    Fixity (..),
    HasLoc (..),
    Loc,
    Located,
    NameAt,
    Pass (DependencyRes, Parse),
    PriorityRelation,
    PriorityRelation' (..),
 )
import Data.Type.Ord (type (<))
import LangPrelude hiding (show)
import Prettyprinter
import Syntax.Term (Binding, Type, VarBinder)
import Prelude (show)

type Declaration p = Located (Declaration_ p)
data Declaration_ (p :: Pass)
    = Value (Binding p) [Declaration p]
    | Type (NameAt p) [VarBinder p] [Constructor p]
    | GADT (NameAt p) (Maybe (Type p)) [GadtConstructor p]
    | Signature (NameAt p) (Type p)
    | p < DependencyRes => Fixity Fixity (NameAt p) (PriorityRelation p)

deriving instance Eq (Declaration_ 'Parse)

data Constructor p = Constructor {loc :: Loc, name :: NameAt p, args :: [Type p]}
deriving instance Eq (Constructor 'Parse)

data GadtConstructor p = GadtConstructor {loc :: Loc, name :: NameAt p, sig :: Type p}
deriving instance (Eq (NameAt p), Eq (Type p)) => Eq (GadtConstructor p)

instance Pretty (NameAt p) => Pretty (Declaration_ p) where
    pretty = \case
        Value binding locals -> pretty binding <> line <> whereIfNonEmpty locals <> line <> nest 4 (vsep (pretty <$> locals))
        Signature name ty -> pretty name <+> ":" <+> pretty ty
        Type name vars cons ->
            sep ("type" : pretty name : map pretty vars)
                <+> encloseSep "= " "" (space <> "|" <> space) (cons <&> \(Constructor _ con args) -> sep (pretty con : map pretty args))
        GADT name mbKind constrs -> "type" <+> nameWithKind name mbKind <+> "where" <> line <> nest 4 (vsep (pretty <$> constrs))
        Fixity fixity op priority ->
            fixityKeyword fixity
                <+> pretty op
                <> listIfNonEmpty "above" priority.above
                <> listIfNonEmpty "below" priority.below
                <> listIfNonEmpty "equals" priority.equal
      where
        fixityKeyword :: Fixity -> Doc ann
        fixityKeyword = \case
            InfixL -> "infix left"
            InfixR -> "infix right"
            InfixChain -> "infix chain"
            Infix -> "infix"

        listIfNonEmpty _ [] = ""
        listIfNonEmpty kw xs = " " <> kw <+> sep (punctuate comma $ map pretty xs)
        whereIfNonEmpty locals
            | null locals = ""
            | otherwise = nest 2 "where"

        nameWithKind name Nothing = pretty name
        nameWithKind name (Just k) = parens $ pretty name <+> ":" <+> pretty k

instance Pretty (NameAt p) => Pretty (GadtConstructor p) where
    pretty (GadtConstructor _ name sig) = pretty name <+> ":" <+> pretty sig

instance Pretty (NameAt p) => Show (Declaration_ p) where
    show = show . pretty

instance HasLoc (Constructor p) where
    getLoc Constructor{loc} = loc
