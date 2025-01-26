{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoFieldSelectors #-}

module Syntax.Declaration (Declaration (..), Constructor (..), GadtConstructor (..)) where

import Common (
    Cast (..),
    Fixity (..),
    HasLoc (..),
    Loc,
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

data Declaration (p :: Pass)
    = Value Loc (Binding p) [Declaration p]
    | Type Loc (NameAt p) [VarBinder p] [Constructor p]
    | GADT Loc (NameAt p) (Maybe (Type p)) [GadtConstructor p]
    | Signature Loc (NameAt p) (Type p)
    | p < DependencyRes => Fixity Loc Fixity (NameAt p) (PriorityRelation p)

deriving instance Eq (Declaration 'Parse)

data Constructor p = Constructor {loc :: Loc, name :: NameAt p, args :: [Type p]}
deriving instance Eq (Constructor 'Parse)

data GadtConstructor p = GadtConstructor {loc :: Loc, name :: NameAt p, sig :: Type p}
deriving instance (Eq (NameAt p), Eq (Type p)) => Eq (GadtConstructor p)

instance Pretty (NameAt p) => Pretty (Declaration p) where
    pretty = \case
        Value _ binding locals -> pretty binding <> line <> whereIfNonEmpty locals <> line <> nest 4 (vsep (pretty <$> locals))
        Signature _ name ty -> pretty name <+> ":" <+> pretty ty
        Type _ name vars cons ->
            sep ("type" : pretty name : map pretty vars)
                <+> encloseSep "= " "" (space <> "|" <> space) (cons <&> \(Constructor _ con args) -> sep (pretty con : map pretty args))
        GADT _ name mbKind constrs -> "type" <+> nameWithKind name mbKind <+> "where" <> line <> nest 4 (vsep (pretty <$> constrs))
        Fixity _ fixity op priority ->
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

instance Pretty (NameAt p) => Show (Declaration p) where
    show = show . pretty

instance HasLoc (Declaration p) where
    getLoc = \case
        Value loc _ _ -> loc
        Type loc _ _ _ -> loc
        GADT loc _ _ _ -> loc
        Signature loc _ _ -> loc
        Fixity loc _ _ _ -> loc

instance HasLoc (Constructor p) where
    getLoc Constructor{loc} = loc

instance (Cast Type p q, NameAt p ~ NameAt q) => Cast Constructor p q where
    cast Constructor{loc, name, args} = Constructor{loc, name, args = fmap cast args}

instance (Cast Type p q, NameAt p ~ NameAt q) => Cast GadtConstructor p q where
    cast GadtConstructor{loc, name, sig} = GadtConstructor{loc, name, sig = cast sig}
