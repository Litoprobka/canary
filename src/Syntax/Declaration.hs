{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE UndecidableInstances #-}

module Syntax.Declaration (Declaration (..), Constructor (..)) where

import Common (Fixity (..), HasLoc (..), Loc, NameAt, Pass (DependencyRes, Parse), PriorityRelation, PriorityRelation' (..))
import Data.Type.Ord (type (<))
import Prettyprinter (Doc, Pretty (pretty), comma, encloseSep, line, nest, punctuate, sep, space, vsep, (<+>))
import Relude hiding (show)
import Syntax.Expression (Binding)
import Syntax.Type (Type')
import Prelude (show)

data Declaration (p :: Pass)
    = Value Loc (Binding p) [Declaration p]
    | Type Loc (NameAt p) [NameAt p] [Constructor p]
    | p < DependencyRes => Signature Loc (NameAt p) (Type' p)
    | p < DependencyRes => Fixity Loc Fixity (NameAt p) (PriorityRelation p)

deriving instance Eq (Declaration 'Parse)

data Constructor p = Constructor {loc :: Loc, name :: NameAt p, args :: [Type' p]}
deriving instance Eq (Constructor 'Parse)
instance Pretty (NameAt p) => Pretty (Declaration p) where
    pretty = \case
        Value _ binding locals -> pretty binding <> line <> whereIfNonEmpty locals <> line <> nest 4 (vsep (pretty <$> locals))
        Signature _ name ty -> pretty name <+> ":" <+> pretty ty
        Type _ name vars cons ->
            sep ("type" : pretty name : map pretty vars)
                <+> encloseSep "= " "" (space <> "|" <> space) (cons <&> \(Constructor _ con args) -> sep (pretty con : map pretty args))
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

instance Pretty (NameAt p) => Show (Declaration p) where
    show = show . pretty

instance HasLoc (Declaration p) where
    getLoc = \case
        Value loc _ _ -> loc
        Type loc _ _ _ -> loc
        Signature loc _ _ -> loc
        Fixity loc _ _ _ -> loc

instance HasLoc (Constructor p) where
    getLoc (Constructor loc _ _) = loc
