{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DerivingVia #-}
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
    PrettyAnsi (..),
    PriorityRelation,
    PriorityRelation' (..),
    UnAnnotate (..),
 )
import Data.Type.Ord (type (<))
import LangPrelude hiding (show)
import Prettyprinter
import Prettyprinter.Render.Terminal (AnsiStyle)
import Syntax.Term (Binding, Type, VarBinder)

type Declaration p = Located (Declaration_ p)
data Declaration_ (p :: Pass)
    = Value (Binding p) [Declaration p]
    | Type (NameAt p) [VarBinder p] [Constructor p]
    | GADT (NameAt p) (Maybe (Type p)) [GadtConstructor p]
    | Signature (NameAt p) (Type p)
    | p < DependencyRes => Fixity Fixity (NameAt p) (PriorityRelation p)

deriving instance Eq (Declaration_ 'Parse)
deriving via (UnAnnotate (Declaration_ p)) instance PrettyAnsi (Declaration_ p) => Pretty (Declaration_ p)
deriving via (UnAnnotate (Declaration_ p)) instance PrettyAnsi (Declaration_ p) => Show (Declaration_ p)

data Constructor p = Constructor {loc :: Loc, name :: NameAt p, args :: [Type p]}
deriving instance Eq (Constructor 'Parse)

data GadtConstructor p = GadtConstructor {loc :: Loc, name :: NameAt p, sig :: Type p}
deriving instance (Eq (NameAt p), Eq (Type p)) => Eq (GadtConstructor p)

instance PrettyAnsi (NameAt p) => PrettyAnsi (Declaration_ p) where
    prettyAnsi opts = \case
        Value binding locals -> prettyAnsi opts binding <> line <> whereIfNonEmpty locals <> line <> nest 4 (vsep (prettyAnsi opts <$> locals))
        Signature name ty -> prettyAnsi opts name <+> ":" <+> prettyAnsi opts ty
        Type name vars cons ->
            sep ("type" : prettyAnsi opts name : map (prettyAnsi opts) vars)
                <+> encloseSep
                    "= "
                    ""
                    (space <> "|" <> space)
                    (cons <&> \(Constructor _ con args) -> sep (prettyAnsi opts con : map (prettyAnsi opts) args))
        GADT name mbKind constrs -> "type" <+> nameWithKind name mbKind <+> "where" <> line <> nest 4 (vsep (prettyAnsi opts <$> constrs))
        Fixity fixity op priority ->
            fixityKeyword fixity
                <+> prettyAnsi opts op
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

        listIfNonEmpty :: PrettyAnsi a => Doc AnsiStyle -> [a] -> Doc AnsiStyle
        listIfNonEmpty _ [] = ""
        listIfNonEmpty kw xs = " " <> kw <+> sep (punctuate comma $ map (prettyAnsi opts) xs)
        whereIfNonEmpty locals
            | null locals = ""
            | otherwise = nest 2 "where"

        nameWithKind name Nothing = prettyAnsi opts name
        nameWithKind name (Just k) = parens $ prettyAnsi opts name <+> ":" <+> prettyAnsi opts k

instance PrettyAnsi (NameAt p) => PrettyAnsi (GadtConstructor p) where
    prettyAnsi opts (GadtConstructor _ name sig) = prettyAnsi opts name <+> ":" <+> prettyAnsi opts sig

instance HasLoc (Constructor p) where
    getLoc Constructor{loc} = loc
