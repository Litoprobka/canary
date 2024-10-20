{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE UndecidableInstances #-}

module Syntax.Declaration (Declaration (..), Constructor (..)) where

import Common (Loc, NameAt, Pass)
import Prettyprinter (Pretty (pretty), encloseSep, line, nest, sep, space, vsep, (<+>))
import Relude
import Syntax.Expression (Binding)
import Syntax.Type (Type')

data Declaration (p :: Pass)
    = Value Loc (Binding p) [Declaration p] -- todo: forbid local type declarations?
    | Type Loc (NameAt p) [NameAt p] [Constructor p]
    | Alias Loc (NameAt p) (Type' p)
    | Signature Loc (NameAt p) (Type' p)

deriving instance Show (NameAt pass) => Show (Declaration pass)
deriving instance Eq (NameAt pass) => Eq (Declaration pass)

data Constructor p = Constructor Loc (NameAt p) [Type' p]
deriving instance Show (NameAt pass) => Show (Constructor pass)
deriving instance Eq (NameAt pass) => Eq (Constructor pass)

instance Pretty (NameAt p) => Pretty (Declaration p) where
    pretty = \case
        Value _ binding locals -> pretty binding <> line <> whereIfNonEmpty locals <> line <> nest 4 (vsep (pretty <$> locals))
        Signature _ name ty -> pretty name <+> ":" <+> pretty ty
        Type _ name vars cons ->
            sep ("type" : pretty name : map pretty vars)
                <+> encloseSep "= " "" (space <> "|" <> space) (cons <&> \(Constructor _ con args) -> sep (pretty con : map pretty args))
        Alias _ name ty -> "type alias" <+> pretty name <+> "=" <+> pretty ty
      where
        whereIfNonEmpty locals
            | null locals = ""
            | otherwise = nest 2 "where"