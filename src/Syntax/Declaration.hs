{-# LANGUAGE LambdaCase #-}
module Syntax.Declaration (Declaration (..), Constructor (..)) where

import Relude
import Syntax.Expression (Binding)
import Syntax.Type (Type')
import Prettyprinter (Pretty (pretty), nest, vsep, line, (<+>), sep, space, encloseSep)
import CheckerTypes (Loc)

data Declaration n
    = Value Loc (Binding n) [Declaration n] -- todo: forbid local type declarations?
    | Type Loc n [n] [Constructor n]
    | Alias Loc n (Type' n)
    | Signature Loc n (Type' n)
    deriving (Show, Eq)

data Constructor n = Constructor Loc n [Type' n] deriving (Show, Eq)

instance Pretty n => Pretty (Declaration n) where
    pretty = \case
       Value _ binding locals -> pretty binding <> line <> whereIfNonEmpty locals <> line <> nest 4 (vsep (pretty <$> locals))
       Signature _ name ty -> pretty name <+> ":" <+> pretty ty
       Type _ name vars cons -> sep ("type" : pretty name : map pretty vars) <+> encloseSep "= " "" (space <> "|" <> space)  (cons <&> \(Constructor _ con args) -> sep (pretty con : map pretty args))
       Alias _ name ty -> "type alias" <+> pretty name <+> "=" <+> pretty ty
      where
        whereIfNonEmpty locals
          | null locals = ""
          | otherwise = nest 2 "where"