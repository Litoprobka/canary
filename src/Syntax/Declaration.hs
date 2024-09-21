{-# LANGUAGE LambdaCase #-}
module Syntax.Declaration (Declaration (..)) where

import Relude
import Syntax.Expression (Binding)
import Syntax.Type (Type')
import Prettyprinter (Pretty (pretty), nest, vsep, line, (<+>), sep, space, encloseSep)

data Declaration n
    = Value (Binding n) [Declaration n] -- todo: forbid local type declarations?
    | Type n [n] [(n, [Type' n])]
    | Alias n (Type' n)
    | Signature n (Type' n)
    deriving (Show, Eq)

instance Pretty n => Pretty (Declaration n) where
    pretty = \case
       Value binding locals -> pretty binding <> line <> whereIfNonEmpty locals <> line <> nest 4 (vsep (pretty <$> locals))
       Signature name ty -> pretty name <+> ":" <+> pretty ty
       Type name vars cons -> "type" <+> pretty name <+> sep (pretty <$> vars) <+> encloseSep "= " "" (space <> "|" <> space)  (cons <&> \(con, args) -> sep (pretty con : map pretty args))
       Alias name ty -> "type alias" <+> pretty name <+> "=" <+> pretty ty
      where
        whereIfNonEmpty locals
          | null locals = ""
          | otherwise = nest 2 "where"