{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DeriveAnyClass #-}
module CheckerTypes (Name(..), UniVar(..), Skolem(..), Scope(..)) where

import Relude
import Prettyprinter

-- this file is a bit of a crutch. Perhaps it's better to move the definitions to Type or TypeChecker
-- however, they don't really to Type, and moving them to TypeChecker introduces a cyclic dependency (which may or may not be fine)

-- a disambiguated name
data Name = Name Text Int deriving (Show, Eq, Generic, Hashable)
newtype UniVar = UniVar Int
    deriving (Show, Eq)
    deriving newtype (Hashable)

newtype Skolem = Skolem Name
    deriving (Show, Eq)
    deriving newtype (Hashable)

newtype Scope = Scope Int deriving (Show, Eq, Ord)

instance Pretty Name where
    pretty (Name name 0) = pretty name
    pretty (Name name n) = pretty name <> "#" <> pretty n
instance Pretty UniVar where
    pretty (UniVar n) = "#" <> pretty n
instance Pretty Skolem where
    pretty (Skolem (Name name 0)) = pretty name <> "?"
    pretty (Skolem (Name name n)) = pretty name <> "?" <> pretty n