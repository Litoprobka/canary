{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}

module CheckerTypes (Name (..), UniVar (..), Skolem (..), Scope (..), Id(..), inc) where

import Prettyprinter
import Relude

-- this file is a bit of a crutch. Perhaps it's better to move the definitions to Type or TypeChecker
-- however, they don't really to Type, and moving them to TypeChecker introduces a cyclic dependency (which may or may not be fine)

-- a disambiguated name
-- I haven't decided whether ids should be global or per-name
-- a slight problem with global ids is that anything that uses builtins
-- should take a list of their names
--
-- it is also convenient to pretty print local ids as `name` or `name#10`, which is
-- not really an option with global ids
data Name = Name Text Id deriving (Show, Eq, Generic, Hashable)

-- univars use a different range of ids, so it's not clear they should use the same Id newtype
newtype UniVar = UniVar Int
    deriving (Show, Eq)
    deriving newtype (Hashable)

newtype Id = Id {id :: Int}
    deriving (Show, Eq)
    deriving newtype (Hashable, Pretty)

inc :: Id -> Id
inc (Id n) = Id $ n + 1

newtype Skolem = Skolem Name
    deriving (Show, Eq)
    deriving newtype (Hashable)

newtype Scope = Scope Int deriving (Show, Eq, Ord)

instance Pretty Name where
    pretty (Name name n) = pretty name <> "#" <> pretty n
instance Pretty UniVar where
    pretty (UniVar n) = "#" <> pretty n
instance Pretty Skolem where
    pretty (Skolem (Name name n)) = pretty name <> "?" <> pretty n