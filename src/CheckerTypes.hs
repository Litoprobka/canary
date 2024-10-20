{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NoFieldSelectors #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# OPTIONS_GHC -Wno-partial-fields #-}

module CheckerTypes (Name (..), UniVar (..), Skolem (..), Scope (..), Id (..), inc, Loc (..), SimpleName (..), HasLoc(..), zipLoc) where

import Prettyprinter
import Relude
import Text.Megaparsec (SourcePos)

-- this file is a bit of a crutch. Perhaps it's better to move the definitions to Type or TypeChecker
-- however, they don't really belong to Type, and moving them to TypeChecker introduces a cyclic dependency (which may or may not be fine)

-- a disambiguated name
-- I haven't decided whether ids should be global or per-name
-- a slight problem with global ids is that anything that uses builtins
-- should take a list of their names
--
-- it is also convenient to pretty print local ids as `name` or `name#10`, which is
-- not really an option with global ids
data Name
    = Name Loc Text Id
    | BoolName Loc
    | ListName Loc
    | IntName Loc
    | NatName Loc
    | TextName Loc
    | CharName Loc
    | LensName Loc
    deriving (Show, Eq, Generic, Hashable)

instance HasLoc Name where
    getLoc (Name loc _ _) = loc
    getLoc _ = Blank

data SimpleName = SimpleName {loc :: Loc, name :: Text} deriving (Show, Eq, Generic, Hashable)

instance Ord SimpleName where
    compare lhs rhs = compare lhs.name rhs.name

instance Pretty SimpleName where
    pretty SimpleName{name} = pretty name

instance HasLoc SimpleName where
    getLoc name = name.loc

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
    pretty = \case
        (Name _ name n) -> pretty name <> "#" <> pretty n
        BoolName{} -> "Bool"
        ListName{} -> "List"
        IntName{} -> "Int"
        NatName{} -> "Nat"
        TextName{} -> "Text"
        CharName{} -> "Char"
        LensName{} -> "Lens"
instance Pretty UniVar where
    pretty (UniVar n) = "#" <> pretty n
instance Pretty Skolem where
    pretty (Skolem (Name _ name n)) = pretty name <> "?" <> pretty n
    pretty (Skolem builtin) = pretty builtin <> "?"

data Loc
    = Loc {start :: SourcePos, end :: SourcePos}
    | Blank
    deriving (Show)

instance Eq Loc where
    _ == _ = True -- a crutch for the inferred Eq instance of Type'

instance Hashable Loc where
    hashWithSalt salt _ = salt

-- this should probably be replaced by a classy lens
class HasLoc a where
    getLoc :: a -> Loc

zipLoc :: Loc -> Loc -> Loc
zipLoc loc Blank = loc
zipLoc Blank loc = loc
zipLoc (Loc start _) (Loc _ end) = Loc start end