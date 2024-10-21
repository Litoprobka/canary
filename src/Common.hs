{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE NoFieldSelectors #-}
{-# OPTIONS_GHC -Wno-partial-fields #-}

module Common (
    Name (..),
    UniVar (..),
    Skolem (..),
    Scope (..),
    Id (..),
    inc,
    Loc (..),
    SimpleName (..),
    HasLoc (..),
    zipLoc,
    NameAt,
    Pass (..),
    bifix,
    zipLocOf,
    locFromSourcePos,
    mkNotes,
) where

import Error.Diagnose (Position (..), end)
import Error.Diagnose qualified as M
import Prettyprinter
import Relude
import Text.Megaparsec (SourcePos (..), unPos)

-- this file is a bit of a crutch. Perhaps it's better to move the definitions to Type or TypeChecker
-- however, they don't really belong to Type, and moving them to TypeChecker introduces a cyclic dependency (which may or may not be fine)

data Pass
    = Parse -- after parsing
    | NameRes -- etc
    | Fixity
    | DuringTypecheck -- an intermediate state for univars and skolems

type family NameAt (pass :: Pass) where
    NameAt 'Parse = SimpleName
    NameAt other = Name

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
    getLoc = \case
        Name loc _ _ -> loc
        BoolName loc -> loc
        ListName loc -> loc
        IntName loc -> loc
        NatName loc -> loc
        TextName loc -> loc
        CharName loc -> loc
        LensName loc -> loc

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

instance HasLoc Skolem where
    getLoc (Skolem name) = getLoc name

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
    = Loc Position
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
zipLoc (Loc lhs) (Loc rhs) = Loc $ lhs{end = rhs.end}

zipLocOf :: (HasLoc a, HasLoc b) => a -> b -> Loc
zipLocOf lhs rhs = zipLoc (getLoc lhs) (getLoc rhs)

locFromSourcePos :: SourcePos -> SourcePos -> Loc
locFromSourcePos start end =
    Loc $
        Position
            { file = start.sourceName
            , begin = (unPos start.sourceLine, unPos start.sourceColumn)
            , end = (unPos end.sourceLine, unPos end.sourceColumn)
            }

instance Pretty Loc where
    pretty = \case
        Blank -> "<blank>"
        Loc pos -> pretty pos

mkNotes :: [(Loc, M.Marker a)] -> [(Position, M.Marker a)]
mkNotes = mapMaybe \case
    (Blank, _) -> Nothing
    (Loc pos, marker) -> Just (pos{file = "none"}, marker)

-- * Some fancy boilerplate prevention stuff

-- bifix f g = f $ g $ f $ g $ ...
-- we don't need a special case to make bifix it monadic. We do need monadic baseCast-s though
bifix :: ((a -> b) -> a -> b) -> ((a -> b) -> a -> b) -> a -> b
bifix f g = let recur = f (g recur) in recur
