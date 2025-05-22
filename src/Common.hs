{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoFieldSelectors #-}

module Common (
    Name,
    Name_ (..),
    UniVar (..),
    Skolem (..),
    Scope (..),
    Id (..),
    inc,
    Loc (..),
    Located (..),
    SimpleName,
    SimpleName_ (..),
    HasLoc (..),
    zipLoc,
    NameAt,
    Pass (..),
    zipLocOf,
    locFromSourcePos,
    mkNotes,
    Literal_ (..),
    Literal,
    Fixity (..),
    PriorityRelation,
    PriorityRelation' (..),
    type (!=),
    Cast (..),
    toSimpleName,
    pattern L,
    unLoc,
    noLoc,
    pattern (:@),
) where

import Data.Type.Bool (type (||))
import Data.Type.Ord (Compare, type (>?))
import Error.Diagnose (Position (..))
import Error.Diagnose qualified as M
import GHC.TypeError (Assert, ErrorMessage (..), TypeError)
import LangPrelude
import Prettyprinter
import Text.Megaparsec (SourcePos (..), unPos)

-- this file is a bit of a crutch. Perhaps it's better to move the definitions to Type or TypeChecker
-- however, they don't really belong to Type, and moving them to TypeChecker introduces a cyclic dependency (which may or may not be fine)

data Pass
    = Parse -- after parsing
    | NameRes -- etc
    | DependencyRes -- not sure how to call this pass. it computes a dependency graph and collects all sorts of information
    | Fixity
    | DuringTypecheck -- an intermediate state for univars and skolems

type instance Compare (a :: Pass) (b :: Pass) = ComparePass a b
type family ComparePass a b where
    ComparePass Parse Parse = EQ
    ComparePass NameRes NameRes = EQ
    ComparePass 'Fixity 'Fixity = EQ
    ComparePass 'DuringTypecheck 'DuringTypecheck = EQ
    ComparePass 'DependencyRes 'DependencyRes = EQ
    ComparePass Parse _ = LT
    ComparePass _ Parse = GT
    ComparePass NameRes _ = LT
    ComparePass _ NameRes = GT
    ComparePass 'DependencyRes _ = LT
    ComparePass _ 'DependencyRes = GT
    ComparePass 'Fixity _ = LT
    ComparePass _ 'Fixity = GT
    ComparePass DuringTypecheck _ = LT
    ComparePass _ DuringTypecheck = GT

type (!=) (a :: k) (b :: k) =
    Assert
        (a >? b || b >? a)
        (TypeError ('Text "Cannot satisfy: " ':<>: 'ShowType a ':<>: 'Text " != " ':<>: 'ShowType b))

data Fixity = InfixL | InfixR | InfixChain | Infix deriving (Show, Eq)

type PriorityRelation p = PriorityRelation' (NameAt p)
data PriorityRelation' a = PriorityRelation
    { above :: [Maybe a]
    , below :: [a]
    , equal :: [a]
    }
    deriving (Eq, Functor, Foldable, Traversable)

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
type Name = Located Name_
data Name_
    = Name Text Id
    | Wildcard Int Id
    | BoolName
    | TrueName
    | ListName
    | ConsName
    | NilName
    | IntName
    | NatName
    | TextName
    | CharName
    | LensName
    | TypeName
    deriving (Show, Eq, Generic, Hashable)

-- some hacky code to use Name_ in an EnumMap
-- this relies on the fact that ids are non-negative
-- also, EnumMap wouldn't work well with randomly generated ids
instance Enum Name_ where
    fromEnum = \case
        Name _ (Id id') -> id'
        Wildcard _ (Id id') -> id'
        BoolName -> -10
        TrueName -> -11
        ListName -> -12
        ConsName -> -13
        NilName -> -14
        IntName -> -15
        NatName -> -16
        TextName -> -17
        CharName -> -18
        LensName -> -19
        TypeName -> -20

    -- I don't think we ever care about retrieving name keys from an EnumMap
    toEnum = \case
        -10 -> BoolName
        -11 -> TrueName
        -12 -> ListName
        -13 -> ConsName
        -14 -> NilName
        -15 -> IntName
        -16 -> NatName
        -17 -> TextName
        -18 -> CharName
        -19 -> LensName
        -20 -> TypeName
        n -> Name "" (Id n)

instance Enum Name where
    fromEnum (L name) = fromEnum name
    toEnum = Located Blank . toEnum

type SimpleName = Located SimpleName_
data SimpleName_
    = Name' Text
    | Wildcard' Int
    deriving (Show, Eq, Ord, Generic, Hashable)

data Located a = Located Loc a deriving (Show, Generic, Functor, Foldable, Traversable)

{-# COMPLETE L #-}
pattern L :: a -> Located a
pattern L x <- Located _ x

{-# COMPLETE (:@) #-}
pattern (:@) :: a -> Loc -> Located a
pattern (:@) x loc <- Located loc x
    where
        x :@ loc = Located loc x
instance Eq a => Eq (Located a) where
    (L lhs) == (L rhs) = lhs == rhs

instance Ord a => Ord (Located a) where
    compare (L lhs) (L rhs) = compare lhs rhs

instance Hashable a => Hashable (Located a) where
    hashWithSalt salt (L x) = hashWithSalt salt x
instance HasLoc (Located a) where
    getLoc (Located loc _) = loc

instance Pretty a => Pretty (Located a) where
    pretty (L x) = pretty x

instance Pretty SimpleName_ where
    pretty (Name' name) = pretty name
    pretty (Wildcard' n) = "_" <> pretty n

-- univars use a different range of ids, so it's not clear whether they should use the same Id newtype
newtype UniVar = UniVar Id
    deriving (Show, Eq)
    deriving newtype (Hashable, Enum)

newtype Id = Id {id :: Int}
    deriving (Show, Eq)
    deriving newtype (Hashable, Pretty, Enum)

inc :: Id -> Id
inc (Id n) = Id $ n + 1

newtype Skolem = Skolem Name
    deriving (Show, Eq)
    deriving newtype (Hashable, Enum)

instance HasLoc Skolem where
    getLoc (Skolem name) = getLoc name

newtype Scope = Scope Int deriving (Show, Eq, Ord)

instance Pretty Name_ where
    pretty = \case
        (Name name id') -> pretty name <> "#" <> pretty id'
        (Wildcard n id') -> "_" <> pretty n <> "#" <> pretty id'
        BoolName -> "Bool"
        TrueName -> "True"
        ListName -> "List"
        ConsName -> "Cons"
        NilName -> "Nil"
        IntName -> "Int"
        NatName -> "Nat"
        TextName -> "Text"
        CharName -> "Char"
        LensName -> "Lens"
        TypeName -> "Type"
instance Pretty UniVar where
    pretty (UniVar n) = "#" <> pretty n
instance Pretty Skolem where
    pretty (Skolem (L (Name name n))) = pretty name <> "?" <> pretty n
    pretty (Skolem builtin) = pretty builtin <> "?"

data Loc
    = Loc Position
    | Blank
    deriving (Show)

instance Eq Loc where
    _ == _ = True -- a crutch for the inferred Eq instance of Type'

instance Hashable Loc where
    hashWithSalt salt _ = salt

type Literal = Located Literal_
data Literal_
    = IntLiteral Int
    | TextLiteral Text
    | CharLiteral Text
    deriving (Eq)

instance Pretty Literal_ where
    pretty = \case
        IntLiteral num -> pretty num
        TextLiteral txt -> dquotes $ pretty txt
        CharLiteral c -> "'" <> pretty c <> "'"

-- this should probably be replaced by a classy lens
class HasLoc a where
    getLoc :: a -> Loc

unLoc :: Located a -> a
unLoc (L x) = x

noLoc :: a -> Located a
noLoc = Located Blank

zipLoc :: Loc -> Loc -> Loc
zipLoc loc Blank = loc
zipLoc Blank loc = loc
zipLoc (Loc lhs) (Loc rhs) = Loc $ lhs{begin = min lhs.begin rhs.begin, end = max rhs.begin rhs.end}

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

toSimpleName :: Name -> SimpleName
toSimpleName (Located loc name) = Located loc case name of
    Name txt _ -> Name' txt
    Wildcard n _ -> Wildcard' n
    BoolName -> Name' "Bool"
    TrueName -> Name' "True"
    ListName -> Name' "List"
    ConsName -> Name' "Cons"
    NilName -> Name' "Nil"
    IntName -> Name' "Int"
    NatName -> Name' "Nat"
    TextName -> Name' "Text"
    CharName -> Name' "Char"
    LensName -> Name' "Lens"
    TypeName -> Name' "Type"

mkNotes :: [(Loc, M.Marker a)] -> [(Position, M.Marker a)]
mkNotes = mapMaybe \case
    (Blank, _) -> Nothing
    (Loc pos, marker) -> Just (pos, marker)

-- a class for AST nodes that can be losslessly cast to a different pass
class Cast ty (p :: Pass) (q :: Pass) where
    cast :: ty p -> ty q
