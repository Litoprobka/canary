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
    mkNotes,
    Literal_ (..),
    Literal,
    Fixity (..),
    PriorityRelation,
    PriorityRelation' (..),
    type (!=),
    toSimpleName,
    pattern L,
    unLoc,
    pattern (:@),
    isInfixConstructor,
) where

import Data.Text qualified as Text
import Data.Type.Bool (type (||))
import Data.Type.Ord (Compare, type (>?))
import Error.Diagnose (Position (..))
import Error.Diagnose qualified as M
import GHC.TypeError (Assert, ErrorMessage (..), TypeError)
import IdMap (HasId (..))
import LangPrelude
import Prettyprinter

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
    | Wildcard Text Id
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

instance HasId Name_ where
    toId = \case
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

type SimpleName = Located SimpleName_
data SimpleName_
    = Name' Text
    | Wildcard' Text
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

instance HasId a => HasId (Located a) where
    toId (L x) = toId x

instance Pretty SimpleName_ where
    pretty (Name' name) = pretty name
    pretty (Wildcard' n) = "_" <> pretty n

-- | does the name belong to an infix constructor?
isInfixConstructor :: Name -> Bool
isInfixConstructor (L (Name name _)) = Text.head name == ':'
isInfixConstructor _ = False

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
    deriving newtype (Hashable, HasId)

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

newtype Loc = Loc Position
    deriving (Show)
    deriving newtype (Pretty)

instance Eq Loc where
    _ == _ = True -- a crutch for the inferred Eq instances of the AST

instance Hashable Loc where
    hashWithSalt salt _ = salt

type Literal = Located Literal_
data Literal_
    = IntLiteral Int
    | TextLiteral Text
    | CharLiteral Text
    deriving (Eq, Ord)

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

zipLoc :: Loc -> Loc -> Loc
zipLoc (Loc lhs) (Loc rhs) = Loc $ lhs{begin = min lhs.begin rhs.begin, end = max rhs.begin rhs.end}

zipLocOf :: (HasLoc a, HasLoc b) => a -> b -> Loc
zipLocOf lhs rhs = zipLoc (getLoc lhs) (getLoc rhs)

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
mkNotes = fmap \(Loc pos, marker) -> (pos, marker)
