{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoFieldSelectors #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Common where

import Data.IdMap (HasId (..))
import Data.Text qualified as Text
import Data.Type.Bool (type (||))
import Data.Type.Ord (Compare, type (>?))
import Error.Diagnose (Position (..))
import Error.Diagnose qualified as M
import GHC.TypeError (Assert, ErrorMessage (..), TypeError)
import LangPrelude
import Prettyprinter
import Prettyprinter.Render.Terminal (AnsiStyle, Color (..), bold, color, colorDull)
import Prelude qualified (Show (..))

-- this file is a bit of a crutch. Perhaps it's better to move the definitions to Type or TypeChecker
-- however, they don't really belong to Type, and moving them to TypeChecker introduces a cyclic dependency (which may or may not be fine)

data Pass
    = Parse -- after parsing
    | NameRes -- etc
    | DependencyRes -- not sure how to call this pass. it computes a dependency graph and collects all sorts of information
    | Fixity

type instance Compare (a :: Pass) (b :: Pass) = ComparePass a b
type family ComparePass a b where
    ComparePass Parse Parse = EQ
    ComparePass NameRes NameRes = EQ
    ComparePass 'Fixity 'Fixity = EQ
    ComparePass 'DependencyRes 'DependencyRes = EQ
    ComparePass Parse _ = LT
    ComparePass _ Parse = GT
    ComparePass NameRes _ = LT
    ComparePass _ NameRes = GT
    ComparePass 'DependencyRes _ = LT
    ComparePass _ 'DependencyRes = GT
    ComparePass 'Fixity _ = LT
    ComparePass _ 'Fixity = GT

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
    | TypeName
    deriving (Show, Eq, Generic, Hashable)
    deriving (Pretty) via (UnAnnotate Name_)

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
        TypeName -> -19

type SimpleName = Located SimpleName_
data SimpleName_
    = Name' Text
    | Wildcard' Text
    deriving (Show, Eq, Ord, Generic, Hashable)
    deriving (Pretty) via (UnAnnotate SimpleName_)

instance IsString SimpleName_ where
    fromString = Name' . fromString

data Located a = a :@ Loc
    deriving (Show, Generic, Functor, Foldable, Traversable)
    deriving (Pretty) via (UnAnnotate (Located a))

{-# COMPLETE L #-}
pattern L :: a -> Located a
pattern L x <- x :@ _

{-# COMPLETE Located #-}
pattern Located :: Loc -> a -> Located a
pattern Located loc x <- x :@ loc
    where
        Located loc x = x :@ loc
instance Eq a => Eq (Located a) where
    (L lhs) == (L rhs) = lhs == rhs

instance Ord a => Ord (Located a) where
    compare (L lhs) (L rhs) = compare lhs rhs

instance Hashable a => Hashable (Located a) where
    hashWithSalt salt (L x) = hashWithSalt salt x
instance HasLoc (Located a) where
    getLoc (Located loc _) = loc

instance PrettyAnsi a => PrettyAnsi (Located a) where
    prettyAnsi opts (L x) = prettyAnsi opts x

instance HasId a => HasId (Located a) where
    toId (L x) = toId x

instance PrettyAnsi SimpleName_ where
    prettyAnsi _ (Name' name) = pretty name
    prettyAnsi _ (Wildcard' txt) = pretty txt

-- | does the name belong to an infix constructor?
isInfixConstructor :: Name -> Bool
isInfixConstructor (L (Name name _)) = Text.head name == ':'
isInfixConstructor _ = False

newtype UniVar = UniVar Id
    deriving (Show, Eq)
    deriving newtype (Hashable, Enum, HasId)
    deriving (Pretty) via (UnAnnotate UniVar)

newtype Id = Id {id :: Int}
    deriving (Show, Eq)
    deriving newtype (Hashable, Pretty, Enum)

instance HasId Id where
    toId = (.id)

newtype Scope = Scope Int deriving (Show, Eq, Ord)

instance PrettyAnsi Name_ where
    prettyAnsi opts = \case
        (Name name id')
            | opts.printIds -> pretty name <> "#" <> pretty id'
            | otherwise -> pretty name
        (Wildcard txt id') -> pretty txt <> "#" <> pretty id'
        BoolName -> "Bool"
        TrueName -> "True"
        ListName -> "List"
        ConsName -> "Cons"
        NilName -> "Nil"
        IntName -> "Int"
        NatName -> "Nat"
        TextName -> "Text"
        CharName -> "Char"
        TypeName -> "Type"
instance PrettyAnsi UniVar where
    prettyAnsi _ (UniVar n) = "?" <> pretty n

newtype Loc = Loc Position
    deriving (Show)
    deriving newtype (Pretty)

instance Eq Loc where
    _ == _ = True -- a crutch for the inferred Eq instances of the AST

instance Hashable Loc where
    hashWithSalt salt _ = salt
data Literal
    = IntLiteral Int
    | TextLiteral Text
    | CharLiteral Text
    deriving (Eq, Ord, Show)
    deriving (Pretty) via UnAnnotate Literal

instance PrettyAnsi Literal where
    prettyAnsi _ = \case
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

instance Semigroup Loc where
    (<>) = zipLoc

zipLocOf :: (HasLoc a, HasLoc b) => a -> b -> Loc
zipLocOf lhs rhs = zipLoc (getLoc lhs) (getLoc rhs)

newtype Index = Index {getIndex :: Int} deriving (Show, Eq, Enum)
newtype Level = Level {getLevel :: Int} deriving (Show, Eq, Enum)

levelToIndex :: Level -> Level -> Index
levelToIndex (Level l) (Level x) = Index $ l - x - 1

incLevel :: Level -> Int -> Level
incLevel (Level l) n = Level $ l + n

toSimpleName :: Name -> SimpleName
toSimpleName (name :@ loc) = toSimpleName_ name :@ loc

toSimpleName_ :: Name_ -> SimpleName_
toSimpleName_ = \case
    Name txt _ -> Name' txt
    Wildcard n _ -> Wildcard' n
    BoolName -> "Bool"
    TrueName -> "True"
    ListName -> "List"
    ConsName -> "Cons"
    NilName -> "Nil"
    IntName -> "Int"
    NatName -> "Nat"
    TextName -> "Text"
    CharName -> "Char"
    TypeName -> "Type"

mkNotes :: [(Loc, M.Marker a)] -> [(Position, M.Marker a)]
mkNotes = fmap \(Loc pos, marker) -> (pos, marker)

newtype PrettyOptions = PrettyOptions {printIds :: Bool}

defaultPrettyOptions :: PrettyOptions
defaultPrettyOptions = PrettyOptions{printIds = True}
class PrettyAnsi a where
    prettyAnsi :: PrettyOptions -> a -> Doc AnsiStyle

prettyDef :: PrettyAnsi a => a -> Doc AnsiStyle
prettyDef = prettyAnsi defaultPrettyOptions

newtype UnAnnotate a = UnAnnotate a

instance Pretty a => Show (UnAnnotate a) where
    show (UnAnnotate x) = show $ pretty x
instance PrettyAnsi a => Pretty (UnAnnotate a) where
    pretty (UnAnnotate x) = unAnnotate $ prettyDef x

instance PrettyAnsi a => PrettyAnsi (Maybe a) where
    prettyAnsi opts = maybe "" (prettyAnsi opts)

keyword :: Doc AnsiStyle -> Doc AnsiStyle
keyword = annotate $ bold <> colorDull Magenta

opStyle :: Doc AnsiStyle -> Doc AnsiStyle
opStyle = annotate $ bold <> colorDull Green

specSym :: Doc AnsiStyle -> Doc AnsiStyle
specSym = annotate $ bold <> color Red

conColor :: Doc AnsiStyle -> Doc AnsiStyle
conColor = annotate $ bold <> colorDull Yellow

typeColor :: Doc AnsiStyle -> Doc AnsiStyle
typeColor = annotate $ bold <> color Blue
