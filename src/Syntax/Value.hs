{-# LANGUAGE DuplicateRecordFields #-}
{-# OPTIONS_GHC -Wno-partial-fields #-}

module Syntax.Value where

import Common (UniVar)
import Common hiding (Skolem, UniVar)
import LangPrelude
import Syntax.Core (CorePattern, CoreTerm)
import Syntax.Row
import Syntax.Term (Erasure (..), Quantifier (..), Visibility (Visible))

data ValueEnv = ValueEnv
    { topLevel :: IdMap Name_ Value
    , locals :: [Value] -- accessed via de bruijn indexes
    }

type VType = Value

-- unlike the AST types, the location information on Values are shallow, since
-- the way we use it is different from the AST nodes
-- in AST, the location corresponds to the source span where the AST node is written
-- in Values, the location is the source space that the location is *arising from*
data Value
    = -- | a type constructor. Unlike value constructors, they don't keep track of arity and may be applied to values
      TyCon Name [Value]
    | -- | a fully-applied counstructor
      Con Name [Value]
    | Lambda Visibility (Closure ())
    | -- | an escape hatch for interpreter primitives and similar stuff
      PrimFunction PrimFunc
    | Record (Row Value)
    | Sigma Value Value
    | Variant OpenName Value
    | -- | A primitive (Text, Char or Int) value. The name 'Literal' is slightly misleading here
      PrimValue Literal
    | -- types
      Q Quantifier Visibility Erasure (Closure VType)
    | VariantT (ExtRow VType)
    | RecordT (ExtRow VType)
    | Stuck Stuck

pattern Var :: Level -> Value
pattern Var lvl <- Stuck (VarApp lvl [])
    where
        Var lvl = Stuck (VarApp lvl [])

pattern UniVar :: UniVar -> Value
pattern UniVar uni <- Stuck (UniVarApp uni [])
    where
        UniVar uni = Stuck (UniVarApp uni [])

pattern Type :: Name -> Value
pattern Type name <- TyCon name []
    where
        Type name = TyCon name []

pattern Pi :: Closure VType -> Value
pattern Pi closure <- Q Forall Visible Retained closure
    where
        Pi closure = Q Forall Visible Retained closure

data PrimFunc = PrimFunc
    { name :: Name
    , remaining :: Int
    , captured :: [Value]
    , f :: NonEmpty Value -> Value
    }

-- a reversed list of applications
-- OnVar x [a, b, c] ~ x c b a
type Spine = [(Visibility, Value)]

data Stuck
    = VarApp Level Spine
    | UniVarApp UniVar Spine
    | Fn PrimFunc Stuck
    | Case Stuck [PatternClosure ()]

data Closure ty = Closure
    { var :: SimpleName_
    , ty :: ty
    , env :: ValueEnv
    , body :: CoreTerm
    }
data PatternClosure ty = PatternClosure
    { pat :: CorePattern
    , ty :: ty
    , env :: ValueEnv
    , body :: CoreTerm
    }
