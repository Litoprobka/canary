{-# LANGUAGE DuplicateRecordFields #-}
{-# OPTIONS_GHC -Wno-partial-fields #-}

module Syntax.Value where

import Common (UniVar)
import Common hiding (Skolem, UniVar)
import LangPrelude
import Syntax.Core (CorePattern, CoreTerm)
import Syntax.Row
import Syntax.Term (Erasure, Quantifier, Visibility)

newtype ValueEnv = ValueEnv
    { values :: IdMap Name Value
    }

type Type' = Value

-- unlike the AST types, the location information on Values are shallow, since
-- the way we use it is different from the AST nodes
-- in AST, the location corresponds to the source span where the AST node is written
-- in Values, the location is the source space that the location is *arising from*
data Value
    = -- unbound variables are pretty much the same as skolems
      Var Name
    | -- | a type constructor. unlike value constructors, `Either a b` is represented as a stuck application Either `App` a `App` b
      TyCon Name
    | -- | a fully-applied counstructor
      Con Name [Value]
    | Lambda (Closure ())
    | -- | an escape hatch for interpreter primitives and similar stuff
      -- the Int field is the expected argument count, the list is current partially applied arguments
      PrimFunction
        { name :: Name
        , remaining :: Int
        , captured :: [Value]
        , f :: NonEmpty Value -> Value
        }
    | Record (Row Value)
    | Sigma Value Value
    | Variant OpenName Value
    | -- | A primitive (Text, Char or Int) value. The name 'Literal' is slightly misleading here
      PrimValue Literal
    | -- types
      Function Type' Type'
    | Q Quantifier Visibility Erasure (Closure Type')
    | VariantT (ExtRow Type')
    | RecordT (ExtRow Type')
    | -- stuck computations
      App Value ~Value
    | Case Value [PatternClosure ()]
    | -- typechecking metavars
      UniVar UniVar

isStuck :: Value -> Bool
isStuck = \case
    Var{} -> True
    App{} -> True
    Case{} -> True
    UniVar{} -> True
    _ -> False

data Closure ty = Closure {var :: Name, ty :: ty, env :: ValueEnv, body :: CoreTerm}
data PatternClosure ty = PatternClosure {pat :: CorePattern, ty :: ty, env :: ValueEnv, body :: CoreTerm}
