{-# LANGUAGE DuplicateRecordFields #-}

module Syntax.Value where

import Common (UniVar)
import Common hiding (Skolem, UniVar)
import LangPrelude
import Syntax.Core (CorePattern, CoreTerm)
import Syntax.Row
import Syntax.Term (Erasure, Quantifier, Visibility)

data ValueEnv = ValueEnv
    { values :: IdMap Name Value
    , skolems :: IdMap Name Value -- does the split even make sense?
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
      PrimFunction Name (Value -> Value)
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

data Closure ty = Closure {var :: Name, ty :: ty, env :: ValueEnv, body :: CoreTerm}
data PatternClosure ty = PatternClosure {pat :: CorePattern, ty :: ty, env :: ValueEnv, body :: CoreTerm}
