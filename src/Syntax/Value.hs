{-# LANGUAGE DuplicateRecordFields #-}
{-# OPTIONS_GHC -Wno-partial-fields #-}

module Syntax.Value where

import Common (UniVar)
import Common hiding (Skolem, UniVar)
import Data.Sequence qualified as Seq
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
    = -- | a type constructor. Unlike value constructors, they don't keep track of arity and may be applied to values
      TyCon Name [Value]
    | -- | a fully-applied counstructor
      Con Name [Value]
    | Lambda (Closure ())
    | -- | an escape hatch for interpreter primitives and similar stuff
      PrimFunction PrimFunc
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
    | Stuck Stuck (Seq StuckPart)

pattern Var :: Name -> Value
pattern Var name <- Stuck (OnVar name) Seq.Empty
    where
        Var name = Stuck (OnVar name) Seq.Empty

pattern UniVar :: UniVar -> Value
pattern UniVar uni <- Stuck (OnUniVar uni) Seq.Empty
    where
        UniVar uni = Stuck (OnUniVar uni) Seq.Empty

data PrimFunc = PrimFunc
    { name :: Name
    , remaining :: Int
    , captured :: [Value]
    , f :: NonEmpty Value -> Value
    }

data Stuck
    = OnVar Name
    | OnUniVar UniVar

-- `Stuck (OnVar f) [App x, App y, Fn prim]`
-- represents `prim ((f x) y)`
data StuckPart
    = App ~Value -- _ x
    | Fn PrimFunc -- f _
    | Case [PatternClosure ()] -- case _ of

data Closure ty = Closure {var :: Name, ty :: ty, env :: ValueEnv, body :: CoreTerm}
data PatternClosure ty = PatternClosure {pat :: CorePattern, ty :: ty, env :: ValueEnv, body :: CoreTerm}
