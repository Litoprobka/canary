{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -Wno-partial-fields #-}

module Syntax.Value where

import Common (UniVar)
import Common hiding (Skolem, UniVar)
import Data.Vector qualified as Vec
import LangPrelude
import Syntax.Core (CorePattern, CoreTerm)
import Syntax.Core qualified as C
import Syntax.Row
import Syntax.Term (Erasure (..), Quantifier (..), Visibility (Visible))

-- Values probably shouldn't close over top level bindings
data ValueEnv = ValueEnv
    { topLevel :: IdMap Name_ Value
    , locals :: [Value] -- accessed via de bruijn indexes
    }

type VType = Value

data Value
    = -- | a fully-applied type constructor
      TyCon Name (Vector (Visibility, Value))
    | -- | a fully-applied counstructor
      Con Name (Vector (Visibility, Value))
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
pattern Type name <- TyCon name (Vec.null -> True)
    where
        Type name = TyCon name Vec.empty

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

-- I have a feeling that it's safer to stick to CoreTerm in the cases where I have to introduce new binders

-- | lift a value through N new binders, altering all encountered levels
lift :: Int -> Value -> Value
lift n = go
  where
    go = \case
        TyCon name args -> TyCon name ((fmap . fmap) go args)
        Con name args -> Con name ((fmap . fmap) go args)
        Lambda vis Closure{..} -> Lambda vis $ Closure{body = C.lift n body, env = liftEnv env, ..}
        PrimFunction fn -> PrimFunction (liftFunc fn)
        Record row -> Record (fmap go row)
        RecordT row -> RecordT (fmap go row)
        VariantT row -> VariantT (fmap go row)
        Sigma lhs rhs -> Sigma (go lhs) (go rhs)
        Variant name arg -> Variant name (go arg)
        PrimValue prim -> PrimValue prim
        Q q v e Closure{..} -> Q q v e $ Closure{body = C.lift n body, ty = go ty, env = liftEnv env, ..}
        Stuck stuck -> Stuck (liftStuck stuck)

    liftStuck = \case
        VarApp (Level lvl) spine -> VarApp (Level $ lvl + n) ((fmap . fmap) go spine)
        UniVarApp uni spine -> UniVarApp uni ((fmap . fmap) go spine)
        Fn fn stuck -> Fn (liftFunc fn) (liftStuck stuck)
        Case stuck branches -> Case (liftStuck stuck) (fmap liftPatternClosure branches)

    liftEnv ValueEnv{locals, ..} = ValueEnv{locals = fmap go locals, ..}
    liftFunc PrimFunc{captured, ..} = PrimFunc{captured = fmap go captured, ..}

    liftPatternClosure PatternClosure{body, env, ..} = PatternClosure{body = C.lift n body, env = liftEnv env, ..}
