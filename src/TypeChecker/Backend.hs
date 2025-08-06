{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -Wno-partial-fields #-}

module TypeChecker.Backend where

import Common
import Data.EnumMap.Strict qualified as EMap
import Data.EnumSet qualified as ESet
import Data.IdMap qualified as Map
import Data.Row
import Diagnostic (Diagnose, internalError')
import Effectful.Labeled (Labeled, labeled, runLabeled)
import Effectful.Reader.Static
import Effectful.State.Static.Local
import Eval (ExtendedEnv (..), Postponed, Postponings, UniVarState (..), UniVars, evalCore, quote, quoteWhnf)
import LangPrelude
import NameGen (NameGen, freshId, runNameGen)
import Prettyprinter.Render.Terminal (AnsiStyle)
import Syntax
import Syntax.Core qualified as C
import Syntax.Elaborated qualified as E
import Syntax.Value qualified as V
import Trace

newtype ConstructorTable = ConstructorTable
    { table :: IdMap Name_ (IdMap Name_ ([ExType] -> [ExType]))
    }
data ExType = TyCon Name_ [ExType] | ExVariant (ExtRow ExType) | ExRecord (Row ExType) | OpaqueTy
    deriving (Show)

newtype ConMetadata
    = ConMetadata
        (forall es. (UniEffs es, Reader TopLevel :> es, Diagnose :> es, NameGen :> es) => Context -> Eff es (VType, ConArgList))

getConMetadata
    :: forall es
     . (UniEffs es, Reader TopLevel :> es, Diagnose :> es, NameGen :> es)
    => ConMetadata
    -> Context
    -> Eff es (VType, ConArgList)
getConMetadata (ConMetadata f) = f

type UniEffs es = (State UniVars :> es, Labeled UniVar NameGen :> es, State Postponings :> es, Labeled Postponed NameGen :> es)

data ConArgList
    = UnusedInType {vis :: Visibility, name :: SimpleName_, ty :: VType, mkRest :: Value -> ConArgList}
    | UsedInType {vis :: Visibility, name :: SimpleName_, ty :: VType, unifyWith :: Value, rest :: ConArgList}
    | FinalType VType

pattern Arg :: Visibility -> SimpleName_ -> VType -> ConArgList
pattern Arg{vis, name, ty} <- (getArg -> Just (vis, name, ty))

{-# COMPLETE Arg, FinalType #-}

getArg :: ConArgList -> Maybe (Visibility, SimpleName_, VType)
getArg = \case
    UnusedInType{vis, name, ty} -> Just (vis, name, ty)
    UsedInType{vis, name, ty} -> Just (vis, name, ty)
    FinalType{} -> Nothing

type ConMetaTable = IdMap Name_ ConMetadata

-- | types of top-level bindings
type TopLevel = IdMap Name_ VType

data Context = Context
    { env :: ValueEnv
    , localEquality :: EnumMap Level Value
    , level :: Level
    , locals :: Locals
    , pruning :: Pruning -- a mask that's used for fresh univars
    , types :: IdMap Name_ (Level, VType)
    }

data Locals
    = None
    | Bind Name_ ~CoreType Locals
    | Define Name_ ~CoreType ~CoreTerm Locals

emptyContext :: ValueEnv -> Context
emptyContext env =
    Context
        { env
        , localEquality = EMap.empty
        , level = Level 0
        , types = Map.empty
        , locals = None
        , pruning = Pruning []
        }

prettyCoreCtx :: Context -> CoreTerm -> Doc AnsiStyle
prettyCoreCtx ctx = C.prettyEnvDef (namesOfLocals ctx.locals)
  where
    namesOfLocals = \case
        None -> []
        Bind name _ rest -> name : namesOfLocals rest
        Define name _ _ rest -> name : namesOfLocals rest

prettyValCtx :: Context -> Value -> Doc AnsiStyle
prettyValCtx ctx = prettyCoreCtx ctx . quoteWhnf EMap.empty ctx.level

type TC es =
    (UniEffs es, NameGen :> es, Diagnose :> es, Trace :> es, Reader TopLevel :> es, Reader ConMetaTable :> es)

run
    :: TopLevel
    -> ConMetaTable
    -> Eff
        ( State Postponings
            : Labeled Postponed NameGen
            : State UniVars
            : Labeled UniVar NameGen
            : Reader TopLevel
            : Reader ConMetaTable
            : es
        )
        a
    -> Eff es a
run types conMeta = runReader conMeta . runReader types . runUniEffs

runUniEffs :: Eff (State Postponings : Labeled Postponed NameGen : State UniVars : Labeled UniVar NameGen : es) a -> Eff es a
runUniEffs = runLabeled runNameGen . evalState EMap.empty . runLabeled runNameGen . evalState EMap.empty

-- | insert a new UniVar applied to all bound variables in scope
freshUniVar :: UniEffs es => Context -> VType -> Eff es CoreTerm
freshUniVar ctx vty = do
    env <- extendEnv ctx.env
    let fullType = evalCore env $ closeType ctx.locals (quote env.univars ctx.level vty)
    uni <- newUniVar fullType
    pure $ C.AppPruning (C.UniVar uni) ctx.pruning

newUniVar :: UniEffs es => VType -> Eff es UniVar
newUniVar ty = do
    uni <- Common.UniVar <$> labeled @UniVar freshId
    modify $ EMap.insert uni Unsolved{blocks = ESet.empty, ty}
    pure uni

readUnsolvedUniVar :: (Diagnose :> es, State UniVars :> es) => UniVar -> Eff es (EnumSet Postponed, VType)
readUnsolvedUniVar uni =
    gets (EMap.lookup uni) >>= \case
        Just Unsolved{blocks, ty} -> pure (blocks, ty)
        Just Solved{} -> internalError' "expected the univar to be unsolved"
        Nothing -> internalError' "out of scope univar"

typeOfUniVar :: (Diagnose :> es, State UniVars :> es) => UniVar -> Eff es VType
typeOfUniVar uni =
    gets (EMap.lookup uni) >>= \case
        Just Unsolved{ty} -> pure ty
        Just Solved{ty} -> pure ty
        Nothing -> internalError' "out of scope univar"

-- | convert a list of local bindings to a top-level Pi type
closeType :: Locals -> CoreType -> CoreType
closeType locals body = case locals of
    None -> body
    Bind x ty rest -> closeType rest (C.Q Forall Visible Retained (toSimpleName_ x) ty body)
    Define x val _ty rest -> closeType rest (C.Let (toSimpleName_ x) val body)

freshUniVarV :: (UniEffs es) => Context -> VType -> Eff es Value
freshUniVarV ctx vty = do
    uniTerm <- freshUniVar ctx vty
    univars <- get
    let V.ValueEnv{..} = ctx.env
        env = ExtendedEnv{..}
    pure $ evalCore env uniTerm

freshUniVarS :: (UniEffs es) => Context -> VType -> Eff es V.Stuck
freshUniVarS ctx vty = do
    uni <- freshUniVarV ctx vty
    pure case uni of
        V.Stuck stuck -> stuck
        _ -> error "fresh univar didn't evaluate to a Stuck value"

-- | extend the value environment with current UniVar state for pure evaluation
extendEnv :: State UniVars :> es => ValueEnv -> Eff es ExtendedEnv
extendEnv V.ValueEnv{..} = do
    univars <- get
    pure ExtendedEnv{..}

bind :: UniVars -> Name_ -> VType -> Context -> Context
bind univars name ty Context{env = V.ValueEnv{locals = vlocals, ..}, ..} =
    Context
        { level = succ level
        , env = V.ValueEnv{locals = V.Var level : vlocals, ..}
        , types = Map.insert name (level, ty) types
        , locals = Bind name (quote univars level ty) locals
        , pruning = Pruning (Just Visible : pruning.getPruning) -- 'bind' should probably take a visibility argument
        , ..
        }

{- | bind a list of new vars, where the first var in the list is the most recently bound
e. g. `Cons x xs` --> `[xs, x]`
-}
bindMany :: UniVars -> [(Name_, VType)] -> Context -> Context
bindMany univars newLocals ctx = foldr (uncurry $ bind univars) ctx newLocals

define :: Name_ -> CoreTerm -> Value -> CoreType -> VType -> Context -> Context
define name val vval ty vty Context{env = V.ValueEnv{locals = vlocals, ..}, ..} =
    Context
        { level = succ level
        , env = V.ValueEnv{locals = vval : vlocals, ..}
        , types = Map.insert name (level, vty) types
        , locals = Define name ty val locals
        , pruning = Pruning (Nothing : pruning.getPruning)
        , ..
        }

lookupSig :: (Reader TopLevel :> es, UniEffs es) => Name -> Context -> Eff es (ETerm, VType)
lookupSig name ctx = do
    topLevel <- ask
    case (Map.lookup (unLoc name) ctx.types, Map.lookup (unLoc name) topLevel) of
        (Just (lvl, ty), _) -> pure (E.Var (levelToIndex ctx.level lvl), ty)
        (_, Just ty) -> pure (E.Name $ unLoc name, ty)
        (Nothing, Nothing) -> do
            ty <- freshUniVarV ctx (V.Type TypeName)
            (E.Name $ unLoc name,) <$> freshUniVarV ctx ty

-- | collect all free vars in a zonked CoreTerm
freeVarsInCore :: UniVars -> CoreTerm -> Eff (State (EnumSet UniVar) : es) ()
freeVarsInCore univars = void . go
  where
    go = \case
        C.UniVar uni -> case EMap.lookup uni univars of
            Just Unsolved{ty} -> do
                let tyC = quote univars (Level 0) ty
                unlessM (gets (ESet.member uni)) do
                    modify $ ESet.insert uni
                    void $ go tyC
                pure $ C.UniVar uni
            Just Solved{} -> error "freeVarsInCore: unexpected solved univar"
            Nothing -> error "freeVarsInCore: out of scope univar"
        other -> C.coreTraversal go other
