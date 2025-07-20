{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE NoFieldSelectors #-}

module TypeChecker.Backend where

import Common
import Data.EnumMap.Strict qualified as EMap
import Data.IdMap qualified as Map
import Data.Row
import Diagnostic (Diagnose, internalError')
import Effectful.Labeled (Labeled, labeled, runLabeled)
import Effectful.Reader.Static
import Effectful.State.Static.Local
import Eval (ExtendedEnv (..), UniVarState (..), UniVars, appM, evalCore, forceM, quote)
import LangPrelude
import NameGen (NameGen, freshId, runNameGen)
import Syntax
import Syntax.Core qualified as C
import Syntax.Elaborated qualified as E
import Syntax.Value qualified as V

newtype ConstructorTable = ConstructorTable
    { table :: IdMap Name_ (IdMap Name_ ([ExType] -> [ExType]))
    }
data ExType = TyCon Name_ [ExType] | ExVariant (ExtRow ExType) | ExRecord (Row ExType) | OpaqueTy
    deriving (Show)

-- | types of top-level bindings
type TopLevel = IdMap Name_ VType

data Context = Context
    { env :: ValueEnv
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
        , level = Level 0
        , types = Map.empty
        , locals = None
        , pruning = Pruning []
        }

type TC es = (Labeled UniVar NameGen :> es, NameGen :> es, Diagnose :> es, State UniVars :> es, Reader TopLevel :> es)

run :: TopLevel -> Eff (State UniVars : Reader TopLevel : Labeled UniVar NameGen : es) a -> Eff es a
run types = runLabeled @UniVar runNameGen . runReader types . evalState @UniVars EMap.empty

-- | insert a new UniVar applied to all bound variables in scope
freshUniVar :: (Labeled UniVar NameGen :> es, State UniVars :> es) => Context -> VType -> Eff es CoreTerm
freshUniVar ctx vty = do
    env <- extendEnv ctx.env
    let fullType = evalCore env $ closeType ctx.locals (quote env.univars ctx.level vty)
    uni <- newUniVar fullType
    pure $ C.AppPruning (C.UniVar uni) ctx.pruning

newUniVar :: (Labeled UniVar NameGen :> es, State UniVars :> es) => VType -> Eff es UniVar
newUniVar ty = do
    uni <- Common.UniVar <$> labeled @UniVar @NameGen freshId
    modify @UniVars $ EMap.insert uni Unsolved{ty}
    pure uni

typeOfUnsolvedUniVar :: (Diagnose :> es, State UniVars :> es) => UniVar -> Eff es VType
typeOfUnsolvedUniVar uni =
    gets (EMap.lookup uni) >>= \case
        Just Unsolved{ty} -> pure ty
        Just Solved{} -> internalError' "expected the univar to be unsolved"
        Nothing -> internalError' "out of scope univar"

-- | convert a list of local bindings to a top-level Pi type
closeType :: Locals -> CoreType -> CoreType
closeType locals body = case locals of
    None -> body
    Bind x ty rest -> closeType rest (C.Q Forall Visible Retained (toSimpleName_ x) ty body)
    Define x val _ty rest -> closeType rest (C.Let (toSimpleName_ x) val body)

freshUniVarV :: (Labeled UniVar NameGen :> es, State UniVars :> es) => Context -> VType -> Eff es Value
freshUniVarV ctx vty = do
    uniTerm <- freshUniVar ctx vty
    univars <- get @UniVars
    let V.ValueEnv{..} = ctx.env
        env = ExtendedEnv{..}
    pure $ evalCore env uniTerm

-- | extend the value environment with current UniVar state for pure evaluation
extendEnv :: State UniVars :> es => ValueEnv -> Eff es ExtendedEnv
extendEnv V.ValueEnv{..} = do
    univars <- get @UniVars
    pure ExtendedEnv{..}

bind :: UniVars -> Name_ -> VType -> Context -> Context
bind univars name ty Context{env = V.ValueEnv{locals = vlocals, ..}, ..} =
    Context
        { level = succ level
        , env = V.ValueEnv{locals = V.Var level : vlocals, ..}
        , types = Map.insert name (level, ty) types
        , locals = Bind name (quote univars level ty) locals
        , pruning = Pruning (Just Visible : pruning.getPruning) -- 'bind' should probably take a visibility argument
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
        }

lookupSig :: TC es => Name -> Context -> Eff es (ETerm, VType)
lookupSig name ctx = do
    topLevel <- ask @TopLevel
    case (Map.lookup (unLoc name) ctx.types, Map.lookup (unLoc name) topLevel) of
        (Just (lvl, ty), _) -> pure (E.Var (levelToIndex ctx.level lvl), ty)
        (_, Just ty) -> pure (E.Name name, ty)
        (Nothing, Nothing) -> do
            ty <- freshUniVarV ctx (V.Type $ TypeName :@ getLoc name)
            (E.Name name,) <$> freshUniVarV ctx ty

-- internalError' $ pretty name <+> "not in scope"

{- | replace solved univars with their solutions and unsolved univars with a placeholder type
in the future, unsolved unis should get converted to a forall with the appropriate type
-}
removeUniVars :: TC es => Level -> Value -> Eff es Value
removeUniVars lvl = go
  where
    go =
        forceM >=> \case
            V.TyCon name args -> V.TyCon name <$> (traverse . traverse) go args
            V.Con name args -> V.Con name <$> (traverse . traverse) go args
            V.Lambda vis closure@V.Closure{var, env} -> do
                newBody <- removeUniVars (succ lvl) =<< closure `appM` V.Var lvl
                univars <- get @UniVars
                pure $ V.Lambda vis V.Closure{var, ty = (), env, body = quote univars (succ lvl) newBody}
            V.PrimFunction fn -> do
                captured <- traverse go fn.captured
                pure $ V.PrimFunction fn{V.captured}
            V.Record row -> V.Record <$> traverse go row
            V.Variant name arg -> V.Variant name <$> go arg
            V.Sigma lhs rhs -> V.Sigma <$> go lhs <*> go rhs
            V.PrimValue lit -> pure $ V.PrimValue lit
            V.Q q v e closure@V.Closure{var, env} -> do
                ty <- go closure.ty
                newBody <- removeUniVars (succ lvl) =<< closure `appM` V.Var lvl
                univars <- get @UniVars
                pure $ V.Q q v e V.Closure{var, ty, env, body = quote univars (succ lvl) newBody}
            V.RecordT row -> V.RecordT <$> traverse go row
            V.VariantT row -> V.VariantT <$> traverse go row
            V.Stuck stuck -> V.Stuck <$> goStuck stuck
    goStuck = \case
        V.VarApp vlvl spine -> V.VarApp vlvl <$> (traverse . traverse) go spine
        -- if we reach this case, it means the univar is still unsolved
        -- in the future, we will collect all unsolved unis and convert them to
        -- a forall clause
        uniApp@V.UniVarApp{} -> pure uniApp
        V.Fn fn arg -> do
            captured <- traverse go fn.captured
            V.Fn fn{V.captured} <$> goStuck arg
        V.Case _arg _matches -> internalError' "todo: remove univars from stuck case" -- V.Case <$> goStuck arg <*> _ matches

{- | remove left-over univars from an eterm
todo: write a traversal for ETerm
-}
removeUniVarsT :: TC es => Level -> ETerm -> Eff es ETerm
removeUniVarsT lvl = go
  where
    go = \case
        E.Var ix -> pure $ E.Var ix
        E.Name name -> pure $ E.Name name
        E.Literal lit -> pure $ E.Literal lit
        E.App vis lhs rhs -> E.App vis <$> go lhs <*> go rhs
        E.Lambda vis (E.VarP name) body -> do
            body' <- removeUniVarsT (succ lvl) body
            pure $ E.Lambda vis (E.VarP name) body'
        E.Lambda{} -> internalError' "non-trivial patterns are not supported yet"
        E.Let (E.ValueB name defn) body -> do
            defn' <- go defn
            body' <- removeUniVarsT (succ lvl) body
            pure $ E.Let (E.ValueB name defn') body'
        E.Let{} -> internalError' "non-trivial let not supported yet"
        E.LetRec{} -> internalError' "letrec not supported yet"
        E.Case arg branches -> E.Case <$> go arg <*> traverse goBranch branches
        E.Match{} -> internalError' "match not supported yet"
        E.If cond true false -> E.If <$> go cond <*> go true <*> go false
        E.Variant name -> pure $ E.Variant name
        E.Record row -> E.Record <$> traverse go row
        E.RecordAccess record field -> E.RecordAccess <$> go record <*> pure field
        E.List ty items -> E.List <$> go ty <*> traverse go items
        E.Sigma lhs rhs -> E.Sigma <$> go lhs <*> go rhs
        E.Do{} -> internalError' "do not supported yet"
        E.Q q v e (var ::: ty) body -> do
            ty' <- go ty
            body' <- removeUniVarsT (succ lvl) body
            pure $ E.Q q v e (var ::: ty') body'
        E.VariantT row -> E.VariantT <$> traverse go row
        E.RecordT row -> E.RecordT <$> traverse go row
        E.Core coreTerm -> do
            univars <- get
            let val = evalCore ExtendedEnv{univars, locals = [], topLevel = Map.empty} coreTerm
            val <- removeUniVars lvl val
            pure (E.Core $ quote univars lvl val)
    goBranch (pat, body) = do
        (pat,) <$> removeUniVarsT (Level $ lvl.getLevel + E.patternArity pat) body
