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
import Eval (ExtendedEnv (..), UniVarState (..), UniVars, evalCore, quote, quoteM, whnf)
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

removeUniVars :: TC es => Context -> VType -> Eff es VType
removeUniVars ctx ty = snd <$> removeUniVars' ctx (Nothing, ty)

removeUniVarsT :: TC es => Context -> (ETerm, VType) -> Eff es (ETerm, VType)
removeUniVarsT ctx (term, ty) = first runIdentity <$> removeUniVars' ctx (Identity term, ty)

-- zonk unification variables from a term and its type,
-- generalise unsolved variables to new forall binders
removeUniVars' :: (TC es, Traversable t) => Context -> (t ETerm, VType) -> Eff es (t ETerm, VType)
removeUniVars' ctx (mbTerm, ty) = do
    env <- extendEnv ctx.env
    -- quote forces a term to normal form and applies all solved univars
    -- quoteWhnf would also work here, I'm not sure which one is better in this case
    ty <- evalCore env <$> quoteM ctx.level ty
    mbTerm <- traverse (zonkTerm (ctx.level, ctx.env)) mbTerm
    pure (mbTerm, ty)
  where
    -- the only important case is E.Core, which may actually contain univars
    -- the rest are just plain traversal logic
    zonkTerm :: TC es => (Level, ValueEnv) -> ETerm -> Eff es ETerm
    zonkTerm c@(lvl, env@V.ValueEnv{..}) = \case
        E.Core coreTerm -> do
            env <- extendEnv env
            pure $ E.Core $ whnf lvl env coreTerm
        E.App vis lhs rhs -> E.App vis <$> zonkTerm c lhs <*> zonkTerm c rhs
        E.Lambda vis pat body -> do
            let env = V.ValueEnv{locals = freeVars <> locals, ..}
                freeVars = V.Var <$> [pred newLevel, pred (pred newLevel) .. lvl]
                newLevel = Level $ lvl.getLevel + E.patternArity pat
            E.Lambda vis pat <$> zonkTerm (newLevel, env) body
        E.Let{} -> internalError' "zonkTerm: let bindings are not supported yet"
        E.LetRec{} -> internalError' "zonkTerm: let rec bindings are not supported yet"
        E.Case arg branches -> E.Case <$> zonkTerm c arg <*> traverse zonkBranch branches
          where
            zonkBranch (pat, body) = do
                let env = V.ValueEnv{locals = freeVars <> locals, ..}
                    freeVars = V.Var <$> [pred newLevel, pred (pred newLevel) .. lvl]
                    newLevel = Level $ lvl.getLevel + E.patternArity pat
                (pat,) <$> zonkTerm (newLevel, env) body
        E.Match{} -> internalError' "zonkTerm: match not supported yet"
        E.If cond true false -> E.If <$> zonkTerm c cond <*> zonkTerm c true <*> zonkTerm c false
        E.Record row -> E.Record <$> traverse (zonkTerm c) row
        E.RecordT row -> E.RecordT <$> traverse (zonkTerm c) row
        E.VariantT row -> E.VariantT <$> traverse (zonkTerm c) row
        E.RecordAccess term field -> E.RecordAccess <$> zonkTerm c term <*> pure field
        E.List ty items -> E.List <$> zonkTerm c ty <*> traverse (zonkTerm c) items
        E.Sigma lhs rhs -> E.Sigma <$> zonkTerm c lhs <*> zonkTerm c rhs
        E.Do{} -> internalError' "zonkTerm: do notation not supported yet"
        E.Q q v e (var ::: ty) body -> do
            ty <- zonkTerm c ty
            E.Q q v e (var ::: ty) <$> zonkTerm (succ lvl, V.ValueEnv{locals = V.Var lvl : locals, ..}) body
        v@E.Var{} -> pure v
        n@E.Name{} -> pure n
        v@E.Variant{} -> pure v
        l@E.Literal{} -> pure l
