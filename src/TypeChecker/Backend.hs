{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE NoFieldSelectors #-}

module TypeChecker.Backend where

import Common
import Data.EnumMap.Strict qualified as EMap
import Data.EnumSet qualified as ESet
import Data.IdMap qualified as Map
import Data.Poset qualified as Poset
import Data.Row
import Diagnostic (Diagnose, internalError')
import Effectful.Error.Static (runErrorNoCallStack)
import Effectful.Labeled (Labeled, labeled, runLabeled)
import Effectful.Reader.Static
import Effectful.State.Static.Local
import Effectful.Writer.Static.Local (Writer, runWriter, tell)
import Eval (ExtendedEnv (..), UniVarState (..), UniVars, evalCore, nf, quote, quoteM)
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

generalise :: TC es => Context -> VType -> Eff es VType
generalise ctx ty = snd <$> generalise' ctx Nothing (Nothing, ty)

generaliseTerm :: TC es => Context -> (ETerm, VType) -> Eff es (ETerm, VType)
generaliseTerm ctx (term, ty) = first runIdentity <$> generalise' ctx Nothing (Identity term, ty)

generaliseRecursiveTerm :: TC es => Context -> Name -> (ETerm, VType) -> Eff es (ETerm, VType)
generaliseRecursiveTerm ctx name (term, ty) = first runIdentity <$> generalise' ctx (Just name) (Identity term, ty)

-- | zonk unification variables from a term, report an error on leftover free variables
zonkTerm :: TC es => Context -> ETerm -> Eff es ETerm
zonkTerm ctx term = do
    (term, freeVars) <- runWriter @(EnumSet UniVar) $ zonkTerm' (ctx.level, ctx.env) term

    -- todo: this reports only the first variable
    -- also, I need a proper type error for this case
    for_ (ESet.toList freeVars) \freeUni -> do
        internalError' $ "ambiguous unification variable" <+> pretty freeUni
    pure term

{- | zonk unification variables from a term and its type,
generalise unsolved variables to new forall binders
-}
generalise' :: (TC es, Traversable t) => Context -> Maybe Name -> (t ETerm, VType) -> Eff es (t ETerm, VType)
generalise' ctx mbName (mbTerm, ty) = do
    -- quote forces a term to normal form and applies all solved univars
    -- quoteWhnf would also work here, I'm not sure which one is better in this case
    tyC <- quoteM ctx.level ty
    (mbTerm, freeVarsInTerm) <- runWriter @(EnumSet UniVar) $ traverse (zonkTerm' (ctx.level, ctx.env)) mbTerm
    univars <- get
    let freeVars = freeVarsInCore univars tyC <> freeVarsInTerm

    -- we collect a list of dependencies for each univar
    unisWithDependencies <- for (ESet.toList freeVars) \uni -> do
        uniType <- quoteM (Level 0) =<< typeOfUnsolvedUniVar uni
        pure (uni, ESet.toList $ freeVarsInCore univars uniType)
    let addDeps poset (uni, uniDeps) = foldlM (\p dep -> Poset.addRelationStrict uni dep GT p) poset uniDeps
    let mkUniPoset =
            Poset.reportError $
                concat . Poset.ordered <$> foldlM addDeps (Poset.fromList (map fst unisWithDependencies)) unisWithDependencies

    -- and sort them wrt. dependencies
    sortedUnis <-
        runErrorNoCallStack @(Poset.Cycle UniVar) mkUniPoset >>= \case
            Left{} -> internalError' "univar types are cyclic"
            Right uniPoset -> pure uniPoset

    let solveToLvl i uni = do
            ty <- typeOfUnsolvedUniVar uni
            let newLevel = ctx.level `incLevel` i
            modify @UniVars $ EMap.insert uni $ Solved{solution = V.Var newLevel, ty}

    -- DANGER: this step wouldn't work when I implement destructuring bindings
    -- solving univars like this makes sense only if this binding and its type are the only things that referred to them
    zipWithM_ solveToLvl [0 ..] sortedUnis

    let newBinderCount = length sortedUnis
        (newLocals, newLevel) = liftLevel ctx.level newBinderCount
        innerEnv = ctx.env{V.locals = newLocals <> ctx.env.locals}

    innerType <- do
        env <- extendEnv innerEnv
        pure $ nf newLevel env $ C.lift newBinderCount tyC
    (innerTerm, stillFree) <- runWriter $ traverse (zonkTerm' (newLevel, innerEnv) . E.lift newBinderCount) mbTerm

    univars <- get
    unless (ESet.null $ stillFree <> freeVarsInCore univars innerType) do
        internalError' "zonking didn't remove all univars"

    let mkName i = one $ chr (ord 'a' + i `mod` 26)
    newNames <- for (zip [0 ..] sortedUnis) \(i, uni) -> do
        uniType <- quote univars (ctx.level `incLevel` i) <$> typeOfUniVar uni
        pure (Name' (mkName i), uniType)

    let finalType = foldr (uncurry (C.Q Forall Implicit Retained)) innerType newNames
        wrapInLambdas body = foldr (\(name, _) -> E.Lambda Implicit (E.VarP name)) body newNames
        withApps lvl name =
            foldl' (\acc vlvl -> C.App Implicit acc (C.Var $ levelToIndex lvl vlvl)) (C.Name name) [Level 0 .. pred (Level newBinderCount)]

    -- after generalisation, the recursive calls to the same binding are
    -- no longer well-typed - they are missing implicit applications
    let withFixedCalls = case mbName of
            Nothing -> id
            Just name -> replaceRecursiveCalls name (`withApps` name) (Level newBinderCount)

    env <- extendEnv ctx.env
    pure (wrapInLambdas . withFixedCalls <$> innerTerm, evalCore env finalType)
  where
    replaceRecursiveCalls fnName fixTerm lvl = \case
        E.Name name | name == fnName -> E.Core (fixTerm lvl)
        other -> E.elabTraversalPureWithLevel (replaceRecursiveCalls fnName fixTerm) (replaceRecursiveCallsCore fnName fixTerm) lvl other
    replaceRecursiveCallsCore fnName fixTerm lvl = \case
        C.Name name | name == fnName -> fixTerm lvl
        other -> C.coreTraversalPureWithLevel (replaceRecursiveCallsCore fnName fixTerm) lvl other

-- | collect all free vars in a zonked CoreTerm
freeVarsInCore :: UniVars -> CoreTerm -> EnumSet UniVar
freeVarsInCore univars = \case
    C.UniVar uni -> case EMap.lookup uni univars of
        Just Unsolved{ty} ->
            let tyC = quote univars (Level 0) ty
             in ESet.singleton uni <> freeVarsInCore univars tyC
        Just Solved{} -> error "freeVarsInCore: unexpected solved univar"
        Nothing -> error "freeVarsInCore: out of scope univar"
    other -> getConst $ C.coreTraversal (Const . freeVarsInCore univars) other

-- the only important case is E.Core, which may actually contain univars
-- the rest are just plain traversal logic
-- unfortunately, it doesn't quite fit 'elabTraversal', since the env logic is unique
zonkTerm' :: TC es => (Level, ValueEnv) -> ETerm -> Eff (Writer (EnumSet UniVar) : es) ETerm
zonkTerm' c@(lvl, env@V.ValueEnv{..}) = \case
    E.Core coreTerm -> do
        env <- extendEnv env
        let zonkedCore = nf lvl env coreTerm
        univars <- get
        tell $ freeVarsInCore univars zonkedCore
        pure $ E.Core zonkedCore
    E.App vis lhs rhs -> E.App vis <$> zonkTerm' c lhs <*> zonkTerm' c rhs
    E.Lambda vis pat body -> do
        let env = V.ValueEnv{locals = freeVars <> locals, ..}
            (freeVars, newLevel) = liftLevel lvl (E.patternArity pat)
        E.Lambda vis pat <$> zonkTerm' (newLevel, env) body
    E.Let{} -> internalError' "zonkTerm': let bindings are not supported yet"
    E.LetRec{} -> internalError' "zonkTerm': let rec bindings are not supported yet"
    E.Case arg branches -> E.Case <$> zonkTerm' c arg <*> traverse zonkBranch branches
      where
        zonkBranch (pat, body) =
            let env = V.ValueEnv{locals = freeVars <> locals, ..}
                (freeVars, newLevel) = liftLevel lvl (E.patternArity pat)
             in (pat,) <$> zonkTerm' (newLevel, env) body
    E.Match branches -> E.Match <$> traverse zonkBranch branches
      where
        zonkBranch (pats, body) =
            let env = V.ValueEnv{locals = freeVars <> locals, ..}
                (freeVars, newLevel) = liftLevel lvl (sum (fmap (E.patternArity . E.unTyped) pats))
             in (pats,) <$> zonkTerm' (newLevel, env) body
    E.If cond true false -> E.If <$> zonkTerm' c cond <*> zonkTerm' c true <*> zonkTerm' c false
    E.Record row -> E.Record <$> traverse (zonkTerm' c) row
    E.RecordT row -> E.RecordT <$> traverse (zonkTerm' c) row
    E.VariantT row -> E.VariantT <$> traverse (zonkTerm' c) row
    E.RecordAccess term field -> E.RecordAccess <$> zonkTerm' c term <*> pure field
    E.List ty items -> E.List <$> zonkTerm' c ty <*> traverse (zonkTerm' c) items
    E.Sigma lhs rhs -> E.Sigma <$> zonkTerm' c lhs <*> zonkTerm' c rhs
    E.Do{} -> internalError' "zonkTerm: do notation not supported yet"
    E.Q q v e (var ::: ty) body -> do
        ty <- zonkTerm' c ty
        E.Q q v e (var ::: ty) <$> zonkTerm' (succ lvl, V.ValueEnv{locals = V.Var lvl : locals, ..}) body
    v@E.Var{} -> pure v
    n@E.Name{} -> pure n
    v@E.Variant{} -> pure v
    l@E.Literal{} -> pure l

liftLevel :: Level -> Int -> ([Value], Level)
liftLevel lvl diff = (freeVars, newLevel)
  where
    freeVars = V.Var <$> [pred newLevel, pred (pred newLevel) .. lvl]
    newLevel = lvl `incLevel` diff
