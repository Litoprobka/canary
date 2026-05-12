{-# LANGUAGE RecordWildCards #-}

module TypeChecker.Generalisation where

import Common
import Data.EnumMap.Strict qualified as EMap
import Data.EnumSet qualified as ESet
import Data.Poset qualified as Poset
import Diagnostic (internalError')
import Effectful.Error.Static (runErrorNoCallStack)
import Effectful.State.Static.Local
import Eval (PostponedEntry (..), Postponings, UniVarState (..), eval, nf, quote, quoteM)
import LangPrelude
import Prettyprinter (sep)
import Syntax
import Syntax.Core qualified as C
import Syntax.Value qualified as V
import Trace (trace, traceScope_)
import TypeChecker.Backend
import TypeChecker.Unification

generalise :: TC es => Context -> VType -> Eff es VType
generalise ctx ty = snd <$> generalise' ctx Nothing (Nothing, ty)

generaliseTerm :: TC es => Context -> (CoreTerm, VType) -> Eff es (CoreTerm, VType)
generaliseTerm ctx (term, ty) = first runIdentity <$> generalise' ctx Nothing (Identity term, ty)

generaliseRecursiveTerm :: TC es => Context -> Name_ -> (CoreTerm, VType) -> Eff es (CoreTerm, VType)
generaliseRecursiveTerm ctx name (term, ty) = first runIdentity <$> generalise' ctx (Just name) (Identity term, ty)

-- | zonk unification variables from a term, report an error on leftover free variables
zonkTerm :: TC es => Context -> CoreTerm -> Eff es CoreTerm
zonkTerm ctx term = do
    forceSolvePostponed ctx

    (term, freeVars) <- runState ESet.empty $ zonkTerm' (ctx.level, ctx.env) term

    -- todo: this reports only the first variable
    -- also, I need a proper type error for this case
    for_ (ESet.toList freeVars) \freeUni -> do
        internalError' $ "ambiguous unification variable" <+> pretty freeUni
    pure term

forceSolvePostponed :: TC es => Context -> Eff es ()
forceSolvePostponed ctx = do
    postponings <- get
    trace $ "still blocked:" <+> pretty (EMap.size postponings)
    for_ postponings \(PostponedEntry lvl lhs rhs) -> forceUnify ctx lvl lhs rhs
    put @Postponings EMap.empty

{- | zonk unification variables from a term and its type,
generalise unsolved variables to new forall binders
-}
generalise' :: (TC es, Traversable t) => Context -> Maybe Name_ -> (t CoreTerm, VType) -> Eff es (t CoreTerm, VType)
generalise' ctx mbName (mbTerm, ty) = traceScope_ (specSymBlue "generalise" <+> prettyDef mbName) do
    -- first, we retry all postponed constraints once again
    forceSolvePostponed ctx

    -- quote forces a term to normal form and applies all solved univars
    -- quoteWhnf would also work here, I'm not sure which one is better in this case
    tyC <- quoteM ctx.level ty
    (mbTerm, freeVarsInTerm) <- runState ESet.empty $ traverse (zonkTerm' (ctx.level, ctx.env)) mbTerm
    univars <- get
    freeVars <- execState freeVarsInTerm $ freeVarsInCore univars tyC
    trace $ "to generalise:" <+> sep (map prettyDef $ ESet.toList freeVars)

    -- we collect a list of dependencies for each univar
    unisWithDependencies <- for (ESet.toList freeVars) \uni -> do
        uniType <- quoteM (Level 0) . snd =<< readUnsolvedUniVar uni
        (uni,) . ESet.toList <$> execState ESet.empty (freeVarsInCore univars uniType)
    let addDeps poset (uni, uniDeps) = foldlM (\p dep -> Poset.addRelationStrict uni dep GT p) poset uniDeps
    let mkUniPoset =
            Poset.reportError $
                concat . Poset.ordered <$> foldlM addDeps (Poset.fromList (map fst unisWithDependencies)) unisWithDependencies

    -- and sort them wrt. dependencies
    sortedUnis <-
        runErrorNoCallStack mkUniPoset >>= \case
            Left{} -> internalError' "univar types are cyclic"
            Right uniPoset -> pure uniPoset

    let solveToLvl i uni = do
            (_, ty) <- readUnsolvedUniVar uni
            let newLevel = ctx.level `incLevel` i
            modify $ EMap.insert uni $ Solved{solution = V.Var newLevel, ty}

    -- DANGER: this step wouldn't work when I implement destructuring bindings and mutually recursive binding groups
    -- solving univars like this makes sense only if this binding and its type are the only things that referred to them
    zipWithM_ solveToLvl [0 ..] sortedUnis

    let newBinderCount = length sortedUnis
        (newLocals, newLevel) = liftLevel ctx.level newBinderCount
        innerEnv = ctx.env{V.locals = newLocals <> ctx.env.locals}

    innerType <- do
        env <- extendEnv innerEnv
        pure $ nf newLevel env $ C.lift newBinderCount tyC

    univars <- get
    (innerTerm, freeVars) <- runState ESet.empty do
        innerTerm <- traverse (zonkTerm' (newLevel, innerEnv) . C.lift newBinderCount) mbTerm
        freeVarsInCore univars innerType
        pure innerTerm

    unless (ESet.null freeVars) do
        internalError' "zonking didn't remove all univars"

    let mkName i = one $ chr (ord 'a' + i `mod` 26)
    newNames <- for (zip [0 ..] sortedUnis) \(i, uni) -> do
        uniType <- quote univars (ctx.level `incLevel` i) <$> typeOfUniVar uni
        pure (Name' (mkName i), uniType)

    let finalType = foldr (uncurry (C.Q Forall Implicit Retained)) innerType newNames
        wrapInLambdas body = foldr (uncurry (C.Lambda Implicit)) body newNames
        withApps lvl name =
            foldl' (\acc vlvl -> C.App Implicit acc (C.Var $ levelToIndex lvl vlvl)) (C.Name name) [Level 0 .. pred (Level newBinderCount)]

    -- after generalisation, the recursive calls to the same binding are
    -- no longer well-typed - they are missing implicit applications
    let withFixedCalls = case mbName of
            Nothing -> id
            Just name -> replaceRecursiveCalls name (`withApps` name) (Level newBinderCount)

    env <- extendEnv ctx.env
    pure (wrapInLambdas . withFixedCalls <$> innerTerm, eval env finalType)
  where
    -- this function is applied after zonking, so ElabInsert should not matter here anymore
    replaceRecursiveCalls fnName fixTerm lvl = \case
        C.Name name | name == fnName -> fixTerm lvl
        other -> C.coreTraversalPureWithLevel (replaceRecursiveCalls fnName fixTerm) lvl other

-- the only important case is C.ElabInsert, which may actually contain univars
-- the rest are just plain traversal logic
-- unfortunately, it doesn't quite fit 'coreTraversal', since the env logic is unique
zonkTerm' :: TC es => (Level, ValueEnv) -> CoreTerm -> Eff (State (EnumSet UniVar) : es) CoreTerm
zonkTerm' c@(lvl, env@V.ValueEnv{..}) = \case
    C.ElabInsert coreTerm -> do
        env <- extendEnv env
        let zonkedCore = nf lvl env coreTerm
        univars <- get
        freeVarsInCore univars zonkedCore
        pure $ C.ElabInsert zonkedCore
    C.TyCon name args -> C.TyCon name <$> traverse (bitraverse pure $ zonkTerm' c) args
    C.Con name args -> C.Con name <$> traverse (bitraverse pure $ zonkTerm' c) args
    C.App vis lhs rhs -> C.App vis <$> zonkTerm' c lhs <*> zonkTerm' c rhs
    -- wrapping argument types in ElabInsert is a bit of a crutch, but we generally want types in nf
    -- the main reason this crutch is required is lambdas produced by the `match` desugar.
    -- When inferring the type of a match, we produce a multi-arg function type, which is used to construct a lambda later on
    -- the function type then gets normalized, so we can't it in C.ElabInsert before that point
    C.Lambda{vis, argName, argType, body} ->
        let newEnv = V.ValueEnv{locals = V.Var lvl : locals, ..}
         in C.Lambda vis argName <$> zonkTerm' (lvl, env) (C.ElabInsert argType) <*> zonkTerm' (succ lvl, newEnv) body
    C.Let name body expr ->
        -- is it safe to eval the binding here? I'm not sure
        let newEnv = V.ValueEnv{locals = V.Var lvl : locals, ..}
         in C.Let name <$> zonkTerm' (lvl, env) body <*> zonkTerm' (succ lvl, newEnv) expr
    C.Case arg C.CaseWD{branches, def} -> do
        arg <- zonkTerm' c arg
        branches <- zonkBranches branches
        def <- traverse (bitraverse pure $ zonkTerm' (succ lvl, V.ValueEnv{locals = V.Var lvl : locals, ..})) def
        pure $ C.Case arg C.CaseWD{branches, def}
      where
        zonkBranches = \case
            C.ConCase idmap ->
                C.ConCase <$> for idmap \(pat, body) ->
                    let env = V.ValueEnv{locals = freeVars <> locals, ..}
                        (freeVars, newLevel) = liftLevel lvl (C.patternArity pat)
                     in (pat,) <$> zonkTerm' (newLevel, env) body
            C.TypeCase idmap ->
                C.TypeCase <$> for idmap \(pat, body) ->
                    let env = V.ValueEnv{locals = freeVars <> locals, ..}
                        (freeVars, newLevel) = liftLevel lvl (C.patternArity pat)
                     in (pat,) <$> zonkTerm' (newLevel, env) body
            C.VariantCase hmap ->
                C.VariantCase <$> for hmap \(name, body) ->
                    let env = V.ValueEnv{locals = V.Var lvl : locals, ..}
                     in (name,) <$> zonkTerm' (succ lvl, env) body
            C.LitCase lits -> C.LitCase <$> for lits \(lit, body) -> (lit,) <$> zonkTerm' c body
    C.Record row -> C.Record <$> traverse (zonkTerm' c) row
    C.Row row -> C.Row <$> traverse (zonkTerm' c) row
    C.RecordAccess term field -> C.RecordAccess <$> zonkTerm' c term <*> pure field
    C.Sigma vis lhs rhs -> C.Sigma vis <$> zonkTerm' c lhs <*> zonkTerm' c rhs
    C.Q q v e var ty body -> do
        ty <- zonkTerm' c ty
        C.Q q v e var ty <$> zonkTerm' (succ lvl, V.ValueEnv{locals = V.Var lvl : locals, ..}) body
    v@C.Var{} -> pure v
    n@C.Name{} -> pure n
    v@C.Variant{} -> pure v
    l@C.Literal{} -> pure l
    C.UniVar{} -> internalError' "univar outside of ElabInsert" -- zonkTerm' c (C.ElabInsert u)
    C.AppPruning{} -> internalError' "pruning outside of ElabInsert"

liftLevel :: Level -> Int -> ([Value], Level)
liftLevel lvl diff = (freeVars, newLevel)
  where
    freeVars = V.Var <$> [pred newLevel, pred (pred newLevel) .. lvl]
    newLevel = lvl `incLevel` diff
