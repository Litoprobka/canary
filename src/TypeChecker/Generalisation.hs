{-# LANGUAGE RecordWildCards #-}

module TypeChecker.Generalisation where

import Common
import Data.EnumMap.Strict qualified as EMap
import Data.EnumSet qualified as ESet
import Data.Poset qualified as Poset
import Diagnostic (internalError')
import Effectful.Error.Static (runErrorNoCallStack)
import Effectful.State.Static.Local
import Eval (PostponedEntry (..), UniVarState (..), evalCore, nf, quote, quoteM)
import LangPrelude
import Prettyprinter (sep)
import Syntax
import Syntax.Core qualified as C
import Syntax.Elaborated qualified as E
import Syntax.Value qualified as V
import Trace (trace, traceScope_)
import TypeChecker.Backend
import TypeChecker.Unification

generalise :: TC es => Context -> VType -> Eff es VType
generalise ctx ty = snd <$> generalise' ctx Nothing (Nothing, ty)

generaliseTerm :: TC es => Context -> (ETerm, VType) -> Eff es (ETerm, VType)
generaliseTerm ctx (term, ty) = first runIdentity <$> generalise' ctx Nothing (Identity term, ty)

generaliseRecursiveTerm :: TC es => Context -> Name_ -> (ETerm, VType) -> Eff es (ETerm, VType)
generaliseRecursiveTerm ctx name (term, ty) = first runIdentity <$> generalise' ctx (Just name) (Identity term, ty)

-- | zonk unification variables from a term, report an error on leftover free variables
zonkTerm :: TC es => Context -> ETerm -> Eff es ETerm
zonkTerm ctx term = do
    (term, freeVars) <- runState ESet.empty $ zonkTerm' (ctx.level, ctx.env) term

    -- todo: this reports only the first variable
    -- also, I need a proper type error for this case
    for_ (ESet.toList freeVars) \freeUni -> do
        internalError' $ "ambiguous unification variable" <+> pretty freeUni
    pure term

{- | zonk unification variables from a term and its type,
generalise unsolved variables to new forall binders
-}
generalise' :: (TC es, Traversable t) => Context -> Maybe Name_ -> (t ETerm, VType) -> Eff es (t ETerm, VType)
generalise' ctx mbName (mbTerm, ty) = traceScope_ (specSymBlue "generalise" <+> prettyDef mbName) do
    -- first, we retry all postponed constraints once again
    postponings <- get
    trace $ "still blocked:" <+> pretty (EMap.size postponings)
    for_ postponings \(PostponedEntry lvl lhs rhs) -> forceUnify ctx lvl lhs rhs

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
        innerTerm <- traverse (zonkTerm' (newLevel, innerEnv) . E.lift newBinderCount) mbTerm
        freeVarsInCore univars innerType
        pure innerTerm

    unless (ESet.null freeVars) do
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

-- the only important case is E.Core, which may actually contain univars
-- the rest are just plain traversal logic
-- unfortunately, it doesn't quite fit 'elabTraversal', since the env logic is unique
zonkTerm' :: TC es => (Level, ValueEnv) -> ETerm -> Eff (State (EnumSet UniVar) : es) ETerm
zonkTerm' c@(lvl, env@V.ValueEnv{..}) = \case
    E.Core coreTerm -> do
        env <- extendEnv env
        let zonkedCore = nf lvl env coreTerm
        univars <- get
        freeVarsInCore univars zonkedCore
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
