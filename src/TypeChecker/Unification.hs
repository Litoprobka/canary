{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE RecordWildCards #-}

module TypeChecker.Unification (unify, refine, forceUnify) where

import Common
import Data.EnumMap.Strict qualified as EMap
import Data.EnumSet qualified as ESet
import Data.Row (ExtRow (..), zipRows)
import Data.Row qualified as Row
import Data.Vector qualified as Vec
import Diagnostic (currentLoc, internalError')
import Effectful.Error.Static (Error, catchError, runErrorNoCallStack, throwError_, tryError)
import Effectful.Labeled (labeled)
import Effectful.Reader.Static (runReader)
import Effectful.State.Static.Local (execState, get, gets, modify)
import Eval (
    ExtendedEnv (..),
    Postponed (..),
    PostponedEntry (..),
    UniVarState (..),
    UniVars,
    app,
    appM,
    applySpine,
    evalAppM,
    evalCore,
    force,
    forceM,
    quoteWhnf,
    quoteWhnfM,
    skolemizePatternClosure,
 )
import LangPrelude hiding (force, lift)
import NameGen (freshId)
import Prettyprinter (vsep)
import Syntax
import Syntax.Core (reversedPruning)
import Syntax.Core qualified as C
import Syntax.Value as V hiding (lift)
import Trace (trace, traceScope_)
import TypeChecker.Backend hiding (ExType (..))
import TypeChecker.TypeError (TypeError (..), UnificationError (..), typeError)

newtype ValueTopLevel = ValueTopLevel {getValues :: IdMap Name_ Value}
newtype LocalEq = LocalEq {getLocalEq :: EnumMap Level Value}

data Mode = Postpone | PruneEverything deriving (Eq)

type TC' es =
    (TC es, ?topLevel :: ValueTopLevel, ?localEq :: LocalEq, ?ctx :: Context, ?mode :: Mode, Error UnificationError :> es)

unify :: TC es => Context -> Value -> Value -> Eff es ()
unify ctx lhs rhs = do
    univars <- get
    -- prettyValCtx doesn't unroll solved univars, which is something that we need here
    let lhsC = prettyCoreCtx ctx $ quoteWhnf univars ctx.level lhs
        rhsC = prettyCoreCtx ctx $ quoteWhnf univars ctx.level rhs
    trace $ lhsC <+> specSym "~" <+> rhsC
    result <-
        let ?localEq = LocalEq ctx.localEquality
            ?topLevel = ValueTopLevel ctx.env.topLevel
            ?ctx = ctx
            ?mode = Postpone
         in runErrorNoCallStack
                . runReader ()
                $ unify' ctx.level lhs rhs
    case result of
        Right () -> pass
        Left context -> do
            mbLoc <- currentLoc
            typeError CannotUnify{mbLoc, lhs = lhsC, rhs = rhsC, context}

forceUnify :: TC es => Context -> Level -> Value -> Value -> Eff es ()
forceUnify ctx lvl lhs rhs = do
    univars <- get
    let lhsC = prettyDef $ quoteWhnf univars lvl lhs
        rhsC = prettyDef $ quoteWhnf univars lvl rhs
    trace $ lhsC <+> specSym "~" <+> rhsC
    result <-
        let ?localEq = LocalEq EMap.empty -- todo: seems like local equalities should be stored with postponing constraints
            ?topLevel = ValueTopLevel ctx.env.topLevel
            ?ctx = ctx
            ?mode = PruneEverything
         in runErrorNoCallStack
                . runReader ()
                $ unify' ctx.level lhs rhs
    case result of
        Right () -> pass
        Left context -> do
            mbLoc <- currentLoc
            typeError CannotUnify{mbLoc, lhs = lhsC, rhs = rhsC, context}

{- | given two values of the same type, add local equality constraints to the given context such that the values become equal
note that refinement is not symmetrical wrt. local equality constraints and unification variables,
so you generally want a value from an inner scope as the first argument and from an outer scope as the second
-}
refine :: TC es => Context -> Value -> Value -> Eff es Context
refine ctx lhs rhs = do
    univars <- get
    let lhsC = prettyCoreCtx ctx $ quoteWhnf univars ctx.level lhs
        rhsC = prettyCoreCtx ctx $ quoteWhnf univars ctx.level rhs
    traceScope_ (specSym "refine" <+> lhsC <+> specSym "~" <+> rhsC) do
        result <- runErrorNoCallStack $ refine' ctx lhs rhs
        case result of
            Right ctx -> pure ctx
            Left context -> do
                mbLoc <- currentLoc
                typeError CannotUnify{mbLoc, lhs = lhsC, rhs = rhsC, context}

-- todo: 'refine' should get its own type error that uses the same error context

unify' :: TC' es => Level -> Value -> Value -> Eff es ()
unify' lvl lhsTy rhsTy = do
    lhs' <- forceM lhsTy
    rhs' <- forceM rhsTy
    match lhs' rhs'
  where
    match = \cases
        (Var vlvl) (Var vlvl2) | vlvl == vlvl2 -> pass
        (Stuck (VarApp vlvl spine)) rhs | Just refined <- EMap.lookup vlvl ?localEq.getLocalEq -> do
            univars <- get
            let lhs = applySpine univars refined spine
            unify' lvl lhs rhs
        lhs (Stuck (VarApp vlvl spine)) | Just refined <- EMap.lookup vlvl ?localEq.getLocalEq -> do
            univars <- get
            let rhs = applySpine univars refined spine
            unify' lvl lhs rhs

        -- since unify is only ever called on two values of the same type,
        -- we known that these lambdas must have the same visibility
        (Lambda _vis lhsClosure) (Lambda _vis2 rhsClosure) -> do
            lhsBody <- lhsClosure `appM` Var lvl
            rhsBody <- rhsClosure `appM` Var lvl
            unify' (succ lvl) lhsBody rhsBody
        -- to unify a stuck value with a lambda, we eta-expand both sides
        --
        -- since the types of lhs and rhs are known to be the same, lhs must be a
        -- - prim function
        -- - stuck value
        --
        -- t ~ \x. expr
        -- t x ~ expr
        nonLambda (Lambda vis rhsClosure) -> do
            lhsBody <- evalAppM vis nonLambda (Var lvl)
            rhsBody <- rhsClosure `appM` Var lvl
            unify' (succ lvl) lhsBody rhsBody
        -- \x. expr ~ t
        -- expr ~ t x
        (Lambda vis lhsClosure) nonLambda -> do
            lhsBody <- lhsClosure `appM` Var lvl
            rhsBody <- evalAppM vis nonLambda (Var lvl)
            unify' (succ lvl) lhsBody rhsBody

        -- just like with lambdas, if the constructors are the same, their visibilities are guaranteed to match
        (TyCon lhs lhsArgs) (TyCon rhs rhsArgs)
            | lhs == rhs -> Vec.zipWithM_ (unify' lvl `on` snd) lhsArgs rhsArgs
            | otherwise -> throwError_ (NotEq (C.TyCon lhs Vec.empty) (C.TyCon rhs Vec.empty))
        (Con lhs lhsArgs) (Con rhs rhsArgs)
            | lhs == rhs -> Vec.zipWithM_ (unify' lvl `on` snd) lhsArgs rhsArgs
            | otherwise -> throwError_ (NotEq (C.Con lhs Vec.empty) (C.Con rhs Vec.empty))
        (Row lhsRow lhsExt) (Row rhsRow rhsExt) -> do
            let (both, lhsOnly, rhsOnly) = zipRows lhsRow rhsRow
            traverse_ (uncurry $ unify' lvl) both
            let bothClosedAndMatching = isNothing lhsExt && isNothing rhsExt && Row.isEmpty lhsOnly && Row.isEmpty rhsOnly
            unless bothClosedAndMatching do
                -- using the outer context here might be overly restrictive, but it's tedious to build up a new context during unification
                newExt <- freshUniVarS ?ctx (V.Type RowName)
                unifyRowExtension lvl (lhsRow, lhsExt) rhsOnly newExt
                unifyRowExtension lvl (rhsRow, rhsExt) lhsOnly newExt
        (Record lhsRow) (Record rhsRow) -> unify' lvl (Row lhsRow Nothing) (Row rhsRow Nothing)
        (Q Forall v _e closure) (Q Forall v2 _e2 closure2) | v == v2 -> do
            unify' lvl closure.ty closure2.ty
            body <- closure `appM` Var lvl
            body2 <- closure2 `appM` Var lvl
            unify' (succ lvl) body body2
        (Stuck (VarApp vlvl spine)) (Stuck (VarApp vlvl2 spine2))
            | vlvl == vlvl2 -> unifySpine lvl spine spine2
            | otherwise -> do
                lhs <- quoteWhnfM lvl (V.Var vlvl)
                rhs <- quoteWhnfM lvl (V.Var vlvl2)
                throwError_ (NotEq lhs rhs)
        (Stuck (Opaque name spine)) (Stuck (Opaque name2 spine2))
            | name == name2 -> unifySpine lvl spine spine2
            | otherwise -> throwError_ $ NotEq (C.Name name) (C.Name name2)
        lhs@(Stuck (UniVarApp uni spine)) rhs@(Stuck (UniVarApp uni2 spine2))
            | uni == uni2 -> postponeOnFailure lvl lhs rhs $ intersect lvl uni spine spine2
            | otherwise -> postponeOnFailure lvl lhs rhs $ uniUni lvl uni spine uni2 spine2
        lhs@(Stuck (UniVarApp uni spine)) rhs -> postponeOnFailure lvl lhs rhs $ solve lvl uni spine rhs
        lhs rhs@(Stuck (UniVarApp uni spine)) -> postponeOnFailure lvl lhs rhs $ solve lvl uni spine lhs
        (Stuck (Fn fn arg)) (Stuck (Fn fn2 arg2))
            | fn.name == fn2.name && length fn.captured == length fn2.captured -> do
                zipWithM_ (unify' lvl) fn.captured fn2.captured
                unify' lvl (Stuck arg) (Stuck arg2)
        lhs rhs -> do
            lhsC <- quoteWhnfM lvl lhs
            rhsC <- quoteWhnfM lvl rhs
            throwError_ (NotEq lhsC rhsC)

unifySpine :: TC' es => Level -> Spine -> Spine -> Eff es ()
unifySpine lvl = \cases
    [] [] -> pass
    ((_, ty1) : s1) ((_, ty2) : s2) -> do
        unifySpine lvl s1 s2
        unify' lvl ty1 ty2
    _ _ -> internalError' "spine length mismatch"

unifyRowExtension :: TC' es => Level -> (Row VType, Maybe Stuck) -> Row VType -> Stuck -> Eff es ()
unifyRowExtension lvl (_, Just ext) onlyInOther newExt = unify' lvl (Stuck ext) (Row onlyInOther (Just newExt))
unifyRowExtension lvl (row, Nothing) onlyInOther _
    | Row.isEmpty onlyInOther = pass
    | otherwise = do
        univars <- get
        throwError_ $ MissingFields (fmap (quoteWhnf univars lvl) row) (fmap (quoteWhnf univars lvl) onlyInOther)

refine' :: (TC es, Error UnificationError :> es) => Context -> Value -> Value -> Eff es Context
refine' ctx lhs' rhs' = do
    lhs' <- forceM lhs'
    rhs' <- forceM rhs'
    match lhs' rhs'
  where
    -- ideally, refinement logic should mirror all the pattern unification machinery, but with rigid variables
    match = \cases
        (Var vlvl) (Var vlvl2) | vlvl == vlvl2 -> pure ctx
        (Var vlvl) rhs -> case EMap.lookup vlvl ctx.localEquality of
            Just refined -> refine' ctx refined rhs
            Nothing -> pure ctx{localEquality = EMap.insert vlvl rhs ctx.localEquality}
        lhs (Var vlvl) -> case EMap.lookup vlvl ctx.localEquality of
            Just refined -> refine' ctx lhs refined
            Nothing -> pure ctx{localEquality = EMap.insert vlvl lhs ctx.localEquality}
        (Stuck (VarApp vlvl spine)) rhs | Just refined <- EMap.lookup vlvl ctx.localEquality -> do
            univars <- get
            refine' ctx (applySpine univars refined spine) rhs
        (Stuck (VarApp vlvl spine)) (Stuck (VarApp vlvl2 spine2)) | vlvl == vlvl2 -> refineSpine ctx spine spine2
        lhs (Stuck (VarApp vlvl spine)) | Just refined <- EMap.lookup vlvl ctx.localEquality -> do
            univars <- get
            refine' ctx lhs (applySpine univars refined spine)
        (TyCon lhs lhsArgs) (TyCon rhs rhsArgs)
            | lhs == rhs -> foldlM (\ctx ((_, lhsArg), (_, rhsArg)) -> refine' ctx lhsArg rhsArg) ctx $ Vec.zip lhsArgs rhsArgs
            | otherwise -> throwError_ (NotEq (C.TyCon lhs Vec.empty) (C.TyCon rhs Vec.empty))
        (Con lhs lhsArgs) (Con rhs rhsArgs)
            | lhs == rhs -> foldlM (\ctx ((_, lhsArg), (_, rhsArg)) -> refine' ctx lhsArg rhsArg) ctx $ Vec.zip lhsArgs rhsArgs
            | otherwise -> throwError_ (NotEq (C.Con lhs Vec.empty) (C.Con rhs Vec.empty))
        -- todo: cases for rows, records and variants
        lhs rhs -> ctx <$ unify ctx lhs rhs

refineSpine :: (TC es, Error UnificationError :> es) => Context -> Spine -> Spine -> Eff es Context
refineSpine ctx = \cases
    [] [] -> pure ctx
    ((_, ty1) : s1) ((_, ty2) : s2) -> do
        ctx <- refineSpine ctx s1 s2
        refine' ctx ty1 ty2
    _ _ -> internalError' "spine length mismatch"

-- pattern unification, based on the example implementation in elaboration-zoo by Andras Kovacs

data PartialRenaming = PartialRenaming
    { uni :: Maybe UniVar -- unification variable for occurs check, if any
    , domain :: Level
    , codomain :: Level
    , renaming :: EnumMap Level Level
    }
    deriving (Show)

-- | add a variable to a partial renaming
lift :: PartialRenaming -> PartialRenaming
lift PartialRenaming{uni, domain, codomain, renaming} =
    PartialRenaming
        { uni
        , domain = succ domain
        , codomain = succ codomain
        , renaming = EMap.insert codomain domain renaming
        }

-- | add multiple variables to a partial renaming
liftN :: Int -> PartialRenaming -> PartialRenaming
liftN n | n < 0 = error "negative lift"
liftN 0 = id
liftN n = lift . liftN (pred n)

skip :: PartialRenaming -> PartialRenaming
skip PartialRenaming{codomain, ..} = PartialRenaming{codomain = succ codomain, ..}

solve :: TC' es => Level -> UniVar -> Spine -> Value -> Eff es ()
solve ctxLevel uni spine rhs = case ?mode of
    Postpone -> do
        pren <- invert ctxLevel spine
        solveWithRenaming uni pren rhs
    PruneEverything ->
        tryError @UnificationError (invert ctxLevel spine) >>= \case
            Right pren -> solveWithRenaming uni pren rhs
            Left (_, err@NonVarInSpine{}) -> do
                pruneNonVars uni spine err
                unify' ctxLevel (Stuck $ UniVarApp uni spine) rhs
            Left (_, nonPrunable) -> throwError_ nonPrunable

solveWithRenaming :: TC' es => UniVar -> (PartialRenaming, Maybe Pruning) -> Value -> Eff es ()
solveWithRenaming uni (pren, pruneNonlinear) rhs = do
    univars <- get @UniVars
    (blocked, ty) <- readUnsolvedUniVar uni
    for_ pruneNonlinear \pruning -> pruneType (reversedPruning pruning) ty
    rhs' <- rename pren{uni = Just uni} rhs
    let env = ExtendedEnv{univars, topLevel = ?topLevel.getValues, locals = []}
    let solution = evalCore env $ lambdas univars pren.domain ty rhs'
    modify @UniVars $ EMap.insert uni $ Solved{solution, ty}
    for_ (ESet.toList blocked) retryPostponed

{- | used in the PruneEverything mode. Prune all arguments that are not variables from a spine
if there's nothing to prune, rethrow the given error
-}
pruneNonVars :: TC' es => UniVar -> Spine -> UnificationError -> Eff es ()
pruneNonVars uni spine err = do
    let pruning = Pruning $ fmap pruneNonVar spine
    void
        if all isJust pruning.getPruning
            then throwError_ err
            else pruneUniVar pruning uni
  where
    pruneNonVar = \case
        (vis, V.Var{}) -> Just vis
        _ -> Nothing

{- | convert a spine to a partial renaming
also returns a pruning of non-linear vars, if one is needed
-}
invert :: TC' es => Level -> Spine -> Eff es (PartialRenaming, Maybe Pruning)
invert codomain spine = do
    (domain, renaming, nonLinears, varSpine) <- go spine

    let mask :: [(Visibility, Level)] -> Pruning
        mask [] = Pruning []
        mask ((vis, lvl) : rest)
            | ESet.member lvl nonLinears = Pruning $ Nothing : (mask rest).getPruning
            | otherwise = Pruning $ Just vis : (mask rest).getPruning

        -- a pruning that eliminates non-linear vars
        mbPruning = mask varSpine <$ guard (not $ ESet.null nonLinears)

    pure (PartialRenaming{uni = Nothing, domain, codomain, renaming}, mbPruning)
  where
    go :: TC' es => Spine -> Eff es (Level, EnumMap Level Level, EnumSet Level, [(Visibility, Level)])
    go [] = pure (Level 0, EMap.empty, ESet.empty, [])
    go ((vis, ty) : spine') = do
        (domain, renaming, nonLinears, rest) <- go spine'
        forceM ty >>= \case
            Var vlvl
                | EMap.member vlvl renaming || ESet.member vlvl nonLinears ->
                    pure (succ domain, EMap.delete vlvl renaming, ESet.insert vlvl nonLinears, (vis, vlvl) : rest)
                | otherwise ->
                    pure (succ domain, EMap.insert vlvl domain renaming, nonLinears, (vis, vlvl) : rest)
            -- TODO: Level 0 is obviously incorrect here, but I'm not sure whether we should use the domain or the codomain
            other -> throwError_ (NonVarInSpine $ quoteWhnf EMap.empty codomain other)

data PruneStatus
    = -- | the spine only contains vars so far and can be pruned if needed
      Renaming
    | -- | the spine contains non-var arguments and cannot be pruned
      NonRenaming
    | -- | the spine contains variables that are out of scope of the renaming. We need to prune them
      NeedsPruning

{- | rename a univar with a spine
if it contains any variables not covered by the renaming, prune them
-}
renameUniVarApp :: TC' es => PartialRenaming -> UniVar -> Spine -> Eff es CoreTerm
renameUniVarApp pren uni initialSpine = do
    (spine, status) <- go initialSpine
    newUni <- case status of
        NeedsPruning ->
            let pruning = Pruning $ map (uncurry (<$)) spine
             in pruneUniVar pruning uni
        _ -> uni <$ readUnsolvedUniVar uni
    pure $ foldr (\(vis, mbTy) acc -> maybe acc (C.App vis acc) mbTy) (C.UniVar newUni) spine
  where
    go [] = pure ([], Renaming)
    go ((vis, ty) : rest) = do
        (spine, status) <- go rest
        forceM ty >>= \case
            Var vlvl -> case (EMap.lookup vlvl pren.renaming, status) of
                (Just targetLvl, _) -> pure ((vis, Just $ C.Var $ levelToIndex pren.domain targetLvl) : spine, status)
                (Nothing, NonRenaming) | ?mode /= PruneEverything -> throwError_ (PruneNonRenaming initialSpine)
                (Nothing, _) -> pure ((vis, Nothing) : spine, NeedsPruning)
            other -> case status of
                NeedsPruning
                    | ?mode == PruneEverything -> pure ((vis, Nothing) : spine, NeedsPruning)
                    | otherwise -> throwError_ (PruneNonPattern initialSpine)
                _ -> do
                    term <- rename pren other
                    pure ((vis, Just term) : spine, NonRenaming)

rename :: TC' es => PartialRenaming -> Value -> Eff es CoreTerm
rename pren ty =
    forceM ty >>= \case
        Stuck (UniVarApp uni2 spine)
            | pren.uni == Just uni2 -> throwError_ (OccursCheck uni2)
            | otherwise -> renameUniVarApp pren uni2 spine
        Stuck (VarApp lvl spine) -> do
            univars <- get
            case (EMap.lookup lvl pren.renaming, EMap.lookup lvl ?localEq.getLocalEq) of
                (Nothing, Nothing) -> throwError_ (EscapingVariable pren.uni lvl)
                (Just x, _) -> renameSpine pren (C.Var $ levelToIndex pren.domain x) spine
                (Nothing, Just refined) -> rename pren (applySpine univars refined spine)
        Lambda vis closure -> do
            bodyToRename <- closure `appM` Var pren.codomain
            C.Lambda vis closure.var <$> rename (lift pren) bodyToRename
        Q q v e closure -> do
            argTy <- rename pren closure.ty
            bodyToRename <- closure `appM` Var pren.codomain
            C.Q q v e closure.var argTy <$> rename (lift pren) bodyToRename
        TyCon name args -> C.TyCon name <$> (traverse . traverse) (rename pren) args
        Con name args -> C.Con name <$> (traverse . traverse) (rename pren) args
        Variant name arg -> C.Variant name <$> rename pren arg
        PrimFunction fn -> do
            captured <- traverse (rename pren) fn.captured
            pure $ foldr (flip $ C.App Visible) (C.Name fn.name) captured
        Record row -> C.Record <$> traverse (rename pren) row
        Row row Nothing -> C.Row <$> traverse (rename pren) (NoExtRow row)
        Row row (Just ext) -> C.Row <$> traverse (rename pren) (ExtRow row (Stuck ext))
        Sigma x y -> C.Sigma <$> rename pren x <*> rename pren y
        PrimValue lit -> pure $ C.Literal lit
        Stuck (Opaque name spine) -> renameSpine pren (C.Name name) spine
        Stuck (Fn fn stuck) -> C.App Visible <$> rename pren (PrimFunction fn) <*> rename pren (Stuck stuck)
        Stuck (Case arg branches) -> C.Case <$> rename pren (Stuck arg) <*> traverse (renameBranch pren) branches

renameSpine :: TC' es => PartialRenaming -> CoreTerm -> Spine -> Eff es CoreTerm
renameSpine _ term [] = pure term
renameSpine pren term ((vis, ty) : spine) = C.App vis <$> renameSpine pren term spine <*> rename pren ty

renameBranch :: TC' es => PartialRenaming -> PatternClosure a -> Eff es (CorePattern, CoreTerm)
renameBranch pren closure = do
    univars <- get
    let (bodyV, newLevel) = skolemizePatternClosure univars pren.codomain closure
        diff = newLevel.getLevel - pren.codomain.getLevel
    renamedBody <- rename (liftN diff pren) bodyV
    pure (closure.pat, renamedBody)

-- wrap a term in lambdas
lambdas :: UniVars -> Level -> VType -> CoreTerm -> CoreTerm
lambdas univars targetLvl initTy body = go initTy (Level 0)
  where
    go :: VType -> Level -> CoreTerm
    go _ lvl | lvl == targetLvl = body
    go ty lvl = case force univars ty of
        Q Forall vis _e closure -> C.Lambda vis closure.var $ go (app univars closure (Var lvl)) (succ lvl)
        _nonPi ->
            error . show $
                vsep
                    [ "less arguments in type than expected: got" <+> pretty lvl.getLevel <> ", expected at least" <+> pretty targetLvl.getLevel
                    , "in type:" <+> pretty initTy
                    ]

-- remove arguments masked by a pruning from a multi-arg Pi type
-- used to construct the type of a new univars
pruneType :: TC' es => ReversedPruning -> VType -> Eff es CoreType
pruneType (ReversedPruning initPruning) =
    go initPruning PartialRenaming{uni = Nothing, domain = Level 0, codomain = Level 0, renaming = EMap.empty}
  where
    go pruning pren ty = do
        ty <- forceM ty
        case (pruning, ty) of
            ([], _) -> rename pren ty
            (Just _ : rest, Q Forall vis e closure) -> do
                argTy <- rename pren closure.ty
                body <- go rest (lift pren) =<< closure `appM` Var pren.codomain
                pure $ C.Q Forall vis e closure.var argTy body
            (Nothing : rest, Q Forall _ _ closure) -> go rest (skip pren) =<< closure `appM` Var pren.codomain
            _ -> error "pruning: not enough arguments in a pi type"

-- | apply a pruning to a univar, produce a new univar with its type also pruned
pruneUniVar :: TC' es => Pruning -> UniVar -> Eff es UniVar
pruneUniVar pruning uni = do
    univars <- get
    (blocked, ty) <- readUnsolvedUniVar uni
    let env = ExtendedEnv{locals = [], topLevel = ?topLevel.getValues, ..}
    prunedType <- evalCore env <$> pruneType (reversedPruning pruning) ty
    newUni <- newUniVar prunedType
    univars' <- get
    let env' = ExtendedEnv{locals = [], univars = univars', topLevel = ?topLevel.getValues}
        solution = evalCore env' $ lambdas univars (Level $ length pruning.getPruning) ty $ C.AppPruning (C.UniVar newUni) pruning
    modify @UniVars $ EMap.insert uni $ Solved{solution, ty}
    for_ (ESet.toList blocked) retryPostponed
    pure newUni

-- try to solve the inner univar with the outer one
-- if the spine of the inner univar is not invertible, try to solve the outer one
uniUni :: TC' es => Level -> UniVar -> Spine -> UniVar -> Spine -> Eff es ()
uniUni ctxLvl uni spine uni2 spine2
    | length spine < length spine2 = go uni2 spine2 uni spine
    | otherwise = go uni spine uni2 spine2
  where
    go u sp u2 sp2 =
        tryError @UnificationError (invert ctxLvl sp) >>= \case
            Left{} -> solve ctxLvl u2 sp2 (Stuck $ UniVarApp u sp)
            Right pren -> solveWithRenaming u pren (Stuck $ UniVarApp u2 sp2)

{- | solve @uni spine ~ uni spine'@ by removing all variables that are not present in either of the spines

e.g. @?a x y z w ~ ?a x u z v ===> ?a x _ z _ ~ ?b x z@
-}
intersect :: TC' es => Level -> UniVar -> Spine -> Spine -> Eff es ()
intersect lvl uni spine spine2 = do
    univars <- get
    case go univars spine spine2 of
        Nothing -> unifySpine lvl spine spine2
        Just pruning
            | any isNothing pruning -> void $ pruneUniVar (Pruning pruning) uni
            | otherwise -> pass
  where
    go univars = \cases
        [] [] -> Just []
        ((vis, t) : rest) ((_, t2) : rest2) -> case (force univars t, force univars t2) of
            (Var x, Var x2) ->
                let visOrPrune = vis <$ guard (x == x2)
                 in (visOrPrune :) <$> go univars rest rest2
            _ -> Nothing
        _ _ -> error "spine length mismatch"

-- | if the current failure mode allows it, postpone in case of an ambiguity error
postponeOnFailure :: TC' es => Level -> Value -> Value -> Eff es () -> Eff es ()
postponeOnFailure lvl lhs rhs action = case ?mode of
    PruneEverything -> action
    Postpone -> catchError @UnificationError action \_ -> \case
        NonVarInSpine{} -> do
            univars <- get
            let blockingUnivars = ESet.toList $ runPureEff $ execState ESet.empty do
                    freeVarsInCore univars (quoteWhnf univars lvl lhs)
                    freeVarsInCore univars (quoteWhnf univars lvl rhs)
            trace $ specSym "postpone" <+> foldr ((<+>) . prettyDef) mempty blockingUnivars
            postpone lvl blockingUnivars lhs rhs
        nonPostponable -> throwError_ nonPostponable

-- | postpone a unification check, block on the given list of univars
postpone :: TC' es => Level -> [UniVar] -> Value -> Value -> Eff es ()
postpone lvl univars lhs rhs = do
    pId <- Postponed <$> labeled @Postponed freshId
    modify $ EMap.insert pId (PostponedEntry lvl lhs rhs)
    let addBlock = \case
            Solved{} -> error "unexpected solved univar"
            Unsolved{blocks, ty} -> Unsolved{blocks = ESet.insert pId blocks, ty}

    for_ univars (modify . EMap.adjust addBlock)

-- | try to solve a postponed constraint
retryPostponed :: TC' es => Postponed -> Eff es ()
retryPostponed pId =
    gets (EMap.lookup pId) >>= \case
        Nothing -> pass
        Just (PostponedEntry lvl lhs rhs) -> do
            trace $ specSymBlue "retry" <+> pretty pId
            modify $ EMap.delete pId
            unify' lvl lhs rhs
