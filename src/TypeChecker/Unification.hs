{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE RecordWildCards #-}

module TypeChecker.Unification where

import Common
import Data.EnumMap.Strict qualified as EMap
import Data.EnumSet qualified as ESet
import Diagnostic (internalError')
import Effectful.Error.Static (Error, runErrorNoCallStack, throwError)
import Effectful.State.Static.Local (get, modify)
import Eval (ExtendedEnv (..), UniVarState (..), UniVars, app, app', evalApp', evalCore, force, force', quote)
import LangPrelude hiding (force, lift)
import Prettyprinter (vsep)
import Prettyprinter.Render.Terminal (AnsiStyle)
import Syntax
import Syntax.Core qualified as C
import Syntax.Value as V hiding (lift)
import TypeChecker.Backend hiding (ExType (..))

type ValueTopLevel = IdMap Name_ Value

-- passing around topLevel like this is a bit ugly, perhaps unify should just take a Context?
unify :: TC es => ValueTopLevel -> Level -> Value -> Value -> Eff es ()
unify topLevel lvl lhsTy rhsTy = do
    lhs' <- force' lhsTy
    rhs' <- force' rhsTy
    match lhs' rhs'
  where
    match = \cases
        -- since unify is only ever called on two values of the same type,
        -- we known that these lambdas must have the same visibility
        (Lambda _vis lhsClosure) (Lambda _vis2 rhsClosure) -> do
            lhsBody <- lhsClosure `app'` Var lvl
            rhsBody <- rhsClosure `app'` Var lvl
            unify topLevel (succ lvl) lhsBody rhsBody
        -- to unify a stuck value with a lambda, we eta-expand both sides
        --
        -- since the types of lhs and rhs are known to be the same, lhs must be a
        -- - prim function
        -- - stuck value
        --
        -- t ~ \x. expr
        -- t x ~ expr
        nonLambda (Lambda vis rhsClosure) -> do
            lhsBody <- evalApp' vis nonLambda (Var lvl)
            rhsBody <- rhsClosure `app'` Var lvl
            unify topLevel (succ lvl) lhsBody rhsBody
        -- \x. expr ~ t
        -- expr ~ t x
        (Lambda vis lhsClosure) nonLambda -> do
            lhsBody <- lhsClosure `app'` Var lvl
            rhsBody <- evalApp' vis nonLambda (Var lvl)
            unify topLevel (succ lvl) lhsBody rhsBody
        (TyCon lhs lhsArgs) (TyCon rhs rhsArgs) | lhs == rhs -> zipWithM_ (unify topLevel lvl) lhsArgs rhsArgs
        (Q Forall v _e closure) (Q Forall v2 _e2 closure2) | v == v2 -> do
            unify topLevel lvl closure.ty closure2.ty
            body <- closure `app'` Var lvl
            body2 <- closure2 `app'` Var lvl
            unify topLevel (succ lvl) body body2
        (Stuck (VarApp vlvl spine)) (Stuck (VarApp vlvl2 spine2)) | vlvl == vlvl2 -> do
            unifySpine topLevel lvl spine spine2
        (Stuck (UniVarApp uni spine)) (Stuck (UniVarApp uni2 spine2)) | uni == uni2 -> intersect topLevel lvl uni spine spine2
        (Stuck (UniVarApp uni spine)) (Stuck (UniVarApp uni2 spine2)) -> uniUni topLevel lvl uni spine uni2 spine2
        (Stuck (UniVarApp uni spine)) ty -> solve topLevel lvl uni spine ty
        ty (Stuck (UniVarApp uni spine)) -> solve topLevel lvl uni spine ty
        (Stuck (Fn fn arg)) (Stuck (Fn fn2 arg2))
            | fn.name == fn2.name && length fn.captured == length fn2.captured -> do
                zipWithM_ (unify topLevel lvl) fn.captured fn2.captured
                unify topLevel lvl (Stuck arg) (Stuck arg2)
        lhs rhs -> do
            univars <- get @UniVars
            internalError' $ "cannot unify" <+> pretty (quote univars lvl lhs) <+> "with" <+> pretty (quote univars lvl rhs)

unifySpine :: TC es => ValueTopLevel -> Level -> Spine -> Spine -> Eff es ()
unifySpine topLevel lvl = \cases
    [] [] -> pass
    ((_, ty1) : s1) ((_, ty2) : s2) -> do
        unifySpine topLevel lvl s1 s2
        unify topLevel lvl ty1 ty2
    _ _ -> internalError' "spine length mismatch"

{-
the way we treat unification variables is based on the example implementation in elaboration-zoo
by Andras Kovacs
-}

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

skip :: PartialRenaming -> PartialRenaming
skip PartialRenaming{codomain, ..} = PartialRenaming{codomain = succ codomain, ..}

solve :: TC es => ValueTopLevel -> Level -> UniVar -> Spine -> Value -> Eff es ()
solve topLevel ctxLevel uni spine rhs = do
    pren <- either internalError' pure =<< invert ctxLevel spine
    solveWithRenaming topLevel uni pren rhs

solveWithRenaming :: TC es => ValueTopLevel -> UniVar -> (PartialRenaming, Maybe Pruning) -> Value -> Eff es ()
solveWithRenaming topLevel uni (pren, pruneNonlinear) rhs = do
    univars <- get @UniVars
    ty <- typeOfUnsolvedUniVar uni
    for_ pruneNonlinear \pruning -> pruneType topLevel (ReversedPruning $ reverse pruning.getPruning) ty
    rhs' <- rename topLevel pren{uni = Just uni} rhs
    let env = ExtendedEnv{univars, topLevel, locals = []}
    let solution = evalCore env $ lambdas univars pren.domain ty rhs'
    modify @UniVars $ EMap.insert uni $ Solved{solution, ty}

{- | convert a spine to a partial renaming
also returns a pruning of non-linear vars, if one is needed
-}
invert :: TC es => Level -> Spine -> Eff es (Either (Doc AnsiStyle) (PartialRenaming, Maybe Pruning))
invert codomain spine = runErrorNoCallStack do
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
    go :: TC es => Spine -> Eff (Error (Doc AnsiStyle) : es) (Level, EnumMap Level Level, EnumSet Level, [(Visibility, Level)])
    go [] = pure (Level 0, EMap.empty, ESet.empty, [])
    go ((vis, ty) : spine') = do
        (domain, renaming, nonLinears, rest) <- go spine'
        force' ty >>= \case
            Var vlvl
                | EMap.member vlvl renaming || ESet.member vlvl nonLinears ->
                    pure (succ domain, EMap.delete vlvl renaming, ESet.insert vlvl nonLinears, (vis, vlvl) : rest)
                | otherwise ->
                    pure (succ domain, EMap.insert vlvl domain renaming, nonLinears, (vis, vlvl) : rest)
            other -> throwError @(Doc AnsiStyle) $ "non-var in spine" <+> pretty other

data PruneStatus
    = Renaming
    | NonRenaming
    | NeedsPruning

pruneUniVarApp :: TC es => ValueTopLevel -> PartialRenaming -> UniVar -> Spine -> Eff es CoreTerm
pruneUniVarApp topLevel pren uni spine = do
    (spine', status) <- go spine
    newUni <- case status of
        NeedsPruning ->
            let pruning = Pruning $ map (uncurry (<$)) spine'
             in pruneUniVar topLevel pruning uni
        _ -> uni <$ typeOfUnsolvedUniVar uni
    pure $ foldr (\(vis, mbTy) acc -> maybe acc (C.App vis acc) mbTy) (C.UniVar newUni) spine'
  where
    go [] = pure ([], Renaming)
    go ((vis, ty) : rest) = do
        (spine', status) <- go rest
        force' ty >>= \case
            Var vlvl -> case (EMap.lookup vlvl pren.renaming, status) of
                (Just targetLvl, _) -> pure ((vis, Just $ C.Var $ levelToIndex pren.domain targetLvl) : spine', status)
                (Nothing, NonRenaming) -> internalError' "can't prune a spine that's not a renaming"
                (Nothing, _) -> pure ((vis, Nothing) : spine', NeedsPruning)
            other -> case status of
                NeedsPruning -> internalError' "can't prune a non-pattern spine"
                _ -> do
                    term <- rename topLevel pren other
                    pure ((vis, Just term) : spine', NonRenaming)

rename :: TC es => ValueTopLevel -> PartialRenaming -> Value -> Eff es CoreTerm
rename topLevel = go
  where
    goSpine _ term [] = pure term
    goSpine pren term ((vis, ty) : spine) = C.App vis <$> goSpine pren term spine <*> go pren ty

    go pren ty =
        force' ty >>= \case
            Stuck (UniVarApp uni2 spine)
                | pren.uni == Just uni2 -> internalError' "self-referential type"
                | otherwise -> pruneUniVarApp topLevel pren uni2 spine
            Stuck (VarApp lvl spine) -> case EMap.lookup lvl pren.renaming of
                Nothing ->
                    internalError' $
                        "escaping variable" <+> "#" <> pretty lvl.getLevel <+> "in scope:" <+> pretty (map (show @Text) $ EMap.keys pren.renaming)
                Just x -> goSpine pren (C.Var $ levelToIndex pren.domain x) spine
            Lambda vis closure -> do
                bodyToRename <- closure `app'` Var pren.codomain
                C.Lambda vis closure.var <$> go (lift pren) bodyToRename
            Q q v e closure -> do
                argTy <- go pren closure.ty
                bodyToRename <- closure `app'` Var pren.codomain
                C.Q q v e closure.var argTy <$> go (lift pren) bodyToRename
            TyCon name args -> foldl' (C.App Visible) (C.Name name) <$> traverse (go pren) args
            Con name args -> foldl' (C.App Visible) (C.Name name) <$> traverse (go pren) args
            PrimFunction fn -> do
                captured <- traverse (go pren) fn.captured
                pure $ foldr (flip $ C.App Visible) (C.Name fn.name) captured
            Record row -> C.Record <$> traverse (go pren) row
            RecordT row -> C.RecordT <$> traverse (go pren) row
            VariantT row -> C.VariantT <$> traverse (go pren) row
            Sigma x y -> C.Sigma <$> go pren x <*> go pren y
            PrimValue lit -> pure $ C.Literal lit
            Variant name arg -> C.App Visible (C.Variant name) <$> go pren arg
            Stuck (Fn fn stuck) -> C.App Visible <$> go pren (PrimFunction fn) <*> go pren (Stuck stuck)
            Stuck Case{} -> error "todo: rename stuck case"

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
pruneType :: TC es => ValueTopLevel -> ReversedPruning -> VType -> Eff es CoreType
pruneType topLevel (ReversedPruning initPruning) =
    go initPruning PartialRenaming{uni = Nothing, domain = Level 0, codomain = Level 0, renaming = EMap.empty}
  where
    go pruning pren ty = do
        ty' <- force' ty
        univars <- get
        case (pruning, ty') of
            ([], _) -> rename topLevel pren ty'
            (Just _ : rest, Q Forall vis e closure) -> do
                argTy <- rename topLevel pren closure.ty
                body <- go rest (lift pren) (app univars closure (Var pren.codomain))
                pure $ C.Q Forall vis e closure.var argTy body
            (Nothing : rest, Q Forall _ _ closure) -> go rest (skip pren) (app univars closure (Var pren.codomain))
            _ -> error "pruning: not enough arguments on a pi type"

-- | apply a pruning to a univar, produce a new univar with its type also pruned
pruneUniVar :: TC es => ValueTopLevel -> Pruning -> UniVar -> Eff es UniVar
pruneUniVar topLevel pruning uni = do
    univars <- get
    ty <- typeOfUnsolvedUniVar uni
    let env = ExtendedEnv{locals = [], ..}
    prunedType <- evalCore env <$> pruneType topLevel (ReversedPruning $ reverse pruning.getPruning) ty
    newUni <- newUniVar prunedType
    univars' <- get
    let env' = ExtendedEnv{locals = [], univars = univars', ..}
        solution = evalCore env' $ lambdas univars (Level $ length pruning.getPruning) ty $ C.AppPruning (C.UniVar newUni) pruning
    modify @UniVars $ EMap.insert uni $ Solved{solution, ty}
    pure newUni

-- try to solve the inner univar with the outer one
-- if the spine of the inner univar is not invertible, try to solve the outer one
uniUni :: TC es => ValueTopLevel -> Level -> UniVar -> Spine -> UniVar -> Spine -> Eff es ()
uniUni topLevel ctxLvl uni spine uni2 spine2
    | length spine < length spine2 = go uni2 spine2 uni spine
    | otherwise = go uni spine uni2 spine2
  where
    go u sp u2 sp2 =
        invert ctxLvl sp >>= \case
            Left{} -> solve topLevel ctxLvl u2 sp2 (Stuck $ UniVarApp u sp)
            Right pren -> solveWithRenaming topLevel u pren (Stuck $ UniVarApp u2 sp2)

intersect :: TC es => ValueTopLevel -> Level -> UniVar -> Spine -> Spine -> Eff es ()
intersect topLevel lvl uni spine spine2 = do
    univars <- get
    case go univars spine spine2 of
        Nothing -> unifySpine topLevel lvl spine spine2
        Just pruning
            | any isNothing pruning -> void $ pruneUniVar topLevel (Pruning pruning) uni
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
