{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE RecordWildCards #-}

module TypeChecker.Unification (unify) where

import Common
import Data.EnumMap.Strict qualified as EMap
import Data.EnumSet qualified as ESet
import Data.Vector qualified as Vec
import Diagnostic (currentLoc, internalError')
import Effectful.Error.Static (Error, runErrorNoCallStack, throwError_, tryError)
import Effectful.Reader.Static (Reader, asks, runReader)
import Effectful.State.Static.Local (get, modify)
import Eval (
    ExtendedEnv (..),
    UniVarState (..),
    UniVars,
    app,
    appM,
    evalAppM,
    evalCore,
    force,
    forceM,
    quote,
    quoteM,
    skolemizePatternClosure,
 )
import LangPrelude hiding (force, lift)
import Prettyprinter (vsep)
import Syntax
import Syntax.Core (reversedPruning)
import Syntax.Core qualified as C
import Syntax.Value as V hiding (lift)
import Trace (trace)
import TypeChecker.Backend hiding (ExType (..))
import TypeChecker.TypeError (TypeError (..), UnificationError (..), typeError)

newtype ValueTopLevel = ValueTopLevel {getValues :: IdMap Name_ Value}

askValues :: Reader ValueTopLevel :> es => Eff es (IdMap Name_ Value)
askValues = asks (.getValues)

type TC' es = (TC es, Reader ValueTopLevel :> es, Error UnificationError :> es)

unify :: TC es => Context -> Value -> Value -> Eff es ()
unify ctx lhs rhs = do
    univars <- get
    let lhsC = prettyCoreCtx ctx $ quote univars ctx.level lhs
        rhsC = prettyCoreCtx ctx $ quote univars ctx.level rhs
    trace $ lhsC <+> specSym "~" <+> rhsC
    result <- runErrorNoCallStack $ runReader (ValueTopLevel ctx.env.topLevel) $ unify' ctx.level lhs rhs
    case result of
        Right () -> pass
        Left context -> do
            -- fixme: location info should be handled outside of here
            loc <-
                currentLoc >>= \case
                    Just loc -> pure loc
                    Nothing -> internalError' "no loc available in unify"
            typeError CannotUnify{loc, lhs = lhsC, rhs = rhsC, context}

unify' :: TC' es => Level -> Value -> Value -> Eff es ()
unify' lvl lhsTy rhsTy = do
    lhs' <- forceM lhsTy
    rhs' <- forceM rhsTy
    match lhs' rhs'
  where
    match = \cases
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
        (Q Forall v _e closure) (Q Forall v2 _e2 closure2) | v == v2 -> do
            unify' lvl closure.ty closure2.ty
            body <- closure `appM` Var lvl
            body2 <- closure2 `appM` Var lvl
            unify' (succ lvl) body body2
        (Stuck (VarApp vlvl spine)) (Stuck (VarApp vlvl2 spine2))
            | vlvl == vlvl2 -> unifySpine lvl spine spine2
            | otherwise -> do
                lhs <- quoteM lvl (V.Var vlvl)
                rhs <- quoteM lvl (V.Var vlvl2)
                throwError_ (NotEq lhs rhs)
        (Stuck (Opaque name spine)) (Stuck (Opaque name2 spine2))
            | name == name2 -> unifySpine lvl spine spine2
            | otherwise -> throwError_ $ NotEq (C.Name name) (C.Name name2)
        (Stuck (UniVarApp uni spine)) (Stuck (UniVarApp uni2 spine2)) | uni == uni2 -> intersect lvl uni spine spine2
        (Stuck (UniVarApp uni spine)) (Stuck (UniVarApp uni2 spine2)) -> uniUni lvl uni spine uni2 spine2
        (Stuck (UniVarApp uni spine)) ty -> solve lvl uni spine ty
        ty (Stuck (UniVarApp uni spine)) -> solve lvl uni spine ty
        (Stuck (Fn fn arg)) (Stuck (Fn fn2 arg2))
            | fn.name == fn2.name && length fn.captured == length fn2.captured -> do
                zipWithM_ (unify' lvl) fn.captured fn2.captured
                unify' lvl (Stuck arg) (Stuck arg2)
        lhs rhs -> do
            lhsC <- quoteM lvl lhs
            rhsC <- quoteM lvl rhs
            throwError_ (NotEq lhsC rhsC)

unifySpine :: TC' es => Level -> Spine -> Spine -> Eff es ()
unifySpine lvl = \cases
    [] [] -> pass
    ((_, ty1) : s1) ((_, ty2) : s2) -> do
        unifySpine lvl s1 s2
        unify' lvl ty1 ty2
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
liftN 0 = id
liftN n = lift . liftN (pred n)

skip :: PartialRenaming -> PartialRenaming
skip PartialRenaming{codomain, ..} = PartialRenaming{codomain = succ codomain, ..}

solve :: TC' es => Level -> UniVar -> Spine -> Value -> Eff es ()
solve ctxLevel uni spine rhs = do
    pren <- invert ctxLevel spine
    solveWithRenaming uni pren rhs

solveWithRenaming :: TC' es => UniVar -> (PartialRenaming, Maybe Pruning) -> Value -> Eff es ()
solveWithRenaming uni (pren, pruneNonlinear) rhs = do
    univars <- get @UniVars
    ty <- typeOfUnsolvedUniVar uni
    for_ pruneNonlinear \pruning -> pruneType (reversedPruning pruning) ty
    rhs' <- rename pren{uni = Just uni} rhs
    topLevel <- askValues
    let env = ExtendedEnv{univars, topLevel, locals = []}
    let solution = evalCore env $ lambdas univars pren.domain ty rhs'
    modify @UniVars $ EMap.insert uni $ Solved{solution, ty}

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
            other -> throwError_ (NonVarInSpine $ quote EMap.empty (Level 0) other)

data PruneStatus
    = Renaming
    | NonRenaming
    | NeedsPruning

pruneUniVarApp :: TC' es => PartialRenaming -> UniVar -> Spine -> Eff es CoreTerm
pruneUniVarApp pren uni spine = do
    (spine', status) <- go spine
    newUni <- case status of
        NeedsPruning ->
            let pruning = Pruning $ map (uncurry (<$)) spine'
             in pruneUniVar pruning uni
        _ -> uni <$ typeOfUnsolvedUniVar uni
    pure $ foldr (\(vis, mbTy) acc -> maybe acc (C.App vis acc) mbTy) (C.UniVar newUni) spine'
  where
    go [] = pure ([], Renaming)
    go ((vis, ty) : rest) = do
        (spine', status) <- go rest
        forceM ty >>= \case
            Var vlvl -> case (EMap.lookup vlvl pren.renaming, status) of
                (Just targetLvl, _) -> pure ((vis, Just $ C.Var $ levelToIndex pren.domain targetLvl) : spine', status)
                (Nothing, NonRenaming) -> throwError_ (PruneNonRenaming spine)
                (Nothing, _) -> pure ((vis, Nothing) : spine', NeedsPruning)
            other -> case status of
                NeedsPruning -> throwError_ (PruneNonPattern spine)
                _ -> do
                    term <- rename pren other
                    pure ((vis, Just term) : spine', NonRenaming)

rename :: TC' es => PartialRenaming -> Value -> Eff es CoreTerm
rename pren ty =
    forceM ty >>= \case
        Stuck (UniVarApp uni2 spine)
            | pren.uni == Just uni2 -> throwError_ (OccursCheck uni2)
            | otherwise -> pruneUniVarApp pren uni2 spine
        Stuck (VarApp lvl spine) -> case EMap.lookup lvl pren.renaming of
            Nothing -> throwError_ (EscapingVariable pren.uni lvl)
            Just x -> renameSpine pren (C.Var $ levelToIndex pren.domain x) spine
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
        RecordT row -> C.RecordT <$> traverse (rename pren) row
        VariantT row -> C.VariantT <$> traverse (rename pren) row
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
        diff = pren.codomain.getLevel - newLevel.getLevel
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
    topLevel <- askValues
    ty <- typeOfUnsolvedUniVar uni
    let env = ExtendedEnv{locals = [], ..}
    prunedType <- evalCore env <$> pruneType (reversedPruning pruning) ty
    newUni <- newUniVar prunedType
    univars' <- get
    let env' = ExtendedEnv{locals = [], univars = univars', ..}
        solution = evalCore env' $ lambdas univars (Level $ length pruning.getPruning) ty $ C.AppPruning (C.UniVar newUni) pruning
    modify $ EMap.insert uni $ Solved{solution, ty}
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
