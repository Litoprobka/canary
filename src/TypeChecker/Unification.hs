{-# LANGUAGE DuplicateRecordFields #-}

module TypeChecker.Unification where

import Common
import Data.EnumMap.Strict qualified as EMap
import Diagnostic (internalError')
import Effectful.State.Static.Local (get, modify)
import Eval (ExtendedEnv (..), UniVarState (..), UniVars, app', evalApp', evalCore, force', quote)
import LangPrelude hiding (force, lift)
import Syntax.Core (CoreTerm)
import Syntax.Core qualified as C
import Syntax.Term (Quantifier (..), Visibility (..))
import Syntax.Value as V
import TypeChecker.Backend hiding (ExType (..))

-- passing around topLevel like this is a bit ugly, perhaps unify should just take a Context?
unify :: TC es => IdMap Name_ Value -> Level -> Value -> Value -> Eff es ()
unify topLevel lvl lhsTy rhsTy = do
    lhs' <- force' lhsTy
    rhs' <- force' rhsTy
    match lhs' rhs'
  where
    match = \cases
        (Lambda _vis lhsClosure) (Lambda _vis2 rhsClosure) -> do
            lhsBody <- lhsClosure `app'` V.Var lvl
            rhsBody <- rhsClosure `app'` V.Var lvl
            unify topLevel (succ lvl) lhsBody rhsBody
        -- these two cases seem kinda redundant
        nonLambda (Lambda vis rhsClosure) -> do
            lhsBody <- evalApp' vis nonLambda (V.Var lvl)
            rhsBody <- rhsClosure `app'` V.Var lvl
            unify topLevel (succ lvl) lhsBody rhsBody
        (Lambda vis lhsClosure) nonLambda -> do
            lhsBody <- lhsClosure `app'` V.Var lvl
            rhsBody <- evalApp' vis nonLambda (V.Var lvl)
            unify topLevel (succ lvl) lhsBody rhsBody
        (TyCon lhs lhsArgs) (TyCon rhs rhsArgs) | lhs == rhs -> zipWithM_ (unify topLevel lvl) lhsArgs rhsArgs
        (Q Forall v _e closure) (Q Forall v2 _e2 closure2) | v == v2 -> do
            unify topLevel lvl closure.ty closure2.ty
            body <- closure `app'` Var lvl
            body2 <- closure2 `app'` Var lvl
            unify topLevel (succ lvl) body body2
        (Stuck (VarApp vlvl spine)) (Stuck (VarApp vlvl2 spine2)) | vlvl == vlvl2 -> do
            unifySpine topLevel lvl spine spine2
        (Stuck (UniVarApp uni spine)) ty -> solve topLevel lvl uni spine ty
        ty (Stuck (UniVarApp uni spine)) -> solve topLevel lvl uni spine ty
        (Stuck (Fn fn arg)) (Stuck (Fn fn2 arg2))
            | fn.name == fn2.name && length fn.captured == length fn2.captured -> do
                zipWithM_ (unify topLevel lvl) fn.captured fn2.captured
                unify topLevel lvl (Stuck arg) (Stuck arg2)
        lhs rhs -> do
            univars <- get @UniVars
            internalError' $ "cannot unify" <+> pretty (quote univars lvl lhs) <+> "with" <+> pretty (quote univars lvl rhs)

unifySpine :: TC es => IdMap Name_ Value -> Level -> Spine -> Spine -> Eff es ()
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
    { domain :: Level
    , codomain :: Level
    , renaming :: EnumMap Level Level
    }
    deriving (Show)

-- | add a variable to a partial renaming
lift :: PartialRenaming -> PartialRenaming
lift PartialRenaming{domain, codomain, renaming} =
    PartialRenaming
        { domain = succ domain
        , codomain = succ codomain
        , renaming = EMap.insert codomain domain renaming
        }

solve :: TC es => IdMap Name_ Value -> Level -> UniVar -> Spine -> Value -> Eff es ()
solve topLevel ctxLevel uni spine rhs = do
    pren <- invert ctxLevel spine
    rhs' <- rename uni pren rhs
    univars <- get @UniVars
    let env = ExtendedEnv{univars, topLevel, locals = []}
    let solution = evalCore env $ lambdas (reverse $ map fst spine) rhs'
    modify @UniVars $ EMap.insert uni $ Solved solution

-- | convert a spine to a partial renaming
invert :: TC es => Level -> Spine -> Eff es PartialRenaming
invert codomain spine = do
    (domain, renaming) <- go spine
    pure $ PartialRenaming{domain, codomain, renaming}
  where
    go [] = pure (Level 0, EMap.empty)
    go ((_, ty) : rest) = do
        (domain, renaming) <- go rest
        force' ty >>= \case
            Var vlvl | EMap.notMember vlvl renaming -> pure (succ domain, EMap.insert vlvl domain renaming)
            other -> internalError' $ "non-var in spine" <+> pretty other

rename :: TC es => UniVar -> PartialRenaming -> Value -> Eff es CoreTerm
rename uni = go
  where
    goSpine _ term [] = pure term
    goSpine pren term ((vis, ty) : spine) = C.App vis <$> goSpine pren term spine <*> go pren ty

    go pren ty =
        force' ty >>= \case
            Stuck (UniVarApp uni2 spine)
                | uni == uni2 -> internalError' "self-referential type"
                | otherwise -> goSpine pren (C.UniVar uni) spine
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
lambdas :: [Visibility] -> CoreTerm -> CoreTerm
lambdas = go 0
  where
    go :: Int -> [Visibility] -> CoreTerm -> CoreTerm
    go _ [] term = term
    go x (vis : vises) term = C.Lambda vis (Name' $ "x" <> show x) $ go (succ x) vises term
