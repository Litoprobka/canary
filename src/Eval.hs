{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE RecordWildCards #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -Wno-partial-fields #-}

module Eval where

import Common (
    Index (..),
    Level (..),
    Name,
    Name_,
    PrettyAnsi (..),
    SimpleName_ (..),
    UnAnnotate (..),
    UniVar,
    levelToIndex,
    prettyDef,
    unLoc,
 )

-- IdMap is currently lazy anyway, but it's up to change

import Data.EnumMap.Lazy qualified as EMap
import Data.List ((!!))
import Desugar (desugar)
import Effectful.State.Static.Local (State, get)
import IdMap qualified as LMap
import LangPrelude hiding (force)
import Prettyprinter (line, vsep)
import Syntax
import Syntax.Core qualified as C
import Syntax.Elaborated qualified as D
import Syntax.Elaborated qualified as E
import Syntax.Value as Reexport

data UniVarState
    = Solved {solution :: Value, ty :: ~VType}
    | Unsolved {ty :: ~VType}
    deriving (Show)
type UniVars = EnumMap UniVar UniVarState

data ExtendedEnv = ExtendedEnv
    { locals :: [Value]
    , topLevel :: IdMap Name_ Value
    , univars :: UniVars
    }

-- an orphan instance, since I don't want to merge 'Value.hs' and 'Eval.hs'
instance PrettyAnsi Value where
    prettyAnsi opts = prettyAnsi opts . quote EMap.empty (Level 0)

deriving via (UnAnnotate Value) instance Pretty Value
deriving via (UnAnnotate Value) instance Show Value

quote :: UniVars -> Level -> Value -> CoreTerm
quote univars = go
  where
    go lvl = \case
        TyCon name args -> foldl' (C.App Visible) (C.TyCon name) $ fmap (quote univars lvl) args
        Con con args -> C.Con con $ fmap (quote univars lvl) args
        Lambda vis closure -> C.Lambda vis closure.var $ quoteClosure univars lvl closure
        PrimFunction PrimFunc{name, captured} ->
            -- captured names are stored as a stack, i.e. backwards, so we fold right rather than left here
            foldr (\arg acc -> C.App Visible acc (go lvl arg)) (C.Name name) captured
        Record vals -> C.Record $ fmap (go lvl) vals
        Sigma x y -> C.Sigma (go lvl x) (go lvl y)
        Variant name val -> C.App Visible (C.Variant name) (go lvl val)
        PrimValue lit -> C.Literal lit
        Q q v e closure -> C.Q q v e closure.var (go lvl closure.ty) $ quoteClosure univars lvl closure
        VariantT row -> C.VariantT $ fmap (go lvl) row
        RecordT row -> C.RecordT $ fmap (go lvl) row
        Stuck stuck -> quoteStuck lvl stuck

    -- for now, all quote applications are explicit
    quoteStuck :: Level -> Stuck -> CoreTerm
    quoteStuck lvl = \case
        VarApp varLvl spine -> quoteSpine (C.Var $ levelToIndex lvl varLvl) spine
        UniVarApp uni spine -> quoteSpine (C.UniVar uni) spine
        Fn fn acc -> C.App Visible (go lvl $ PrimFunction fn) (quoteStuck lvl acc)
        Case arg matches -> C.Case (quoteStuck lvl arg) (fmap quotePatternClosure matches)
      where
        quoteSpine = foldr (\(vis, arg) acc -> C.App vis acc (quote univars lvl arg))
        quotePatternClosure PatternClosure{pat, env, body} =
            let ValueEnv{..} = env
                freeVars = Var <$> [pred newLevel .. lvl]
                newLevel = Level $ lvl.getLevel + C.patternArity pat
                bodyV = evalCore ExtendedEnv{locals = freeVars <> locals, ..} body
             in (pat, quote univars newLevel bodyV)

evalCore :: ExtendedEnv -> CoreTerm -> Value
evalCore env@ExtendedEnv{..} = \case
    -- note that env.topLevel is a lazy IdMap, so we only force the outer structure here
    C.Name name -> LMap.lookupDefault (error . show $ "unbound top-level name" <+> pretty name) (unLoc name) env.topLevel
    C.Var index -> env.locals !! index.getIndex
    C.TyCon name -> Type name
    C.Con name args -> Con name $ map (evalCore env) args
    C.Lambda vis var body -> Lambda vis $ Closure{var, ty = (), env = ValueEnv{..}, body}
    C.App _vis (C.Variant name) arg -> Variant name $ evalCore env arg -- this is a bit of an ugly case
    C.App vis lhs rhs -> evalApp univars vis (evalCore env lhs) (evalCore env rhs)
    C.Case arg matches -> case evalCore env arg of
        Stuck stuck -> Stuck $ Case stuck (mkStuckBranches matches)
        val ->
            fromMaybe
                (error $ show $ "pattern mismatch when matching" <+> prettyDef val <+> "with:" <> line <> vsep (map (prettyDef . fst) matches))
                . asum
                $ matches <&> \(pat, body) -> evalCore <$> matchCore env pat val <*> pure body
    C.Let _name expr body -> evalCore (ExtendedEnv{locals = evalCore env expr : env.locals, ..}) body
    C.Literal lit -> PrimValue lit
    C.Record row -> Record $ evalCore env <$> row
    C.Sigma x y -> Sigma (evalCore env x) (evalCore env y)
    C.Variant name ->
        Lambda Visible $ Closure{var = Name' "x", ty = (), env = ValueEnv{..}, body = C.App Visible (C.Variant name) (C.Var (Index 0))}
    C.Q q vis e var ty body -> Q q vis e $ Closure{var, ty = evalCore env ty, env = ValueEnv{..}, body}
    C.VariantT row -> VariantT $ evalCore env <$> row
    C.RecordT row -> RecordT $ evalCore env <$> row
    C.UniVar uni -> force univars (UniVar uni)
    C.AppPruning lhs pruning -> evalAppPruning env.locals (evalCore env lhs) pruning.getPruning
  where
    mkStuckBranches :: [(CorePattern, CoreTerm)] -> [PatternClosure ()]
    mkStuckBranches = map \(pat, body) -> PatternClosure{pat, ty = (), env = ValueEnv{..}, body}

    evalAppPruning ls val pruning = case (ls, pruning) of
        ([], []) -> val
        (t : ls', Just vis : rest) -> evalApp env.univars vis (evalAppPruning ls' val rest) t
        (_ : ls', Nothing : rest) -> evalAppPruning ls' val rest
        _ -> error "pruning-env length mismatch"

nf :: Level -> ExtendedEnv -> CoreTerm -> CoreTerm
nf lvl env term = quote env.univars lvl $ evalCore env term

evalAppM :: State UniVars :> es => Visibility -> Value -> Value -> Eff es Value
evalAppM vis lhs rhs = do
    univars <- get @UniVars
    pure $ evalApp univars vis lhs rhs

evalApp :: UniVars -> Visibility -> Value -> Value -> Value
evalApp univars vis = \cases
    (Lambda vis2 closure) arg | vis == vis2 -> app univars closure arg
    (Lambda vis2 _) _ -> error $ "visibility mismatch " <> show vis <> " != " <> show vis2
    -- this is slightly janky, but I'm not sure whether I want to represent type constructors as lambdas yet
    (TyCon name args) arg -> TyCon name (args <> [arg])
    (PrimFunction fn) (Stuck stuck) -> Stuck $ Fn fn stuck
    (PrimFunction PrimFunc{remaining = 1, captured, f}) arg -> f (arg :| captured)
    (PrimFunction PrimFunc{name, remaining, captured, f}) arg -> PrimFunction PrimFunc{name, remaining = pred remaining, captured = arg : captured, f}
    (Stuck (VarApp lvl spine)) arg -> Stuck $ VarApp lvl ((vis, arg) : spine)
    (Stuck (UniVarApp uni spine)) arg -> Stuck $ UniVarApp uni ((vis, arg) : spine)
    nonFunc arg -> error . show $ "attempted to apply" <+> pretty nonFunc <+> "to" <+> pretty arg

forceM :: State UniVars :> es => Value -> Eff es Value
forceM val = do
    univars <- get @UniVars
    pure $ force univars val

-- try to evaluate an expression that was previously stuck on an unsolved skolem
force :: UniVars -> Value -> Value
force !univars = \case
    Stuck (UniVarApp uni spine) -> case EMap.lookup uni univars of
        -- an out of scope univar indicates a bug, but a non-fatal one
        Nothing -> Stuck $ UniVarApp uni spine
        Just Unsolved{} -> Stuck $ UniVarApp uni spine
        Just (Solved{solution}) -> force univars $ applySpine solution spine
    Stuck (Fn fn arg) -> case force univars (Stuck arg) of
        Stuck stillStuck -> Stuck (Fn fn stillStuck)
        noLongerStuck -> evalApp univars Visible (PrimFunction fn) noLongerStuck
    Stuck (Case arg matches) -> case force univars (Stuck arg) of
        Stuck stillStuck -> Stuck (Case stillStuck matches)
        noLongerStuck -> fromMaybe (error "couldn't match") $ asum $ fmap (\closure -> tryApplyPatternClosure univars closure noLongerStuck) matches
    other -> other
  where
    applySpine = foldr (\(vis, arg) acc -> evalApp univars vis acc arg)

app :: UniVars -> Closure ty -> Value -> Value
app univars Closure{env = ValueEnv{..}, body} arg = evalCore (ExtendedEnv{locals = arg : locals, ..}) body

appM :: State UniVars :> es => Closure ty -> Value -> Eff es Value
appM closure arg = do
    univars <- get @UniVars
    pure $ app univars closure arg

quoteClosure :: UniVars -> Level -> Closure a -> CoreTerm
quoteClosure univars lvl closure = quote univars (succ lvl) $ app univars closure (Var lvl)

-- | try to apply a pattern to a value, updating the given value env
matchCore :: ExtendedEnv -> CorePattern -> Value -> Maybe ExtendedEnv
matchCore ExtendedEnv{..} = \cases
    C.VarP{} val -> Just $ ExtendedEnv{locals = val : locals, ..}
    C.WildcardP{} val -> Just ExtendedEnv{locals = val : locals, ..}
    (C.ConstructorP pname _) (Con name args)
        | pname == name ->
            -- since locals is a SnocList, we have to reverse args before appending
            Just ExtendedEnv{locals = reverse args <> locals, ..}
    (C.VariantP pname _) (Variant name val)
        | pname == name -> Just ExtendedEnv{locals = val : locals, ..}
    (C.RecordP _varRow) (Record _row) -> error "todo: row matching (must preserve original field order)"
    -- let (pairs, _, _) = Row.zipRows varRow row
    -- in Just $ env{locals = foldl' (flip $ uncurry LMap.insert) env.values pairs}
    (C.SigmaP _ _) (Sigma lhs rhs) -> Just ExtendedEnv{locals = rhs : lhs : locals, ..}
    (C.LiteralP lit) (PrimValue val) -> ExtendedEnv{..} <$ guard (lit == val)
    _ _ -> Nothing

tryApplyPatternClosure :: UniVars -> PatternClosure ty -> Value -> Maybe Value
tryApplyPatternClosure univars PatternClosure{pat, env = ValueEnv{..}, body} arg = do
    newEnv <- matchCore ExtendedEnv{..} pat arg
    pure $ evalCore newEnv body

eval :: ExtendedEnv -> ETerm -> Value
eval env term = evalCore env $ desugar term

modifyEnv
    :: ValueEnv
    -> [EDeclaration]
    -> Eff es ValueEnv
modifyEnv ValueEnv{..} decls = do
    desugared <- (fmap . fmap) desugar . LMap.fromList <$> foldMapM collectBindings decls
    let newEnv = ExtendedEnv{topLevel = newTopLevel, univars = EMap.empty, locals = []}
        newTopLevel = fmap (either id (evalCore newEnv)) desugared <> topLevel
    pure ValueEnv{topLevel = newTopLevel, ..}
  where
    collectBindings :: EDeclaration -> Eff es [(Name_, Either Value ETerm)]
    collectBindings decl = case decl of
        D.ValueD (E.ValueB name body) -> pure [(unLoc name, Right body)]
        D.ValueD (E.FunctionB name args body) -> pure [(unLoc name, Right $ foldr (uncurry E.Lambda) body args)]
        -- todo: value constructors have to be in scope by the time we typecheck definitions that depend on them (say, GADTs)
        -- the easiest way is to just apply `typecheck` and `modifyEnv` declaration-by-declaration
        D.TypeD _ constrs -> pure $ fmap mkConstr constrs
        D.SignatureD{} -> pure mempty

    mkConstr (name, count) = (unLoc name, Left $ mkConLambda count name)

-- todo: [Visibility] -> Name -> Value
mkConLambda :: Int -> Name -> Value
mkConLambda n con = evalCore emptyEnv lambdas
  where
    names = fmap (\i -> Name' $ "x" <> show i) [1 .. n]
    lambdas = foldr (C.Lambda Visible) body names
    body = C.Con con $ map (C.Var . Index) [n - 1, n - 2 .. 0]
    emptyEnv = ExtendedEnv{univars = EMap.empty, topLevel = LMap.empty, locals = []}
