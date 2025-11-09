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
    Id,
    Index (..),
    Level (..),
    Name_,
    PrettyAnsi (..),
    SimpleName_ (..),
    UnAnnotate (..),
    UniVar,
    incLevel,
    levelToIndex,
    prettyDef,
 )

-- IdMap is currently lazy anyway, but it's up to change

import Data.EnumMap.Lazy qualified as EMap
import Data.IdMap qualified as LMap
import Data.List ((!!))
import Data.Row (ExtRow (..))
import Data.Row qualified as Row
import Data.Vector qualified as Vec
import Desugar (desugar)
import Effectful.State.Static.Local (State, get)
import LangPrelude hiding (force)
import Prettyprinter (line, vsep)
import Syntax
import Syntax.Core qualified as C
import Syntax.Elaborated qualified as D
import Syntax.Elaborated qualified as E
import Syntax.Value as Reexport

data UniVarState
    = Solved {solution :: Value, ty :: ~VType}
    | Unsolved {blocks :: EnumSet Postponed, ty :: ~VType}
    deriving (Show)
type UniVars = EnumMap UniVar UniVarState

newtype Postponed = Postponed Id deriving (Eq, Show, Enum)
instance Pretty Postponed where
    pretty (Postponed id') = "#" <> pretty id'

data PostponedEntry = PostponedEntry Level Value Value

type Postponings = EnumMap Postponed PostponedEntry

data ExtendedEnv = ExtendedEnv
    { locals :: [Value]
    , topLevel :: IdMap Name_ Value
    , univars :: UniVars
    }

-- an orphan instance, since I don't want to merge 'Value.hs' and 'Eval.hs'
instance PrettyAnsi Value where
    prettyAnsi = prettyAnsi . quoteWhnf EMap.empty (Level 0)

deriving via (UnAnnotate Value) instance Pretty Value
deriving via (UnAnnotate Value) instance Show Value

data UnrollUniVars = NoUnroll | DeepUnroll UniVars

quoteWith
    :: (forall ty. Level -> Closure ty -> CoreTerm)
    -> (Level -> PatternClosure () -> (CorePattern, CoreTerm))
    -> UnrollUniVars
    -> Level
    -> Value
    -> CoreTerm
quoteWith quoteClosure quotePatternClosure unroll = go
  where
    go lvl = \case
        TyCon name args -> C.TyCon name $ (fmap . fmap) (go lvl) args
        Con con args -> C.Con con $ (fmap . fmap) (go lvl) args
        Lambda vis closure -> C.Lambda vis closure.var $ quoteClosure lvl closure
        PrimFunction PrimFunc{name, captured} ->
            -- captured names are stored as a stack, i.e. backwards, so we fold right rather than left here
            foldr (\arg acc -> C.App Visible acc (go lvl arg)) (C.Name name) captured
        Record vals -> C.Record $ fmap (go lvl) vals
        Sigma vis x y -> C.Sigma vis (go lvl x) (go lvl y)
        Variant name val -> C.Variant name (go lvl val)
        PrimValue lit -> C.Literal lit
        Q q v e closure -> C.Q q v e closure.var (go lvl closure.ty) $ quoteClosure lvl closure
        Row row Nothing -> C.Row $ fmap (go lvl) (NoExtRow row)
        Row row (Just ext) -> C.Row $ fmap (go lvl) (ExtRow row (Stuck ext))
        Stuck stuck -> quoteStuck lvl stuck

    quoteStuck :: Level -> Stuck -> CoreTerm
    quoteStuck lvl = \case
        VarApp varLvl spine -> quoteSpine (C.Var $ levelToIndex lvl varLvl) spine
        UniVarApp uni spine -> case unroll of
            NoUnroll -> quoteSpine (C.UniVar uni) spine
            DeepUnroll univars -> case force univars $ Stuck $ UniVarApp uni spine of
                -- if we get a stuck univar even after forcing, then the univar is unsolved
                Stuck (UniVarApp uni spine) -> quoteSpine (C.UniVar uni) spine
                nonStuck -> go lvl nonStuck
        Opaque name spine -> quoteSpine (C.Name name) spine
        Fn fn acc -> C.App Visible (go lvl $ PrimFunction fn) (quoteStuck lvl acc)
        Case arg matches -> C.Case (quoteStuck lvl arg) (fmap (quotePatternClosure lvl) matches)
      where
        quoteSpine = foldr (\(vis, arg) acc -> C.App vis acc (go lvl arg))

quoteM :: State UniVars :> es => Level -> Value -> Eff es CoreTerm
quoteM lvl value = do
    univars <- get
    pure $ quote univars lvl value

quoteWhnfM :: State UniVars :> es => Level -> Value -> Eff es CoreTerm
quoteWhnfM lvl value = do
    univars <- get
    pure $ quoteWhnf univars lvl value

quote :: UniVars -> Level -> Value -> CoreTerm
quote univars = go
  where
    go = quoteWith quoteClosure quotePatternClosure (DeepUnroll univars)

    quoteClosure :: Level -> Closure a -> CoreTerm
    quoteClosure lvl closure = go (succ lvl) $ app univars closure (Var lvl)

    quotePatternClosure :: Level -> PatternClosure a -> (CorePattern, CoreTerm)
    quotePatternClosure lvl closure =
        let (bodyV, newLevel) = skolemizePatternClosure univars lvl closure
         in (closure.pat, go newLevel bodyV)

-- | quote a value without reducing anything under lambdas
quoteWhnf :: UniVars -> Level -> Value -> CoreTerm
quoteWhnf univars = go
  where
    go = quoteWith quoteClosure quotePatternClosure (DeepUnroll univars)

    -- we can't reuse `skolemizePatternClosure`, because it calls `evalCore` inside. Meh.
    quotePatternClosure lvl closure = (closure.pat, subst newLevel env closure.body)
      where
        env = freeVars <> closure.env.locals
        freeVars = Var <$> [pred newLevel, pred (pred newLevel) .. lvl]
        newLevel = lvl `incLevel` C.patternArity closure.pat

    quoteClosure lvl Closure{env, body} = subst (succ lvl) (Var lvl : env.locals) body

    -- substitute known variables without reducing anything
    subst :: Level -> [Value] -> CoreTerm -> CoreTerm
    subst lvl env = \case
        C.Name name -> C.Name name
        C.Literal lit -> C.Literal lit
        C.Var index -> go lvl $ env !! index.getIndex
        C.TyCon name args -> C.TyCon name $ (fmap . fmap) (subst lvl env) args
        C.Con name args -> C.Con name $ (fmap . fmap) (subst lvl env) args
        C.Variant name arg -> C.Variant name $ subst lvl env arg
        C.Lambda vis var body -> C.Lambda vis var $ subst (succ lvl) (Var lvl : env) body
        C.App vis lhs rhs -> C.App vis (subst lvl env lhs) (subst lvl env rhs)
        C.Case arg branches -> C.Case (subst lvl env arg) $ fmap (substBranch lvl env) branches
        C.Let name expr body -> C.Let name (subst lvl env expr) (subst (succ lvl) (Var lvl : env) body)
        C.Record row -> C.Record (fmap (subst lvl env) row)
        C.Row row -> C.Row (fmap (subst lvl env) row)
        C.Sigma vis lhs rhs -> C.Sigma vis (subst lvl env lhs) (subst lvl env rhs)
        C.Q q vis e var ty body -> C.Q q vis e var (subst lvl env ty) (subst (succ lvl) (Var lvl : env) body)
        C.UniVar uni -> case EMap.lookup uni univars of
            Just Solved{solution} -> go lvl solution
            _ -> C.UniVar uni
        C.AppPruning lhs pruning -> substPruning env (subst lvl env lhs) pruning.getPruning
      where
        substPruning env lhs pruning = case (env, pruning) of
            ([], []) -> lhs
            (v : env, Just vis : pruning) -> C.App vis (substPruning env lhs pruning) (go lvl v)
            (_ : env, Nothing : pruning) -> substPruning env lhs pruning
            (env, pruning) -> error $ "[subst] pruning-env length mismatch (" <> show (length pruning) <> " != " <> show (length env) <> ")"

    -- in terms of the printed output, it might be cleaner to evaluate nested pattern matches,
    -- because pattern matching only reduces the size of the output
    -- however, to properly apply a pattern we'd have to evaluate the scrutinee, which is exactly what we were trying to avoid
    substBranch :: Level -> [Value] -> (CorePattern, CoreTerm) -> (CorePattern, CoreTerm)
    substBranch lvl env (pat, body) =
        let diff = C.patternArity pat
            newLevel = lvl `incLevel` diff
            freeVars = Var <$> [pred newLevel, pred (pred newLevel) .. lvl]
         in (pat, subst newLevel (freeVars <> env) body)

evalCore :: ExtendedEnv -> CoreTerm -> Value
evalCore env@ExtendedEnv{..} = \case
    -- note that env.topLevel is a lazy IdMap, so we only force the outer structure here
    C.Name name -> LMap.lookupDefault (Stuck $ Opaque name []) name env.topLevel
    C.Var index
        | index.getIndex < length env.locals -> env.locals !! index.getIndex
        | otherwise -> error . show $ "index" <+> pretty index.getIndex <+> "out of scope of env@" <> pretty (length env.locals)
    C.TyCon name args -> TyCon name $ (fmap . fmap) (evalCore env) args
    C.Con name args -> Con name $ (fmap . fmap) (evalCore env) args
    C.Variant name arg -> Variant name (evalCore env arg)
    C.Lambda vis var body -> Lambda vis $ Closure{var, ty = (), env = ValueEnv{..}, body}
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
    C.Sigma vis x y -> Sigma vis (evalCore env x) (evalCore env y)
    C.Q q vis e var ty body -> Q q vis e $ Closure{var, ty = evalCore env ty, env = ValueEnv{..}, body}
    C.Row (NoExtRow row) -> Row (fmap (evalCore env) row) Nothing
    C.Row (ExtRow row ext) -> case evalCore env ext of
        Stuck stuck -> Row (fmap (evalCore env) row) (Just stuck)
        Row innerRow innerExt -> Row (fmap (evalCore env) row <> innerRow) innerExt
        nonRow -> error . show $ "[eval] non-row value in a row:" <+> pretty nonRow
    C.UniVar uni -> force univars (UniVar uni)
    C.AppPruning lhs pruning -> evalAppPruning env.locals (evalCore env lhs) pruning.getPruning
  where
    mkStuckBranches :: [(CorePattern, CoreTerm)] -> [PatternClosure ()]
    mkStuckBranches = map \(pat, body) -> PatternClosure{pat, ty = (), env = ValueEnv{..}, body}

    evalAppPruning ls val pruning = case (ls, pruning) of
        ([], []) -> val
        (t : ls, Just vis : pruning) -> evalApp env.univars vis (evalAppPruning ls val pruning) t
        (_ : ls, Nothing : pruning) -> evalAppPruning ls val pruning
        (env, pruning) -> error $ "[eval] pruning-env length mismatch (" <> show (length pruning) <> " != " <> show (length env) <> ")"

nf :: Level -> ExtendedEnv -> CoreTerm -> CoreTerm
nf lvl env term = quote env.univars lvl $ evalCore env term

whnf :: Level -> ExtendedEnv -> CoreTerm -> CoreTerm
whnf lvl env term = quoteWhnf env.univars lvl $ evalCore env term

evalAppM :: State UniVars :> es => Visibility -> Value -> Value -> Eff es Value
evalAppM vis lhs rhs = do
    univars <- get @UniVars
    pure $ evalApp univars vis lhs rhs

evalApp :: UniVars -> Visibility -> Value -> Value -> Value
evalApp univars vis = \cases
    (Lambda vis2 closure) arg | vis == vis2 -> app univars closure arg
    lhs@(Lambda vis2 _) arg ->
        error . show $
            "[eval] visibility mismatch "
                <> show vis
                <> " != "
                <> show vis2
                <+> "when applying"
                <> line
                <> pretty lhs
                <> line
                <> "to"
                <> line
                <> pretty arg
    -- this is potentially problematic. primitive functions shouldn't accept anything
    -- that contains even a nested stuck term, e.g. 'Cons x []' where 'x' is stuck
    (PrimFunction fn) (Stuck stuck) -> Stuck $ Fn fn stuck
    (PrimFunction PrimFunc{remaining = 1, captured, f}) arg -> f (arg :| captured)
    (PrimFunction PrimFunc{name, remaining, captured, f}) arg -> PrimFunction PrimFunc{name, remaining = pred remaining, captured = arg : captured, f}
    (Stuck (Opaque name spine)) arg -> Stuck $ Opaque name ((vis, arg) : spine)
    (Stuck (VarApp lvl spine)) arg -> Stuck $ VarApp lvl ((vis, arg) : spine)
    (Stuck (UniVarApp uni spine)) arg -> Stuck $ UniVarApp uni ((vis, arg) : spine)
    -- todo: seems like this would error on primitive functions with multiple stuck arguments
    nonFunc arg -> error . show $ "attempted to apply" <+> pretty nonFunc <+> "to" <+> pretty arg

forceM :: State UniVars :> es => Value -> Eff es Value
forceM val = do
    univars <- get @UniVars
    pure $ force univars val

-- try to evaluate an expression that was previously stuck on a unification variable
force :: UniVars -> Value -> Value
force !univars = \case
    Row row Nothing -> Row row Nothing
    Row row (Just ext)
        | Row.isEmpty row -> force univars $ Stuck ext
        | otherwise -> case force univars (Stuck ext) of
            Stuck stillStuck -> Row row (Just stillStuck)
            (Row innerRow innerExt) -> force univars $ Row (row <> innerRow) innerExt
            nonRow -> error . show $ "[eval] non-row value in a row:" <+> pretty nonRow
    RecordType row -> RecordType $ force univars row
    VariantType row -> VariantType $ force univars row
    Stuck (UniVarApp uni spine) -> case EMap.lookup uni univars of
        -- an out of scope univar indicates a bug, but a non-fatal one
        Nothing -> Stuck $ UniVarApp uni spine
        Just Unsolved{} -> Stuck $ UniVarApp uni spine
        Just (Solved{solution}) -> force univars $ applySpine univars solution spine
    Stuck (Fn fn arg) -> case force univars (Stuck arg) of
        Stuck stillStuck -> Stuck (Fn fn stillStuck)
        noLongerStuck -> force univars $ evalApp univars Visible (PrimFunction fn) noLongerStuck
    Stuck (Case arg matches) -> case force univars (Stuck arg) of
        Stuck stillStuck -> Stuck (Case stillStuck matches)
        noLongerStuck -> fromMaybe (error "couldn't match") $ asum $ fmap (\closure -> tryApplyPatternClosure univars closure noLongerStuck) matches
    other -> other

applySpine :: UniVars -> Value -> Spine -> Value
applySpine !univars = foldr (\(vis, arg) acc -> evalApp univars vis acc arg)

app :: UniVars -> Closure ty -> Value -> Value
app univars Closure{env = ValueEnv{..}, body} arg = evalCore (ExtendedEnv{locals = arg : locals, ..}) body

appM :: State UniVars :> es => Closure ty -> Value -> Eff es Value
appM closure arg = do
    univars <- get @UniVars
    pure $ app univars closure arg

-- | convert a pattern closure to a value with free variables
skolemizePatternClosure :: UniVars -> Level -> PatternClosure a -> (Value, Level)
skolemizePatternClosure univars level closure = (evalCore env closure.body, newLevel)
  where
    ValueEnv{..} = closure.env
    env = ExtendedEnv{locals = freeVars <> locals, ..}
    freeVars = Var <$> [pred newLevel, pred (pred newLevel) .. level]
    newLevel = level `incLevel` C.patternArity closure.pat

-- | try to apply a pattern to a value, updating the given value env
matchCore :: ExtendedEnv -> CorePattern -> Value -> Maybe ExtendedEnv
matchCore ExtendedEnv{..} = \cases
    C.VarP{} val -> Just $ ExtendedEnv{locals = val : locals, ..}
    (C.ConstructorP pname _) (Con name args)
        | pname == name ->
            -- since locals is a SnocList, we have to reverse args before appending
            Just ExtendedEnv{locals = reverse (map snd $ toList args) <> locals, ..}
    (C.TypeP pname _) (TyCon name args)
        | pname == name -> Just ExtendedEnv{locals = reverse (map snd $ toList args) <> locals, ..}
    (C.VariantP pname _) (Variant name val)
        | pname == name -> Just ExtendedEnv{locals = val : locals, ..}
    (C.RecordP vars) (Record row) ->
        let takeField' field = fromMaybe (error "missing field in row match") . Row.takeField field
            (values, _) = foldl' (\(acc, row) (field, _) -> first (: acc) $ takeField' field row) ([], row) vars
         in Just ExtendedEnv{locals = values <> locals, ..}
    C.SigmaP{} (Sigma _ lhs rhs) -> Just ExtendedEnv{locals = rhs : lhs : locals, ..}
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
        D.ValueD (E.ValueB name body) -> pure [(name, Right body)]
        D.ValueD (E.FunctionB name args body) -> pure [(name, Right $ foldr (uncurry E.Lambda) body args)]
        -- todo: value constructors have to be in scope by the time we typecheck definitions that depend on them (say, GADTs)
        -- the easiest way is to just apply `typecheck` and `modifyEnv` declaration-by-declaration
        D.TypeD _ constrs -> pure $ fmap mkConstr constrs
        D.SignatureD{} -> pure mempty

    mkConstr (name, vises) = (name, Left $ mkConLambda vises (C.Con name))

-- todo: [Visibility] -> Name -> Value
mkConLambda :: Vector Visibility -> (Vector (Visibility, CoreTerm) -> CoreTerm) -> Value
mkConLambda vises con = evalCore emptyEnv lambdas
  where
    n = Vec.length vises
    names = zipWith (\vis i -> (vis, Name' $ "x" <> show i)) (toList vises) [1 .. n]
    lambdas = foldr (uncurry C.Lambda) body names
    body = con $ Vec.zipWith (\vis ix -> (vis, C.Var (Index ix))) vises (Vec.fromListN n [n - 1, n - 2 .. 0])
    emptyEnv = ExtendedEnv{univars = EMap.empty, topLevel = LMap.empty, locals = []}

mkTyCon :: CoreType -> Name_ -> Value
mkTyCon ty name = mkConLambda (C.functionTypeArity ty) (C.TyCon name)
