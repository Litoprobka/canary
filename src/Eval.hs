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
import Data.HashMap.Strict qualified as HashMap
import Data.IdMap qualified as LMap
import Data.List ((!!))
import Data.Row (ExtRow (..), OpenName)
import Data.Row qualified as Row
import Data.Vector qualified as Vec
import Effectful.State.Static.Local (State, get)
import LangPrelude hiding (force)
import Prettyprinter (line)
import Syntax
import Syntax.Core (CaseWithDefault)
import Syntax.Core qualified as C
import Syntax.Elaborated qualified as D
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

-- a helper to make working with ExtendedEnv less verbose
-- honestly, I should probably just give in to lens

overLocals :: ([Value] -> [Value]) -> ExtendedEnv -> ExtendedEnv
overLocals f ExtendedEnv{..} = ExtendedEnv{locals = f locals, ..}

-- an orphan instance, since I don't want to merge 'Value.hs' and 'Eval.hs'
instance PrettyAnsi Value where
    prettyAnsi = prettyAnsi . quoteWhnf EMap.empty (Level 0)

deriving via (UnAnnotate Value) instance Pretty Value
deriving via (UnAnnotate Value) instance Show Value

data UnrollUniVars = NoUnroll | DeepUnroll UniVars

quoteWith
    :: (forall ty. Level -> Closure ty -> CoreTerm)
    -> (Level -> ValueEnv -> CaseWithDefault -> CaseWithDefault)
    -> UnrollUniVars
    -> Level
    -> Value
    -> CoreTerm
quoteWith quoteClosure quoteStuckCase unroll = go
  where
    go lvl = \case
        TyCon name args -> C.TyCon name $ (fmap . fmap) (go lvl) args
        Con con args -> C.Con con $ (fmap . fmap) (go lvl) args
        Lambda vis closure -> C.Lambda vis closure.var (go lvl closure.ty) $ quoteClosure lvl closure
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
        RecordAccess record field -> C.RecordAccess (quoteStuck lvl record) field
        Case arg env matches -> C.Case (quoteStuck lvl arg) (quoteStuckCase lvl env matches)
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
    go = quoteWith quoteClosure quoteStuckCase (DeepUnroll univars)

    quoteClosure :: Level -> Closure a -> CoreTerm
    quoteClosure lvl closure = go (succ lvl) $ app univars closure (Var lvl)

    quoteStuckCase :: Level -> ValueEnv -> CaseWithDefault -> CaseWithDefault
    quoteStuckCase lvl ValueEnv{..} = nfCase lvl ExtendedEnv{..}

-- | quote a value without reducing anything under lambdas
quoteWhnf :: UniVars -> Level -> Value -> CoreTerm
quoteWhnf univars = go
  where
    go = quoteWith quoteClosure quoteStuckCase (DeepUnroll univars)

    quoteStuckCase :: Level -> ValueEnv -> CaseWithDefault -> CaseWithDefault
    quoteStuckCase lvl env = substCaseWD lvl env.locals

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
        C.Lambda{vis, argName, argType, body} -> C.Lambda vis argName (subst lvl env argType) $ subst (succ lvl) (Var lvl : env) body
        C.App vis lhs rhs -> C.App vis (subst lvl env lhs) (subst lvl env rhs)
        C.Case arg casewd -> C.Case (subst lvl env arg) $ substCaseWD lvl env casewd
        C.Let name expr body -> C.Let name (subst lvl env expr) (subst (succ lvl) (Var lvl : env) body)
        C.RecordAccess record field -> C.RecordAccess (subst lvl env record) field
        C.Record row -> C.Record (fmap (subst lvl env) row)
        C.Row row -> C.Row (fmap (subst lvl env) row)
        C.Sigma vis lhs rhs -> C.Sigma vis (subst lvl env lhs) (subst lvl env rhs)
        C.Q q vis e var ty body -> C.Q q vis e var (subst lvl env ty) (subst (succ lvl) (Var lvl : env) body)
        C.ElabInsert core -> C.ElabInsert $ subst lvl env core
        C.UniVar uni -> case EMap.lookup uni univars of
            Just Solved{solution} -> go lvl solution
            _ -> C.UniVar uni
        pr@(C.AppPruning lhs pruning) -> substPruning env (subst lvl env lhs) pruning.getPruning
          where
            substPruning env lhs pruning = case (env, pruning) of
                ([], []) -> lhs
                (v : env, Just vis : pruning) -> C.App vis (substPruning env lhs pruning) (go lvl v)
                (_ : env, Nothing : pruning) -> substPruning env lhs pruning
                (env, pruning) ->
                    error $
                        show $
                            "[subst] pruning-env length mismatch ("
                                <> pretty (length pruning)
                                <+> "!="
                                <+> pretty (length env)
                                <> ")\nin the pruning spine"
                                <+> show (prettyDef pr)
    substCaseWD :: Level -> [Value] -> CaseWithDefault -> CaseWithDefault
    substCaseWD lvl env C.CaseWD{branches, def} =
        C.CaseWD
            { branches = substCase lvl env branches
            , def = second (subst (succ lvl) (Var lvl : env)) <$> def
            }

    substCase :: Level -> [Value] -> C.Case -> C.Case
    substCase lvl env = \case
        C.ConCase branches -> C.ConCase $ substBranch lvl env <$> branches
        C.TypeCase branches -> C.TypeCase $ substBranch lvl env <$> branches
        C.VariantCase branches -> C.VariantCase $ branches <&> second (subst (succ lvl) (Var lvl : env))
        C.LitCase branches -> C.LitCase $ second (subst lvl env) <$> branches

    -- in terms of the printed output, it might be cleaner to evaluate nested pattern matches,
    -- because pattern matching only reduces the size of the output
    -- however, to properly apply a pattern we'd have to evaluate the scrutinee, which is exactly what we were trying to avoid
    substBranch :: Level -> [Value] -> (CorePattern, CoreTerm) -> (CorePattern, CoreTerm)
    substBranch lvl env (pat, body) =
        let newLevel = lvl `incLevel` C.patternArity pat
            freeVars = Var <$> [pred newLevel, pred (pred newLevel) .. lvl]
         in (pat, subst newLevel (freeVars <> env) body)

evalM :: State UniVars :> es => ValueEnv -> CoreTerm -> Eff es Value
evalM ValueEnv{..} term = do
    univars <- get
    pure $ eval ExtendedEnv{..} term

eval :: ExtendedEnv -> CoreTerm -> Value
eval env@ExtendedEnv{..} = \case
    -- note that env.topLevel is a lazy IdMap, so we only force the outer structure here
    C.Name name -> LMap.lookupDefault (Stuck $ Opaque name []) name env.topLevel
    C.Var index
        | index.getIndex < length env.locals -> env.locals !! index.getIndex
        | otherwise -> error . show $ "index" <+> pretty index.getIndex <+> "out of scope of env@" <> pretty (length env.locals)
    C.TyCon name args -> TyCon name $ (fmap . fmap) (eval env) args
    C.Con name args -> Con name $ (fmap . fmap) (eval env) args
    C.Variant name arg -> Variant name (eval env arg)
    C.Lambda{vis, argName = var, argType, body} -> Lambda vis $ Closure{var, ty = eval env argType, env = ValueEnv{..}, body}
    C.App vis lhs rhs -> evalApp univars vis (eval env lhs) (eval env rhs)
    C.Case arg matches -> evalPatternMatch env (eval env arg) matches
    C.Let _name expr body -> eval (overLocals (eval env expr :) env) body
    C.Literal lit -> PrimValue lit
    C.RecordAccess record field -> evalRecordAccess (eval env record) field
    C.Record row -> Record $ eval env <$> row
    C.Sigma vis x y -> Sigma vis (eval env x) (eval env y)
    C.Q q vis e var ty body -> Q q vis e $ Closure{var, ty = eval env ty, env = ValueEnv{..}, body}
    C.ElabInsert core -> eval env core
    C.Row (NoExtRow row) -> Row (fmap (eval env) row) Nothing
    C.Row (ExtRow row ext) -> case eval env ext of
        Stuck stuck -> Row (fmap (eval env) row) (Just stuck)
        Row innerRow innerExt -> Row (fmap (eval env) row <> innerRow) innerExt
        nonRow -> error . show $ "[eval] non-row value in a row:" <+> pretty nonRow
    C.UniVar uni -> force univars (UniVar uni)
    pr@(C.AppPruning lhs pruning) -> evalAppPruning env.locals (eval env lhs) pruning.getPruning
      where
        evalAppPruning ls val pruning = case (ls, pruning) of
            ([], []) -> val
            (t : ls, Just vis : pruning) -> evalApp env.univars vis (evalAppPruning ls val pruning) t
            (_ : ls, Nothing : pruning) -> evalAppPruning ls val pruning
            (env, pruning) ->
                error $
                    show $
                        "[eval] pruning-env length mismatch ("
                            <> pretty (length pruning)
                            <+> "!="
                            <+> pretty (length env)
                            <> ")\nin the pruning spine"
                            <+> prettyDef pr

-- | evaluate a case expression
evalPatternMatch :: ExtendedEnv -> Value -> C.CaseWithDefault -> Value
evalPatternMatch ExtendedEnv{..} (Stuck stuck) branches = Stuck $ Case stuck ValueEnv{..} branches
evalPatternMatch env val casewd =
    fromMaybe
        (error $ show $ "[eval] pattern mismatch when matching" <+> prettyDef val <+> "with: <TODO: prettyprint standalone cases>")
        $ fmap (uncurry eval) (matchBranch env val casewd.branches)
            <|> fmap (eval (overLocals (val :) env) . snd) casewd.def

-- | try to match a value with a case expression branch, returning the new env and body expression
matchBranch :: ExtendedEnv -> Value -> C.Case -> Maybe (ExtendedEnv, CoreTerm)
matchBranch env = \cases
    (Con name args) (C.ConCase branches) -> do
        (_, branch) <- LMap.lookup name branches
        pure (catEnv args env, branch)
    (TyCon name args) (C.TypeCase branches) -> do
        (_, branch) <- LMap.lookup name branches
        pure (catEnv args env, branch)
    (Variant name arg) (C.VariantCase branches) -> do
        (_, branch) <- HashMap.lookup name branches
        pure (overLocals (arg :) env, branch)
    (PrimValue val) (C.LitCase branches) ->
        asum $ branches <&> \(lit, body) -> (env, body) <$ guard (val == lit)
    -- TODO: I don't remember whether matching against a literal introduces a new binding (and a new index)
    _ _ -> Nothing
  where
    catEnv :: Vector (a, Value) -> ExtendedEnv -> ExtendedEnv
    catEnv newVals = overLocals (reverse (map snd $ toList newVals) <>)

nf :: Level -> ExtendedEnv -> CoreTerm -> CoreTerm
nf lvl env term = quote env.univars lvl $ eval env term

whnf :: Level -> ExtendedEnv -> CoreTerm -> CoreTerm
whnf lvl env term = quoteWhnf env.univars lvl $ eval env term

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

evalRecordAccess :: Value -> OpenName -> Value
evalRecordAccess record field = case record of
    Record row -> case Row.lookup field row of
        Just val -> val
        Nothing -> error . show $ "field" <+> pretty field <+> "not found in" <+> pretty record
    Stuck stuck -> Stuck (RecordAccess stuck field)
    nonRecord -> error . show $ "expected a record in record access expression: " <+> pretty nonRecord

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
    Stuck (RecordAccess record field) -> case force univars (Stuck record) of
        Stuck stillStuck -> Stuck (RecordAccess stillStuck field)
        noLongerStuck -> force univars $ evalRecordAccess noLongerStuck field
    Stuck (Case arg env@ValueEnv{..} matches) -> case force univars (Stuck arg) of
        Stuck stillStuck -> Stuck (Case stillStuck env matches)
        noLongerStuck -> evalPatternMatch ExtendedEnv{..} noLongerStuck matches
    other -> other

applySpine :: UniVars -> Value -> Spine -> Value
applySpine !univars = foldr (\(vis, arg) acc -> evalApp univars vis acc arg)

app :: UniVars -> Closure ty -> Value -> Value
app univars Closure{env = ValueEnv{..}, body} arg = eval (overLocals (arg :) $ ExtendedEnv{..}) body

appM :: State UniVars :> es => Closure ty -> Value -> Eff es Value
appM closure arg = do
    univars <- get @UniVars
    pure $ app univars closure arg

nfCase :: Level -> ExtendedEnv -> C.CaseWithDefault -> C.CaseWithDefault
nfCase lvl env C.CaseWD{branches, def} =
    C.CaseWD
        { branches = case branches of
            C.ConCase b -> C.ConCase $ nfCaseBranch lvl env <$> b
            C.TypeCase b -> C.TypeCase $ nfCaseBranch lvl env <$> b
            C.VariantCase b -> C.VariantCase $ b <&> second (nf (succ lvl) (overLocals (Var lvl :) env))
            C.LitCase b -> C.LitCase $ second (nf lvl env) <$> b
        , def = (fmap . second) (nf (succ lvl) (overLocals (Var lvl :) env)) def
        }
  where
    nfCaseBranch :: Level -> ExtendedEnv -> (CorePattern, CoreTerm) -> (CorePattern, CoreTerm)
    nfCaseBranch lvl env (pat, body) =
        let newLevel = lvl `incLevel` C.patternArity pat
            freeVars = Var <$> [pred newLevel, pred (pred newLevel) .. lvl]
         in (pat, nf newLevel (overLocals (freeVars <>) env) body)

modifyEnv
    :: ValueEnv
    -> [EDeclaration]
    -> Eff es ValueEnv
modifyEnv ValueEnv{..} decls = do
    desugared <- LMap.fromList <$> foldMapM collectBindings decls
    let newEnv = ExtendedEnv{topLevel = newTopLevel, univars = EMap.empty, locals = []}
        newTopLevel = fmap (either id (eval newEnv)) desugared <> topLevel
    pure ValueEnv{topLevel = newTopLevel, ..}
  where
    collectBindings :: EDeclaration -> Eff es [(Name_, Either Value CoreTerm)]
    collectBindings decl = case decl of
        D.ValueD name body -> pure [(name, Right body)]
        -- todo: value constructors have to be in scope by the time we typecheck definitions that depend on them (say, GADTs)
        -- the easiest way is to just apply `typecheck` and `modifyEnv` declaration-by-declaration
        D.TypeD _ constrs -> pure $ fmap mkConstr constrs
        D.SignatureD{} -> pure mempty

    mkConstr (name, vises) = (name, Left $ mkConLambda vises (C.Con name))

-- todo: [Visibility] -> Name -> Value
mkConLambda :: Vector (Visibility, CoreType) -> (Vector (Visibility, CoreTerm) -> CoreTerm) -> Value
mkConLambda args con = eval emptyEnv lambdas
  where
    n = Vec.length args
    namedArgs = zipWith (\(vis, ty) i -> (vis, Name' $ "x" <> show i, ty)) (toList args) [1 .. n]
    lambdas = foldr (\(vis, var, ty) -> C.Lambda vis var ty) body namedArgs
    body = con $ Vec.zipWith (\(vis, _) ix -> (vis, C.Var (Index ix))) args (Vec.fromListN n [n - 1, n - 2 .. 0])
    emptyEnv = ExtendedEnv{univars = EMap.empty, topLevel = LMap.empty, locals = []}

mkTyCon :: CoreType -> Name_ -> Value
mkTyCon ty name = mkConLambda (C.functionTypeArity ty) (C.TyCon name)
