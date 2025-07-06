{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE RecordWildCards #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Eval (
    evalCore,
    quote,
    module Reexport,
    desugar,
    force,
    eval,
    modifyEnv,
    UniVars,
    UniVarState (..),
    app',
    evalApp',
    force',
    ExtendedEnv (..),
    resugar,
    nf,
) where

import Common (
    Index (..),
    Level (..),
    Literal (..),
    Loc (..),
    Located (..),
    Name,
    Name_ (ConsName, NilName, TrueName),
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
import Effectful.State.Static.Local (State, get)
import Error.Diagnose (Position (..))
import IdMap qualified as LMap
import LangPrelude hiding (force)
import Prettyprinter (line, vsep)
import Syntax
import Syntax.Core qualified as C
import Syntax.Elaborated (Typed (..))
import Syntax.Elaborated qualified as D
import Syntax.Elaborated qualified as E
import Syntax.Value as Reexport

data UniVarState = Solved Value | Unsolved deriving (Show)
type UniVars = EnumMap UniVar UniVarState

data ExtendedEnv = ExtendedEnv
    { locals :: [Value]
    , topLevel :: IdMap Name_ Value
    , univars :: UniVars
    }

-- an orphan instance, since otherwise we'd have a cyclic dependency between elaborated terms, which are typed, and values
-- perhaps elaborated terms should be parametrised by the type instead?..
instance PrettyAnsi Value where
    prettyAnsi opts = prettyAnsi opts . quote EMap.empty (Level 0)

deriving via (UnAnnotate Value) instance Pretty Value
deriving via (UnAnnotate Value) instance Show Value

quote :: UniVars -> Level -> Value -> CoreTerm
quote univars = go
  where
    go lvl = \case
        TyCon name args -> foldl' C.App (C.TyCon name) $ fmap (quote univars lvl) args
        Con con args -> C.Con con $ fmap (quote univars lvl) args
        Lambda closure -> C.Lambda closure.var $ quoteClosure univars lvl closure
        PrimFunction PrimFunc{name, captured} ->
            -- captured names are stored as a stack, i.e. backwards, so we fold right rather than left here
            foldr (\arg acc -> C.App acc (go lvl arg)) (C.Name name) captured
        Record vals -> C.Record $ fmap (go lvl) vals
        Sigma x y -> C.Sigma (go lvl x) (go lvl y)
        Variant name val -> C.App (C.Variant name) (go lvl val)
        PrimValue lit -> C.Literal lit
        Q q v e closure -> C.Q q v e closure.var (go lvl closure.ty) $ quoteClosure univars lvl closure
        VariantT row -> C.VariantT $ fmap (go lvl) row
        RecordT row -> C.RecordT $ fmap (go lvl) row
        Stuck stuck -> quoteStuck lvl stuck

    quoteStuck :: Level -> Stuck -> CoreTerm
    quoteStuck lvl = \case
        VarApp varLvl spine -> quoteSpine (C.Var $ levelToIndex lvl varLvl) spine
        UniVarApp uni spine -> quoteSpine (C.UniVar uni) spine
        Fn fn acc -> C.App (go lvl $ PrimFunction fn) (quoteStuck lvl acc)
        Case _arg _matches -> error "todo: quote stuck case"
      where
        quoteSpine = foldr (\arg acc -> C.App acc (quote univars lvl arg))

evalCore :: ExtendedEnv -> CoreTerm -> Value
evalCore env@ExtendedEnv{..} = \case
    -- note that env.topLevel is a lazy IdMap, so we only force the outer structure here
    C.Name name -> LMap.lookupDefault (error . show $ "unbound top-level name" <+> pretty name) (unLoc name) env.topLevel
    C.Var index
        | index.getIndex >= length env.locals -> PrimValue (IntLiteral $ negate index.getIndex) -- error $ show $ pretty index.getIndex <+> "out of scope, max is" <+> pretty (length env.locals)
        | otherwise -> env.locals !! index.getIndex
    C.TyCon name -> Type name
    C.Con name args -> Con name $ map (evalCore env) args
    C.Lambda var body -> Lambda $ Closure{var, ty = (), env = ValueEnv{..}, body}
    C.App (C.Variant name) arg -> Variant name $ evalCore env arg -- this is a bit of an ugly case
    C.App lhs rhs -> evalApp univars (evalCore env lhs) (evalCore env rhs)
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
    C.Variant name -> Lambda $ Closure{var = Name' "x", ty = (), env = ValueEnv{..}, body = C.Variant name `C.App` C.Var (Index 0)}
    C.Q q vis e var ty body -> Q q vis e $ Closure{var, ty = evalCore env ty, env = ValueEnv{..}, body}
    C.VariantT row -> VariantT $ evalCore env <$> row
    C.RecordT row -> RecordT $ evalCore env <$> row
    C.UniVar uni -> force univars (UniVar uni)
    C.InsertedUniVar uni bds -> appBDs env.locals (force univars $ UniVar uni) bds
  where
    mkStuckBranches :: [(CorePattern, CoreTerm)] -> [PatternClosure ()]
    mkStuckBranches = map \(pat, body) -> PatternClosure{pat, ty = (), env = ValueEnv{..}, body}

    -- apply a univar to all variables in scope, skipping those whose value is known
    appBDs :: [Value] -> Value -> [C.BoundDefined] -> Value
    appBDs = \cases
        [] val [] -> val
        (t : rest) val (C.Bound : bds) -> evalApp univars (appBDs rest val bds) t
        (_ : rest) val (C.Defined : bds) -> appBDs rest val bds
        _ _ _ -> error "bound-defined / env mismatch"

nf :: Level -> ExtendedEnv -> CoreTerm -> CoreTerm
nf lvl env term = quote env.univars lvl $ evalCore env term

evalApp' :: State UniVars :> es => Value -> Value -> Eff es Value
evalApp' lhs rhs = do
    univars <- get @UniVars
    pure $ evalApp univars lhs rhs

evalApp :: UniVars -> Value -> Value -> Value
evalApp univars = \cases
    (Lambda closure) arg -> app univars closure arg
    -- this is slightly janky, but I'm not sure whether I want to represent type constructors as lambdas yet
    (TyCon name args) arg -> TyCon name (args <> [arg])
    (PrimFunction fn) (Stuck stuck) -> Stuck $ Fn fn stuck
    (PrimFunction PrimFunc{remaining = 1, captured, f}) arg -> f (arg :| captured)
    (PrimFunction PrimFunc{name, remaining, captured, f}) arg -> PrimFunction PrimFunc{name, remaining = pred remaining, captured = arg : captured, f}
    (Stuck (VarApp lvl spine)) arg -> Stuck $ VarApp lvl (arg : spine)
    (Stuck (UniVarApp uni spine)) arg -> Stuck $ UniVarApp uni (arg : spine)
    nonFunc arg -> error . show $ "attempted to apply" <+> pretty nonFunc <+> "to" <+> pretty arg

force' :: State UniVars :> es => Value -> Eff es Value
force' val = do
    univars <- get @UniVars
    pure $ force univars val

-- try to evaluate an expression that was previously stuck on an unsolved skolem
force :: UniVars -> Value -> Value
force !univars = \case
    Stuck (UniVarApp uni spine) -> case EMap.lookup uni univars of
        -- an out of scope univar indicates a bug, but a non-fatal one
        Nothing -> traceShow ("out of scope univar:" <+> pretty uni) (UniVar uni)
        Just Unsolved -> Stuck $ UniVarApp uni spine
        Just (Solved val) -> force univars $ applySpine val spine
    Stuck (Fn fn arg) -> case force univars (Stuck arg) of
        Stuck stillStuck -> Stuck (Fn fn stillStuck)
        noLongerStuck -> evalApp univars (PrimFunction fn) noLongerStuck
    Stuck (Case arg matches) -> case force univars (Stuck arg) of
        Stuck stillStuck -> Stuck (Case stillStuck matches)
        noLongerStuck -> fromMaybe (error "couldn't match") $ asum $ fmap (\closure -> tryApplyPatternClosure univars closure noLongerStuck) matches
    other -> other
  where
    applySpine = foldr (flip $ evalApp univars)

app :: UniVars -> Closure ty -> Value -> Value
app univars Closure{env = ValueEnv{..}, body} arg = evalCore (ExtendedEnv{locals = arg : locals, ..}) body

app' :: State UniVars :> es => Closure ty -> Value -> Eff es Value
app' closure arg = do
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

-- TODO: properly handle recursive bindings (that is, don't infinitely loop on them)
desugar :: ETerm -> CoreTerm
desugar = \case
    E.Var index -> C.Var index
    E.Name name -> C.Name name
    E.Literal lit -> C.Literal lit
    E.App lhs rhs -> C.App (go lhs) (go rhs)
    E.Lambda ((E.VarP arg) ::: _) body -> C.Lambda arg (go body)
    E.Lambda (_pat ::: _) _body -> error "desugar pattern lambda: should lift"
    -- C.Lambda "x" <$> go (E.Case (E.Var (Index 0)) [(pat, body)])
    E.Let _binding _expr -> error "todo: properly desugar Let" {- case binding of
                                                               E.ValueB ((E.VarP name) ::: _) body -> C.Let name <$> go body <*> go expr
                                                               E.ValueB (pat ::: _) body -> go $ E.Case body [(pat, expr)]
                                                               E.FunctionB name args body -> C.Let (unLoc . toSimpleName $ name) <$> go (foldr E.Lambda body args) <*> go expr
                                                               -}
    E.LetRec _bindings _body -> error "todo: letrec desugar"
    E.Case arg matches -> C.Case (go arg) $ fmap (bimap flattenPattern go) matches
    E.Match _matches@((_ :| [], _) : _) -> error "todo: lift in match"
    {-do
       name <- freshName $ Name' "matchArg" :@ loc
       matches' <- for matches \case
           ((pat ::: _) :| [], body) -> bitraverse flattenPattern go (pat, body)
           _ -> internalError loc "inconsistent pattern count in a match expression"
       pure $ C.Lambda name $ C.Case (C.Name name) matches'-}
    E.Match _ -> error "todo: multi-arg match desugar"
    E.If cond true false ->
        C.Case
            (go cond)
            [ (C.ConstructorP (TrueName :@ loc) [], go true)
            , (C.WildcardP "", go false)
            ]
    E.Variant name -> C.Variant name
    E.Record fields -> C.Record $ fmap go fields
    E.RecordAccess record field ->
        let arg = go record
         in C.Case arg [(C.RecordP (one (field, unLoc field)), C.Var (Index 0))]
    {- `record.field` gets desugared to
        case record of
            {field} -> field
    -}
    E.Sigma x y -> C.Sigma (go x) (go y)
    E.List xs -> foldr ((C.App . C.App cons) . go) nil xs
    E.Do{} -> error "todo: desugar do blocks"
    E.Q q vis er (var ::: kind) body -> C.Q q vis er var (go kind) (go body)
    E.VariantT row -> C.VariantT $ fmap go row
    E.RecordT row -> C.RecordT $ fmap go row
    E.UniVar uni -> C.UniVar uni
    E.InsertedUniVar uni bds -> C.InsertedUniVar uni bds
  where
    go = desugar
    cons = C.Name $ ConsName :@ loc
    nil = C.Name $ NilName :@ loc
    loc = Loc Position{begin = (0, 0), end = (0, 0), file = "<eval>"}

    -- we only support non-nested patterns for now
    flattenPattern :: EPattern -> CorePattern
    flattenPattern p = case p of
        E.VarP name -> C.VarP name
        E.WildcardP name -> C.WildcardP name
        E.ConstructorP name pats -> C.ConstructorP name (fmap asVar pats)
        E.VariantP name pat -> C.VariantP name (asVar pat)
        E.RecordP row -> C.RecordP $ fmap asVar row
        E.SigmaP lhs rhs -> C.SigmaP (asVar lhs) (asVar rhs)
        E.ListP _ -> error "todo: list pattern desugaring"
        E.LiteralP lit -> C.LiteralP lit

    asVar (E.VarP name) = name
    asVar (E.WildcardP txt) = Wildcard' txt
    asVar _ = error "todo: nested patterns"

-- idk, perhaps typecheck should produce CoreTerm right away
resugar :: CoreTerm -> ETerm
resugar = \case
    C.Var index -> E.Var index
    C.Name name -> E.Name name
    C.TyCon name -> E.Name name
    C.Con name args -> foldl' E.App (E.Name name) (fmap resugar args)
    C.Lambda var body -> E.Lambda (E.VarP var ::: error "what") $ resugar body
    C.App lhs rhs -> E.App (resugar lhs) (resugar rhs)
    C.Case arg matches -> E.Case (resugar arg) $ fmap (bimap resugarPattern resugar) matches
    C.Let _name _expr _body -> error "bindings are annoying" -- E.Let (E.VarP name) (resugar expr) (resugar body)
    C.Literal lit -> E.Literal lit
    C.Record row -> E.Record (fmap resugar row)
    C.Sigma lhs rhs -> E.Sigma (resugar lhs) (resugar rhs)
    C.Variant name -> E.Variant name
    C.Q q v e var ty body -> E.Q q v e (var ::: resugar ty) (resugar body)
    C.VariantT row -> E.VariantT $ fmap resugar row
    C.RecordT row -> E.RecordT $ fmap resugar row
    C.UniVar uni -> E.UniVar uni
    C.InsertedUniVar uni bds -> E.InsertedUniVar uni bds
  where
    resugarPattern = \case
        C.VarP name -> E.VarP name
        C.WildcardP txt -> E.WildcardP txt
        C.ConstructorP name args -> E.ConstructorP name $ fmap E.VarP args
        C.VariantP name arg -> E.VariantP name $ E.VarP arg
        C.RecordP nameRow -> E.RecordP $ fmap E.VarP nameRow
        C.SigmaP lhs rhs -> E.SigmaP (E.VarP lhs) (E.VarP rhs)
        C.LiteralP lit -> E.LiteralP lit

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
        D.ValueD (E.FunctionB name args body) -> pure [(unLoc name, Right $ foldr E.Lambda body args)]
        -- todo: value constructors have to be in scope by the time we typecheck definitions that depend on them (say, GADTs)
        -- the easiest way is to just apply `typecheck` and `modifyEnv` declaration-by-declaration
        D.TypeD _ constrs -> pure $ fmap mkConstr constrs
        D.SignatureD{} -> pure mempty

    mkConstr (name, count) = (unLoc name, Left $ mkConLambda count name)

mkConLambda :: Int -> Name -> Value
mkConLambda n con = evalCore emptyEnv lambdas
  where
    names = fmap (\i -> Name' $ "x" <> show i) [1 .. n]
    lambdas = foldr C.Lambda body names
    body = C.Con con $ map (C.Var . Index) [n - 1, n - 2 .. 0]
    emptyEnv = ExtendedEnv{univars = EMap.empty, topLevel = LMap.empty, locals = []}

{-
names <- for [1 .. n] \i -> freshName (Name' ("x" <> show i) :@ getLoc con)
-- fused foldl/foldr go brrr
pure $
    foldr
        ( \var bodyFromEnv env' ->
            let newEnv = env'{locals = LMap.insert var (Var var) env'.values}
             in -- current implementation with quoteForPrinting is a crutch
                Lambda $ Closure{var, ty = (), env = newEnv, body = quoteForPrinting $ bodyFromEnv newEnv}
        )
        (const $ Con con (map Var names))
        names
        env
-}

{-
-- is template haskell worth it?

mkLambda1 :: Name -> (Value -> Value) -> Value
mkLambda1 name f = PrimFunction name 1 [] \(x :| _) -> f x

mkLambda2 :: Name -> (Value -> Value -> Value) -> Value
mkLambda2 name f = PrimFunction name 2 [] \(y :| x : _) -> f x y

mkLambda3 :: Name -> (Value -> Value -> Value -> Value) -> Value
mkLambda3 name f = PrimFunction name 3 [] \(z :| y : x : _) -> f x y z
-}
