{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE PatternSynonyms #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Eval (quote, eval, evalCore {-unstuck,-}, modifyEnv, evalAll, app, evalApp, module Reexport, desugarElaborated, force) where

import Common (
    Located (..),
    Name,
    Name_ (ConsName, NilName, TrueName),
    PrettyAnsi (..),
    SimpleName_ (Name'),
    UnAnnotate (..),
    getLoc,
    prettyDef,
    toSimpleName,
    pattern L,
 )

import Data.Foldable (foldrM)

-- IdMap is currently lazy anyway, but it's up to change

import Data.Sequence (pattern (:|>))
import Data.Traversable (for)
import Diagnostic
import IdMap qualified as LMap
import LangPrelude hiding (force)
import NameGen (NameGen, freshName)
import Prettyprinter (line, vsep)
import Syntax
import Syntax.Core qualified as C
import Syntax.Elaborated (EDeclaration, EPattern, ETerm, Typed (..))
import Syntax.Elaborated qualified as D
import Syntax.Elaborated qualified as E
import Syntax.Row qualified as Row
import Syntax.Value as Reexport

-- quote a value for pretty-printing
quoteForPrinting :: Value -> CoreTerm
quoteForPrinting = \case
    TyCon name args -> foldl' C.App (C.TyCon name) (map quoteForPrinting args)
    Con con args -> C.Con con (map quoteForPrinting args)
    Lambda closure -> C.Lambda closure.var (quoteForPrinting $ closureBody closure)
    PrimFunction PrimFunc{name, captured} ->
        -- captured names are stored as a stack, i.e. backwards, so we fold right rather than left here
        foldr (\arg acc -> C.App acc (quoteForPrinting arg)) (C.Name name) captured
    Record vals -> C.Record $ fmap quoteForPrinting vals
    Sigma x y -> C.Sigma (quoteForPrinting x) (quoteForPrinting y)
    Variant name val -> C.App (C.Variant name) $ quoteForPrinting val
    PrimValue lit -> C.Literal lit
    Function l r -> C.Function (quoteForPrinting l) (quoteForPrinting r)
    Q q vis e closure -> C.Q q vis e closure.var (quoteForPrinting closure.ty) $ quoteForPrinting (closureBody closure)
    VariantT row -> C.VariantT $ fmap quoteForPrinting row
    RecordT row -> C.RecordT $ fmap quoteForPrinting row
    Stuck reason spine ->
        let initAcc = case reason of
                OnVar name -> C.Name name
                OnUniVar uni -> C.UniVar uni
         in foldl' quoteSpine initAcc spine
  where
    quoteSpine acc = \case
        App rhs -> C.App acc $ quoteForPrinting rhs
        Fn PrimFunc{name, captured} -> C.App (foldr (\arg acc' -> C.App acc' (quoteForPrinting arg)) (C.Name name) captured) acc
        Case cases -> C.Case acc $ fmap (\PatternClosure{pat, body} -> (pat, body)) cases

-- an orphan instance, since otherwise we'd have a cyclic dependency between elaborated terms, which are typed, and values
-- perhaps elaborated terms should be parametrised by the type instead?..
instance PrettyAnsi Value where
    prettyAnsi opts = prettyAnsi opts . quoteForPrinting

deriving via (UnAnnotate Value) instance Pretty Value
deriving via (UnAnnotate Value) instance Show Value

-- quote a value into a normal form expression
quote :: NameGen :> es => Value -> Eff es CoreTerm
quote = \case
    TyCon name args -> foldl' C.App (C.TyCon name) <$> traverse quote args
    Con con args -> C.Con con <$> traverse quote args
    Lambda closure -> do
        (var, body) <- closureBody' closure
        C.Lambda var <$> quote body
    PrimFunction PrimFunc{name, captured} ->
        foldrM (\arg acc -> C.App acc <$> quote arg) (C.Name name) captured
    Record vals -> C.Record <$> traverse quote vals
    Sigma x y -> C.Sigma <$> quote x <*> quote y
    Variant name val -> C.App (C.Variant name) <$> quote val
    PrimValue lit -> pure $ C.Literal lit
    Function l r -> C.Function <$> quote l <*> quote r
    Q q vis e closure -> do
        (var, body) <- closureBody' closure
        ty <- quote closure.ty
        C.Q q vis e var ty <$> quote body
    VariantT row -> C.VariantT <$> traverse quote row
    RecordT row -> C.RecordT <$> traverse quote row
    Stuck reason spine ->
        let initAcc = case reason of
                OnVar name -> C.Name name
                OnUniVar uni -> C.UniVar uni
         in foldlM quoteSpine initAcc spine
  where
    quoteSpine acc = \case
        App rhs -> C.App acc <$> quote rhs
        Fn PrimFunc{name, captured} -> C.App <$> foldrM (\arg acc' -> C.App acc' <$> quote arg) (C.Name name) captured <*> pure acc
        Case cases -> C.Case acc <$> traverse (\PatternClosure{pat, body} -> pure (pat, body)) cases

evalCore :: ValueEnv -> CoreTerm -> Value
evalCore !env = \case
    -- note that env is a lazy IdMap, so we only force the outer structure here
    C.Name name -> LMap.lookupDefault (Var name) name env.values
    C.TyCon name -> TyCon name []
    C.Con name args -> Con name $ map (evalCore env) args
    C.Lambda var body -> Lambda $ Closure{var, ty = (), env, body}
    C.App (C.Variant name) arg -> Variant name $ evalCore env arg -- this is a bit of an ugly case
    C.App lhs rhs -> evalApp (evalCore env lhs) (evalCore env rhs)
    C.Case arg matches -> case evalCore env arg of
        Stuck stuck spine -> Stuck stuck $ spine :|> Case (mkStuckBranches matches)
        val ->
            fromMaybe
                (error $ show $ "pattern mismatch when matching" <+> prettyDef val <+> "with:" <> line <> vsep (map (prettyDef . fst) matches))
                . asum
                $ matches <&> \(pat, body) -> evalCore <$> matchCore env pat val <*> pure body
    C.Let name expr body ->
        let newEnv = env{values = LMap.insert name (evalCore env expr) env.values}
         in evalCore newEnv body
    C.Literal lit -> PrimValue lit
    C.Record row -> Record $ evalCore env <$> row
    C.Sigma x y -> Sigma (evalCore env x) (evalCore env y)
    C.Variant _name -> error "todo: seems like evalCore needs namegen" -- Lambda (Located Blank $ Name' "x") $ C.Variant name `C.App`
    C.Function lhs rhs -> Function (evalCore env lhs) (evalCore env rhs)
    C.Q q vis e var ty body -> Q q vis e $ Closure{var, ty = evalCore env ty, env, body}
    C.VariantT row -> VariantT $ evalCore env <$> row
    C.RecordT row -> RecordT $ evalCore env <$> row
    -- should normal evaluation resolve univars?
    -- probably not, but it should be able to traverse solved vars (wip)
    C.UniVar uni -> UniVar uni
  where
    mkStuckBranches :: [(CorePattern, CoreTerm)] -> [PatternClosure ()]
    mkStuckBranches = map \(pat, body) -> PatternClosure{pat, ty = (), env, body}

evalApp :: Value -> Value -> Value
evalApp = \cases
    (Lambda closure) arg -> closure `app` arg
    -- this is slightly janky, but I'm not sure whether I want to represent type constructors as lambdas yet
    (TyCon name args) arg -> TyCon name (args <> [arg])
    (PrimFunction fn) (Stuck stuck spine) -> Stuck stuck $ spine :|> Fn fn
    (PrimFunction PrimFunc{remaining = 1, captured, f}) arg -> f (arg :| captured)
    (PrimFunction PrimFunc{name, remaining, captured, f}) arg -> PrimFunction $ PrimFunc name (pred remaining) (arg : captured) f
    (Stuck stuck spine) arg -> Stuck stuck $ spine :|> App arg
    nonFunc arg -> error . show $ "attempted to apply" <+> pretty nonFunc <+> "to" <+> pretty arg

-- try to evaluate an expression that was previously stuck on an unsolved skolem
force :: ValueEnv -> Value -> Value
force !env = \case
    Stuck (OnUniVar uni) spine -> Stuck (OnUniVar uni) spine
    Stuck (OnVar name) spine -> case force env <$> LMap.lookup name env.values of
        Nothing -> Stuck (OnVar name) spine
        Just (Stuck reason spine') -> Stuck reason $ spine' <> spine
        Just val -> force env $ foldl' applySpine val spine
    other -> other
  where
    applySpine acc = \case
        App rhs -> evalApp acc rhs
        Fn fn -> evalApp (PrimFunction fn) acc
        Case cases -> fromMaybe (error "failed to match pattern") $ asum $ fmap (`tryApplyPatternClosure` acc) cases

app :: Closure ty -> Value -> Value
app Closure{var, env, body} arg = evalCore (env{values = LMap.insert var arg env.values}) body

-- do we need a fresh name here?
closureBody :: Closure a -> Value
closureBody closure = closure `app` Var closure.var

closureBody' :: NameGen :> es => Closure a -> Eff es (Name, Value)
closureBody' closure = do
    var <- freshName $ toSimpleName closure.var
    pure (var, closure `app` Var var)

-- | try to apply a pattern to a value, updating the given value env
matchCore :: ValueEnv -> CorePattern -> Value -> Maybe ValueEnv
matchCore env = \cases
    (C.VarP name) val -> Just $ env{values = LMap.insert name val env.values}
    C.WildcardP{} _ -> Just env
    (C.ConstructorP pname argNames) (Con name args)
        | pname == name && length argNames == length args ->
            Just $ env{values = foldl' (flip $ uncurry LMap.insert) env.values (zip argNames args)}
    (C.VariantP pname argName) (Variant name val)
        | pname == name -> Just $ env{values = LMap.insert argName val env.values}
    (C.RecordP varRow) (Record row) ->
        let (pairs, _, _) = Row.zipRows varRow row
         in Just $ env{values = foldl' (flip $ uncurry LMap.insert) env.values pairs}
    (C.SigmaP lhsP rhsP) (Sigma lhs rhs) -> Just env{values = LMap.insert lhsP lhs $ LMap.insert rhsP rhs env.values}
    (C.LiteralP lit) (PrimValue val) -> env <$ guard (lit == val)
    _ _ -> Nothing

tryApplyPatternClosure :: PatternClosure ty -> Value -> Maybe Value
tryApplyPatternClosure PatternClosure{pat, env, body} arg = do
    newEnv <- matchCore env pat arg
    pure $ evalCore newEnv body

-- desugar could *almost* be pure, but unfortunately, we need name gen here
-- perhaps we should use something akin to locally nameless?
-- TODO: properly handle recursive bindings (that is, don't infinitely loop on them)
desugarElaborated :: forall es. (NameGen :> es, Diagnose :> es) => ETerm -> Eff es CoreTerm
desugarElaborated = go
  where
    go (e :@ loc ::: ty) = case e of
        E.Name name -> pure $ C.Name name
        E.Literal lit -> pure $ C.Literal lit
        E.App lhs rhs -> C.App <$> go lhs <*> go rhs
        E.Lambda (L (E.VarP arg) ::: _) body -> C.Lambda arg <$> go body
        E.Lambda pat@(_ ::: patTy) body@(_ ::: bodyTy) -> do
            name <- freshName $ Name' "lamArg" :@ loc
            C.Lambda name <$> go (E.Case (E.Name name :@ getLoc name ::: patTy) [(pat, body)] :@ loc ::: bodyTy)
        E.Let binding expr -> case binding of
            E.ValueB (L (E.VarP name) ::: _) body -> C.Let name <$> go body <*> go expr
            E.ValueB pat body -> desugarElaborated $ E.Case body [(pat, expr)] :@ loc ::: ty
            E.FunctionB name args body -> C.Let name <$> go (foldr (\x -> (::: error "tedium") . (:@ loc) . E.Lambda x) body args) <*> go expr
        E.LetRec _bindings _body -> internalError loc "todo: letrec desugar"
        E.Case arg matches -> C.Case <$> go arg <*> traverse (bitraverse flattenPattern go) matches
        E.Match matches@((_ :| [], _) : _) -> do
            name <- freshName $ Name' "matchArg" :@ loc
            matches' <- for matches \case
                (pat :| [], body) -> bitraverse flattenPattern desugarElaborated (pat, body)
                _ -> internalError loc "inconsistent pattern count in a match expression"
            pure $ C.Lambda name $ C.Case (C.Name name) matches'
        E.Match _ -> internalError loc "todo: multi-arg match desugar"
        E.If cond@(_ :@ condLoc ::: _) true false -> do
            cond' <- go cond
            true' <- go true
            false' <- go false
            pure . C.Case cond' $
                [ (C.ConstructorP (TrueName :@ condLoc) [], true')
                , (C.WildcardP "", false')
                ]
        E.Variant name -> pure $ C.Variant name
        E.Record fields -> C.Record <$> traverse go fields
        E.RecordAccess record field -> do
            arg <- desugarElaborated record
            fieldVar <- freshName field
            pure $ C.Case arg [(C.RecordP (one (field, fieldVar)), C.Name fieldVar)]
        {- `record.field` gets desugared to
            case record of
                {field} -> field
        -}
        E.Sigma x y -> C.Sigma <$> go x <*> go y
        E.List xs -> foldr (C.App . C.App cons) nil <$> traverse go xs
        E.Do{} -> error "todo: desugar do blocks"
        E.Function from to -> C.Function <$> go from <*> go to
        E.Q q vis er var kind body -> C.Q q vis er var <$> quote kind <*> go body
        E.VariantT row -> C.VariantT <$> traverse go row
        E.RecordT row -> C.RecordT <$> traverse go row
      where
        cons = C.Name $ ConsName :@ loc
        nil = C.Name $ NilName :@ loc

    -- we only support non-nested patterns for now
    flattenPattern :: EPattern -> Eff es CorePattern
    flattenPattern (p :@ loc ::: _) = case p of
        E.VarP name -> pure $ C.VarP name
        E.WildcardP name -> pure $ C.WildcardP name
        E.ConstructorP name pats -> C.ConstructorP name <$> traverse asVar pats
        E.VariantP name pat -> C.VariantP name <$> asVar pat
        E.RecordP row -> C.RecordP <$> traverse asVar row
        E.SigmaP lhs rhs -> C.SigmaP <$> asVar lhs <*> asVar rhs
        E.ListP _ -> internalError loc "todo: list pattern desugaring"
        E.LiteralP lit -> pure $ C.LiteralP lit

    asVar (L (E.VarP name) ::: _) = pure name
    asVar (E.WildcardP txt :@ loc ::: _) = freshName $ Name' txt :@ loc
    asVar (_ :@ loc ::: _) = internalError loc "todo: nested patterns"

eval :: (Diagnose :> es, NameGen :> es) => ValueEnv -> ETerm -> Eff es Value
eval env term = evalCore env <$> desugarElaborated term

evalAll :: (Diagnose :> es, NameGen :> es) => [EDeclaration] -> Eff es ValueEnv
evalAll = modifyEnv ValueEnv{values = LMap.empty}

modifyEnv
    :: forall es
     . (Diagnose :> es, NameGen :> es)
    => ValueEnv
    -> [EDeclaration]
    -> Eff es ValueEnv
modifyEnv env decls = do
    desugared <- (traverse . traverse) desugarElaborated . LMap.fromList =<< foldMapM collectBindings decls
    let newEnv = env{values = fmap (either id (evalCore newEnv)) desugared <> env.values}
    pure newEnv
  where
    collectBindings :: EDeclaration -> Eff es [(Name, Either Value ETerm)]
    collectBindings (decl :@ loc) = case decl of
        D.ValueD (E.ValueB (L (E.VarP name) ::: _) body) -> pure [(name, Right body)]
        D.ValueD (E.ValueB _ _) -> internalError loc "whoops, destructuring bindings are not supported yet"
        D.ValueD (E.FunctionB name args body) -> pure [(name, Right $ foldr (\x -> (::: error "todo: types in function binding desugar") . (:@ loc) . E.Lambda x) body args)]
        -- todo: value constructors have to be in scope by the time we typecheck definitions that depend on them (say, GADTs)
        -- the easiest way is to just apply `typecheck` and `modifyEnv` declaration-by-declaration
        D.TypeD _ constrs -> traverse mkConstr constrs
        D.SignatureD{} -> pure mempty

    mkConstr (name, count) = (name,) . Left <$> mkConLambda count name env

mkConLambda :: NameGen :> es => Int -> Name -> ValueEnv -> Eff es Value
mkConLambda n con env = do
    names <- for [1 .. n] \i -> freshName (Name' ("x" <> show i) :@ getLoc con)
    -- fused foldl/foldr go brrr
    pure $
        foldr
            ( \var bodyFromEnv env' ->
                let newEnv = env'{values = LMap.insert var (Var var) env'.values}
                 in -- current implementation with quoteForPrinting is a crutch
                    Lambda $ Closure{var, ty = (), env = newEnv, body = quoteForPrinting $ bodyFromEnv newEnv}
            )
            (const $ Con con (map Var names))
            names
            env

{-
-- is template haskell worth it?

mkLambda1 :: Name -> (Value -> Value) -> Value
mkLambda1 name f = PrimFunction name 1 [] \(x :| _) -> f x

mkLambda2 :: Name -> (Value -> Value -> Value) -> Value
mkLambda2 name f = PrimFunction name 2 [] \(y :| x : _) -> f x y

mkLambda3 :: Name -> (Value -> Value -> Value -> Value) -> Value
mkLambda3 name f = PrimFunction name 3 [] \(z :| y : x : _) -> f x y z
-}
