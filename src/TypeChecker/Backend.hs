{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE NoFieldSelectors #-}
{-# OPTIONS_GHC -Wno-missing-export-lists #-}
{-# OPTIONS_GHC -Wno-partial-fields #-}

module TypeChecker.Backend where

import Common
import Data.EnumMap.Strict qualified as EMap
import Data.EnumSet qualified as Set
import Data.Sequence qualified as Seq
import Diagnostic (Diagnose, internalError, internalError')
import Effectful
import Effectful.Dispatch.Dynamic (reinterpret_)
import Effectful.Labeled
import Effectful.Reader.Static (Reader, ask, asks, local, runReader)
import Effectful.State.Static.Local (State, evalState, get, gets, modify, runState)
import Error.Diagnose (Position (..))
import Eval (Value, ValueEnv)
import Eval qualified as V
import IdMap qualified as LMap
import IdMap qualified as Map
import LangPrelude hiding (break, cycle)
import NameGen
import Syntax
import Syntax.Core qualified as C
import Syntax.Row
import Syntax.Row qualified as Row
import Syntax.Term (Erasure (..), Quantifier (..), Visibility (..))
import TypeChecker.TypeError

type Pat = Pattern 'Fixity
type TypeDT = Located Value
type TypeDT_ = Value
type Type' = Located Value
type Type'_ = Value

type Monotype = Located Monotype_
data Monotype_
    = MCon Name [Monotype_]
    | MTyCon Name [Monotype_]
    | MLambda (MonoClosure ())
    | MRecord (Row Monotype_)
    | MSigma Monotype_ Monotype_
    | MVariant OpenName Monotype_
    | MPrim Literal
    | MPrimFn MonoPrimFunc
    | -- types
      MFn Monotype_ Monotype_
    | MQ Quantifier Erasure (MonoClosure Monotype_)
    | MVariantT (ExtRow Monotype_)
    | MRecordT (ExtRow Monotype_)
    | MStuck V.Stuck (Seq MonoStuckPart)

data MonoStuckPart
    = MApp ~Monotype_
    | MStuckFn MonoPrimFunc
    | MCase [MonoPatternClosure ()]

pattern MUniVar :: UniVar -> Monotype_
pattern MUniVar uni <- MStuck (V.UniVarApp uni) Seq.Empty
    where
        MUniVar uni = MStuck (V.UniVarApp uni) Seq.Empty

pattern MSkolem :: Name -> Monotype_
pattern MSkolem name <- MStuck (V.VarApp name) Seq.Empty
    where
        MSkolem name = MStuck (V.OnVar name) Seq.Empty

data MonoPrimFunc = MonoPrimFunc
    { name :: Name
    , remaining :: Int
    , captured :: [Monotype_]
    , f :: NonEmpty Value -> Value
    }
data MonoClosure ty = MonoClosure
    { var :: Name
    , variance :: Variance
    , ty :: ty
    , env :: ValueEnv
    , body :: CoreTerm
    }
data MonoPatternClosure ty = MonoPatternClosure
    { pat :: CorePattern
    , variance :: Variance
    , ty :: ty
    , env :: ValueEnv
    , body :: CoreTerm
    }

data Variance
    = -- | negative variance, forall in a negative position gets instantiated to univars
      In
    | -- | positive variance, forall in a positive position gets instantiated to skolems
      Out
    | -- | invariance, both forall and exists get instantiated to skolems no matter what
      Inv
    deriving (Eq)

data Env = Env
    { scope :: Scope
    , values :: ValueEnv
    , locals :: IdMap Name TypeDT
    }

-- the types of top-level bindings should not contain metavars
-- this is not enforced at type level, though
type TopLevel = IdMap Name Type'_
type UniVars = EnumMap UniVar (Either Scope Monotype) -- should we use located Monotypes here? I'm not sure
type InfEffs es =
    ( NameGen :> es
    , TC :> es
    , -- todo: most of the typecheck actions only need TopLevel and ConstructorTable read-only
      -- however, when they are called from inferDecl, TopLevel and ConstructorTable are needed in State context
      State TopLevel :> es
    , State ConstructorTable :> es
    , Reader Env :> es
    , Diagnose :> es
    )

newtype ConstructorTable = ConstructorTable
    { table :: IdMap Name_ (IdMap Name_ ([ExType] -> [ExType]))
    }
data ExType = TyCon Name_ [ExType] | ExVariant (ExtRow ExType) | ExRecord (Row ExType) | OpaqueTy
    deriving (Show)

data TC :: Effect where
    FreshUniVar' :: TC m UniVar
    LookupUniVar :: UniVar -> TC m (Either Scope Monotype)
    -- | a helper for `alterUniVar`, shouldn't be used directly
    SetUniVar :: UniVar -> (Either Scope Monotype) -> TC m ()
    FreshSkolem' :: SimpleName -> TC m Name
    SkolemScope :: Name -> TC m Scope

makeEffect ''TC

instance Pretty Monotype_ where
    pretty = pretty . unMono'

runTC :: (NameGen :> es, Diagnose :> es, Reader Env :> es) => Eff (TC : es) a -> Eff es a
runTC = reinterpret_
    ( runLabeled @UniVar runNameGen
        . evalState @(IdMap Name Scope) Map.empty
        . evalState @UniVars EMap.empty
    )
    \case
        FreshUniVar' -> do
            -- c'mon effectful
            var <- UniVar <$> labeled @UniVar @NameGen freshId
            scope <- asks @Env (.scope)
            modify @UniVars $ EMap.insert var (Left scope)
            pure var
        LookupUniVar uni -> maybe (internalError' $ "missing univar" <+> prettyDef uni) pure . EMap.lookup uni =<< get @UniVars
        SetUniVar uni scopeOrTy -> modify @UniVars $ EMap.insert uni scopeOrTy
        FreshSkolem' name -> do
            -- skolems are generally derived from type variables, so they have names
            scope <- asks @Env (.scope)
            skolem <- freshName name
            modify $ Map.insert skolem scope
            pure skolem
        SkolemScope skolem ->
            maybe (internalError (getLoc skolem) $ "missing skolem" <+> pretty skolem) pure
                . Map.lookup skolem
                =<< get @(_ Name _)

run
    :: (NameGen :> es, Diagnose :> es)
    => ValueEnv
    -> Eff (TC : Reader Env : es) a
    -> Eff es a
run values action = runReader initState $ runTC action
  where
    initState =
        Env
            { scope = Scope 0
            , values
            , locals = Map.empty
            }

freshUniVar :: TC :> es => Eff es TypeDT_
freshUniVar = V.UniVar <$> freshUniVar'

freshSkolem :: TC :> es => SimpleName -> Eff es TypeDT_
freshSkolem name = V.Var <$> freshSkolem' name

withUniVar :: TC :> es => UniVar -> (Monotype -> Eff es a) -> Eff es ()
withUniVar uni f =
    lookupUniVar uni >>= \case
        Left _ -> pass
        Right ty -> void $ f ty

solveUniVar, overrideUniVar :: InfEffs es => UniVar -> Monotype -> Eff es ()
solveUniVar = alterUniVar False
overrideUniVar = alterUniVar True

data SelfRef = Direct | Indirect
data Cycle = DirectCycle | NoCycle deriving (Eq)

alterUniVar :: forall es. InfEffs es => Bool -> UniVar -> Monotype -> Eff es ()
alterUniVar override uni ty = do
    -- here comes the magic. If the new type contains other univars, we change their scope
    mbScope <-
        lookupUniVar uni >>= \case
            Right _
                | not override ->
                    internalError (getLoc ty) $ "attempted to solve a solved univar " <> prettyDef uni
            Right _ -> pure Nothing
            Left scope -> pure $ Just scope
    cycle <- cycleCheck mbScope (Direct, Set.singleton uni) ty
    when (cycle == NoCycle) $ setUniVar uni (Right ty)
  where
    -- errors out on indirect cycles (i.e. a ~ Maybe a)
    -- returns DirectCycle on direct univar cycles (i.e. a ~ b, b ~ c, c ~ a)
    -- returns NoCycle when there are no cycles (duh)
    -- todo: we can infer equirecursive types (mu) when a cycle goes through a record / variant
    cycleCheck :: Maybe Scope -> (SelfRef, EnumSet UniVar) -> Monotype -> Eff es Cycle
    cycleCheck mbScope state (L mty) = go state mty
      where
        go :: (SelfRef, EnumSet UniVar) -> Monotype_ -> Eff es Cycle
        go (selfRefType, acc) = \case
            MUniVar uni2 | Set.member uni2 acc -> case selfRefType of
                Direct -> pure DirectCycle
                Indirect -> do
                    unwrappedTy <- unMono <$> unwrap ty
                    typeError $ SelfReferential (getLoc $ unMono ty) uni unwrappedTy
            MUniVar uni2 ->
                lookupUniVar uni2 >>= \case
                    Right ty' -> go (selfRefType, Set.insert uni2 acc) $ unLoc ty'
                    Left scope' -> do
                        case mbScope of
                            Just scope | scope' > scope -> setUniVar uni2 (Left scope')
                            _ -> pass
                        pure NoCycle
            MFn from to -> go (Indirect, acc) from *> go (Indirect, acc) to
            MQ _q _e closure -> go (Indirect, acc) closure.ty *> cycleCheckClosure acc closure
            MCon _ args -> NoCycle <$ traverse_ (go (Indirect, acc)) args
            MVariantT row -> NoCycle <$ traverse_ (go (Indirect, acc)) row
            MRecordT row -> NoCycle <$ traverse_ (go (Indirect, acc)) row
            MVariant _ val -> go (Indirect, acc) val
            MRecord row -> NoCycle <$ traverse_ (go (Indirect, acc)) row
            MSigma x y -> go (Indirect, acc) x *> go (Indirect, acc) y
            MLambda closure -> cycleCheckClosure acc closure
            MPrimFn MonoPrimFunc{captured} -> NoCycle <$ traverse_ (go (Indirect, acc)) captured
            MTyCon _ args -> NoCycle <$ traverse_ (go (Indirect, acc)) args
            MStuck V.OnVar{} spine -> NoCycle <$ traverse_ (cycleCheckSpine acc) spine -- todo: recur into solved skolems
            MStuck (V.OnUniVar uni2) spine -> do
                traverse_ (cycleCheckSpine acc) spine
                NoCycle <$ go (Indirect, acc) (MUniVar uni2)
            MPrim{} -> pure NoCycle

        cycleCheckClosure :: EnumSet UniVar -> MonoClosure a -> Eff es Cycle
        cycleCheckClosure acc closure = do
            skolem <- freshSkolem $ toSimpleName closure.var
            go (Indirect, acc) =<< appMono closure skolem

        cycleCheckSpine acc = \case
            MApp rhs -> go (Indirect, acc) rhs
            MCase{} -> internalError' "todo: cycleCheck stuck MCase"
            MStuckFn{} -> pure NoCycle

    unwrap = traverse \case
        uni2@(MUniVar var) ->
            lookupUniVar var >>= \case
                Right refTy -> unLoc <$> unwrap refTy
                Left{} -> pure uni2
        other -> pure other

-- looks up a type of a binding. Global bindings take precedence over local ones (should they?)
lookupSig :: (TC :> es, State TopLevel :> es, Reader Env :> es) => Name -> Eff es TypeDT_
lookupSig name = do
    topLevel <- get
    locals <- asks @Env (.locals)
    case (Map.lookup name topLevel, Map.lookup name locals) of
        (Just ty, _) -> pure ty
        (_, Just ty) -> pure $ unLoc ty
        (Nothing, Nothing) -> do
            -- assuming that type checking is performed after name resolution,
            -- we may just treat unbound names as holes
            -- every occurence of an unbound name should get a new UniVar
            -- (even then, unbound names are supposed to have unique ids)
            freshUniVar

-- | `local` monomorphised to `Env`
local' :: Reader Env :> es => (Env -> Env) -> Eff es a -> Eff es a
local' = local

declareTopLevel :: InfEffs es => IdMap Name Type'_ -> Eff es ()
declareTopLevel types = modify (types <>)

declareTopLevel' :: InfEffs es => Name -> Type'_ -> Eff es ()
declareTopLevel' name ty = modify $ Map.insert name ty

declare :: Name -> TypeDT -> Env -> Env
declare name ty env = env{locals = LMap.insert name ty env.locals}

declareMany :: IdMap Name TypeDT -> Env -> Env
declareMany typeMap env = env{locals = typeMap <> env.locals}

define :: Name -> Value -> Env -> Env
define name val env = env{values = env.values{V.values = LMap.insert name val env.values.values}}

defineMany :: IdMap Name Value -> Env -> Env
defineMany valMap env = env{values = env.values{V.values = valMap <> env.values.values}}

generalise :: InfEffs es => Eff es TypeDT -> Eff es TypeDT
generalise = fmap runIdentity . generaliseAll . fmap Identity

type LocallySolved = EnumMap UniVar (Either Name CoreTerm)

generaliseAll :: (Traversable t, InfEffs es) => Eff es (t TypeDT) -> Eff es (t TypeDT)
generaliseAll action = do
    Scope n <- asks @Env (.scope)
    types <- local' (\e -> e{scope = Scope $ succ n}) action
    traverse generaliseOne types
  where
    generaliseOne (ty :@ loc) = do
        env <- ask @Env
        (ty', vars) <- runState EMap.empty $ evalState Map.empty $ evalState 'a' $ go loc Out env.scope =<< V.quote ty
        let forallVars = hashNub . lefts $ toList vars
        pure $
            Located loc $
                V.evalCore env.values $
                    foldr (\var body -> C.Q Forall Implicit Erased var (type_ loc) body) ty' forallVars
    type_ loc = C.TyCon (TypeName :@ loc)

    go
        :: InfEffs es
        => Loc
        -> Variance
        -> Scope
        -> CoreTerm
        -> Eff (State Char : State (IdMap Name ()) : State LocallySolved : es) CoreTerm
    go loc variance scope = \case
        C.UniVar uni ->
            gets @LocallySolved (EMap.lookup uni) >>= \case
                Just solved -> pure $ typeVarOrBody solved
                Nothing ->
                    lookupUniVar uni >>= \case
                        -- don't generalise outer-scoped vars
                        Left varScope | varScope <= scope -> pure $ C.UniVar uni
                        innerScoped -> do
                            newTy <- bitraverse (const $ freshTypeVar loc) (go loc variance scope <=< V.quote . unLoc . unMono) innerScoped
                            modify @LocallySolved $ EMap.insert uni newTy
                            pure $ typeVarOrBody newTy
        C.Name var -> do
            knownVars <- get @(IdMap Name ())
            env <- asks @Env (.values)
            case (Map.lookup var knownVars, Map.lookup var env.values) of
                -- if this var originated from 'generalise', a dependent binder or a lambda, we don't have to do anything
                (Just (), _) -> pure $ C.Name var
                (Nothing, Just solved) -> V.quote solved
                (Nothing, Nothing) -> do
                    skScope <- skolemScope var
                    if skScope <= scope
                        then pure $ C.Name var
                        else do
                            -- if the skolem would escape its scope, we just convert it to an existential or a forall, depending on variance
                            -- i.e. \x -> runST (newSTRef x) : forall a. a -> STRef (exists s. s) a
                            newVar <- freshTypeVar loc
                            modify $ Map.insert newVar ()
                            let quantifier
                                    | variance == Out = Exists
                                    | otherwise = Forall
                            -- todo: we should make a quantifier for the type of the skolem, not just Type
                            pure $ C.Q quantifier Implicit Erased newVar (type_ loc) $ C.Name newVar
        C.Function l r -> C.Function <$> go loc (flipVariance variance) scope l <*> go loc variance scope r
        C.Q q vis e var ty body ->
            C.Q q vis e var <$> go loc variance scope ty <*> do
                modify $ Map.insert var ()
                go loc variance scope body
        C.Lambda var body ->
            C.Lambda var <$> do
                modify $ Map.insert var ()
                go loc variance scope body
        C.Let name _ _ -> internalError (getLoc name) "unexpected let in a quoted type"
        other -> C.coreTraversal (go loc variance scope) other
    typeVarOrBody = either C.Name id

    freshTypeVar :: (State Char :> es, NameGen :> es) => Loc -> Eff es Name
    freshTypeVar loc = do
        id' <- freshId
        letter <- get <* modify cycleChar
        pure $ Located loc $ Name (one letter) id'

    cycleChar 'z' = 'a'
    cycleChar c = succ c

{- | converts a polytype to a monotype, instantiating / skolemizing depending on variance

> mono Out (forall a. a -> a)
> -- ?a -> ?a
> mono In (forall a. a -> a)
> -- #a -> #a
> mono Out (forall a. forall b. a -> b -> a)
> -- ?a -> ?b -> ?a
> mono Out (forall a. (forall b. b -> a) -> a)
> -- (#b -> ?a) -> ?a
-}
mono :: InfEffs es => Variance -> TypeDT -> Eff es Monotype
mono variance = traverse (mono' variance)

mono' :: InfEffs es => Variance -> TypeDT_ -> Eff es Monotype_
mono' variance = \case
    V.Con name args -> MCon name <$> traverse go args
    V.TyCon name args -> MTyCon name <$> traverse go args
    -- V.App lhs rhs -> MApp <$> go lhs <*> go rhs
    V.Function from to -> MFn <$> mono' (flipVariance variance) from <*> go to
    V.VariantT row -> MVariantT <$> traverse go row
    V.RecordT row -> MRecordT <$> traverse go row
    V.Q q Visible e closure -> do
        ty <- go closure.ty
        pure $ MQ q e MonoClosure{var = closure.var, variance, env = closure.env, ty, body = closure.body}
    V.Q Forall _ _ closure -> go =<< substitute variance closure
    V.Q Exists _ _ closure -> go =<< substitute (flipVariance variance) closure
    V.PrimFunction{} -> internalError' "mono: prim function"
    V.PrimValue val -> pure $ MPrim val
    V.Record row -> MRecord <$> traverse go row
    V.Sigma x y -> MSigma <$> go x <*> go y
    V.Variant name arg -> MVariant name <$> go arg
    -- V.Case arg matches -> MCase <$> go arg <*> pure (fmap monoPatternClosure matches)
    V.Lambda closure -> pure $ MLambda MonoClosure{var = closure.var, variance, env = closure.env, ty = (), body = closure.body}
    V.Stuck reason spine -> MStuck reason <$> traverse monoSpine spine
  where
    go = mono' variance
    monoSpine = \case
        V.App rhs -> MApp <$> go rhs
        V.Case matches -> pure $ MCase $ fmap monoPatternClosure matches
        V.Fn{} -> internalError' "mono: prim function" -- todo
    monoPatternClosure V.PatternClosure{pat, ty, env, body} = MonoPatternClosure{pat, ty, variance, env, body}

appMono :: InfEffs es => MonoClosure a -> Value -> Eff es Monotype_
appMono MonoClosure{var, variance, env, body} arg = mono' variance $ V.evalCore (env{V.values = Map.insert var arg env.values}) body

flipVariance :: Variance -> Variance
flipVariance = \case
    In -> Out
    Out -> In
    Inv -> Inv

unMono :: Monotype -> TypeDT
unMono = fmap unMono'
unMono' :: Monotype_ -> TypeDT_
unMono' = \case
    MCon name args -> V.Con name (map unMono' args)
    MTyCon name args -> V.TyCon name (map unMono' args)
    MFn from to -> V.Function (unMono' from) (unMono' to)
    MVariantT row -> V.VariantT $ fmap unMono' row
    MRecordT row -> V.RecordT $ fmap unMono' row
    MVariant name val -> V.Variant name (unMono' val)
    MRecord row -> V.Record (fmap unMono' row)
    MSigma x y -> V.Sigma (unMono' x) (unMono' y)
    MLambda MonoClosure{var, ty, env, body} -> V.Lambda V.Closure{var, ty, env, body}
    MQ q e MonoClosure{var, ty, env, body} -> V.Q q Visible e V.Closure{var, ty = unMono' ty, env, body}
    MPrim val -> V.PrimValue val
    MPrimFn fn -> V.PrimFunction $ monoPrimFn fn
    MStuck reason spine -> V.Stuck reason $ fmap unMonoSpine spine
  where
    unMonoSpine = \case
        MApp rhs -> V.App (unMono' rhs)
        MCase matches -> V.Case $ fmap toPatternClosure matches
        MStuckFn fn -> V.Fn $ monoPrimFn fn
    toPatternClosure MonoPatternClosure{pat, ty, env, body} = V.PatternClosure{pat, ty, env, body}
    monoPrimFn MonoPrimFunc{name, remaining, captured, f} = V.PrimFunc{name, remaining, captured = map unMono' captured, f}

{- unwraps forall/exists clauses in a type until a monomorphic constructor is encountered

> monoLayer Out (forall a. a -> a)
> -- ?a -> ?a
> monoLayer In (forall a. a -> a)
> -- #a -> #a
> monoLayer Out (forall a. a -> forall b. b -> a)
> -- ?a -> forall b. b -> ?a
> monoLayer Out (forall a. (forall b. b -> a) -> a)
> -- (forall b. b -> ?a) -> ?a
-}
monoLayer :: InfEffs es => Variance -> TypeDT -> Eff es TypeDT
monoLayer variance = traverse (monoLayer' variance)
monoLayer' :: InfEffs es => Variance -> TypeDT_ -> Eff es TypeDT_
monoLayer' variance = \case
    V.Q q Visible e closure -> pure $ V.Q q Visible e closure
    -- todo: I'm not sure how to handle erased vs retained vars yet
    -- in theory, no value may depend on an erased var
    V.Q Forall _ _e closure -> monoLayer' variance =<< substitute variance closure
    V.Q Exists _ _e closure -> monoLayer' variance =<< substitute (flipVariance variance) closure
    other -> pure other

-- WARN: substitute doesn't traverse univars at the moment
substitute :: InfEffs es => Variance -> V.Closure a -> Eff es TypeDT_
substitute variance closure = (.result) <$> substitute' variance closure

data Subst = Subst {var :: TypeDT_, result :: TypeDT_}

-- substitute a type variable with a univar / skolem dependening on variance
substitute' :: InfEffs es => Variance -> V.Closure a -> Eff es Subst
substitute' variance closure = do
    someVar <- freshSomething (toSimpleName closure.var) variance
    pure Subst{var = someVar, result = closure `V.app` someVar}
  where
    -- freshUniVar or freshSkolem, depending on variance
    -- should it be the other way around?
    --
    -- out: forall a. Int -> a
    -- in: forall a. a -> Int
    freshSomething name = \case
        In -> freshUniVar
        Out -> freshSkolem name
        Inv -> freshSkolem name

-- what to match
data RecordOrVariant = Record | Variant deriving (Eq)
conOf :: RecordOrVariant -> ExtRow TypeDT_ -> TypeDT_
conOf Record = V.RecordT
conOf Variant = V.VariantT

{- | lookup a field in a type, assuming that the type is a row type
-- if a univar is encountered, it's solved to a row type
--
-- Note: repetitive calls of deepLookup on an open row turn it into a chain of singular extensions
-- you should probably call `compress` after that
-}
deepLookup :: InfEffs es => RecordOrVariant -> Row.OpenName -> TypeDT -> Eff es (Maybe TypeDT)
deepLookup whatToMatch k = fmap sequence . traverse go
  where
    go :: InfEffs es => TypeDT_ -> Eff es (Maybe TypeDT_)
    go =
        monoLayer' Out >=> \case
            V.RecordT nextRow
                | whatToMatch == Record -> deepLookup' nextRow
            V.VariantT nextRow
                | whatToMatch == Variant -> deepLookup' nextRow
            V.UniVar uni ->
                lookupUniVar uni >>= \case
                    Right ty -> go $ unMono' $ unLoc ty
                    Left _ -> do
                        fieldType <- MUniVar <$> freshUniVar'
                        rowVar <- MUniVar <$> freshUniVar'
                        let con = case whatToMatch of
                                Variant -> MVariantT
                                Record -> MRecordT
                        solveUniVar uni $ Located idk $ con $ ExtRow (one (k, fieldType)) rowVar
                        pure $ Just $ unMono' fieldType
            -- V.Skolem{} -> _ -- todo: handle solved skolems?

            -- there's no point in explicitly listing all of the cases, since
            -- deepLookup only looks at records, variants and univars
            _ -> pure Nothing

    deepLookup' :: InfEffs es => ExtRow TypeDT_ -> Eff es (Maybe TypeDT_)
    deepLookup' extRow = case Row.lookup k extRow.row of
        Just v -> pure $ Just v
        Nothing -> case Row.extension extRow of
            Nothing -> pure Nothing
            Just ext -> go ext

    idk = Loc Position{file = "<todo: deepLookup univars have no position info>", begin = (0, 0), end = (0, 0)}

{- | compresses known row extensions of a row

@{ x : Int | y : Double | z : Char | r } -> { x : Int, y : Double, z : Char | r }@
-}
compress :: InfEffs es => RecordOrVariant -> Variance -> ExtRow TypeDT_ -> Eff es (ExtRow TypeDT_)
compress _ _ row@NoExtRow{} = pure row
compress whatToMatch variance (ExtRow row ext) = Row.extend row <$> go ext
  where
    go =
        monoLayer' variance >=> \case
            V.RecordT nextRow
                | whatToMatch == Record -> compress whatToMatch variance nextRow
            V.VariantT nextRow
                | whatToMatch == Variant -> compress whatToMatch variance nextRow
            v@(V.UniVar uni) ->
                lookupUniVar uni >>= \case
                    Right ty -> go $ unMono' $ unLoc ty
                    Left _ -> pure $ ExtRow Row.empty v
            other -> pure $ ExtRow Row.empty other
