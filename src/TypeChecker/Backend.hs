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

module TypeChecker.Backend where

import Common
import Data.EnumMap.Strict qualified as EMap
import Data.EnumSet qualified as Set
import Data.Traversable (for)
import Diagnostic (Diagnose, internalError, internalError')
import Effectful
import Effectful.Dispatch.Dynamic (reinterpret)
import Effectful.Error.Static (runErrorNoCallStack, throwError_)
import Effectful.Labeled
import Effectful.Reader.Static (Reader, ask, asks, local, runReader)
import Effectful.State.Static.Local (State, evalState, get, gets, modify, runState)
import Effectful.TH
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
import Syntax.Term (Erased (..), Quantifier (..), Visibility (..))
import TypeChecker.TypeError

type Pat = Pattern 'Fixity
type TypeDT = Located Value
type TypeDT_ = Value
type Type' = Located Value
type Type'_ = Value

type Monotype = Located Monotype_
data Monotype_
    = MCon Name [Monotype_]
    | MTyCon Name
    | MLambda (MonoClosure ())
    | MRecord (Row Monotype_)
    | MSigma Monotype_ Monotype_
    | MVariant OpenName Monotype_
    | MPrim Literal
    | -- types
      MFn Monotype_ Monotype_
    | MQ Quantifier Erased (MonoClosure Monotype_)
    | MVariantT (ExtRow Monotype_)
    | MRecordT (ExtRow Monotype_)
    | -- stuck computations
      MApp Monotype_ ~Monotype_
    | MCase Monotype_ [MonoPatternClosure ()]
    | -- typechecking metavars
      MUniVar UniVar
    | MSkolem Skolem

data MonoClosure ty = MonoClosure {var :: Name, variance :: Variance, ty :: ty, env :: ValueEnv, body :: CoreTerm}
data MonoPatternClosure ty = MonoPatternClosure {pat :: CorePattern, variance :: Variance, ty :: ty, env :: ValueEnv, body :: CoreTerm}
data Variance = In | Out | Inv

data Env = Env
    { scope :: Scope
    , values :: ValueEnv
    , locals :: IdMap Name TypeDT
    }

-- the types of top-level bindings should not contain metavars
-- this is not enforced at type level, though
type TopLevel = IdMap Name Type'
type UniVars = EnumMap UniVar (Either Scope Monotype) -- should we use located Monotypes here? I'm not sure
type InfEffs es =
    ( NameGen :> es
    , Labeled UniVar NameGen :> es
    , State UniVars :> es
    , State (IdMap Skolem Scope) :> es
    , State TopLevel :> es
    , Reader Env :> es
    , Diagnose :> es
    )

data Break err :: Effect where
    Break :: err -> Break err m a

makeEffect ''Break

runBreak :: forall err a es. Eff (Break err : es) a -> Eff es (Either err a)
runBreak = reinterpret (runErrorNoCallStack @err) \_ (Break val) -> throwError_ @err val

instance Pretty Monotype_ where
    pretty = pretty . unMono'

run
    :: ValueEnv
    -> Eff (Reader Env : State UniVars : State (IdMap Skolem Scope) : Labeled UniVar NameGen : es) a
    -> Eff es a
run values action =
    runLabeled @UniVar runNameGen
        . evalState Map.empty
        . evalState @UniVars EMap.empty
        $ runReader initState action
  where
    initState =
        Env
            { scope = Scope 0
            , values
            , locals = Map.empty
            }

freshUniVar :: InfEffs es => Eff es TypeDT_
freshUniVar = V.UniVar <$> freshUniVar'

freshUniVar' :: InfEffs es => Eff es UniVar
freshUniVar' = do
    -- c'mon effectful
    var <- UniVar <$> labeled @UniVar @NameGen freshId
    scope <- asks @Env (.scope)
    modify @UniVars $ EMap.insert var (Left scope)
    pure var

freshSkolem :: InfEffs es => SimpleName -> Eff es TypeDT_
freshSkolem name = do
    -- skolems are generally derived from type variables, so they have names
    scope <- asks @Env (.scope)
    skolem <- Skolem <$> mkName name
    modify $ Map.insert skolem scope
    pure $ V.Skolem skolem
  where
    mkName (Located loc (Name' txtName)) = Located loc <$> freshName_ (Name' txtName)
    mkName _ = freshName (Located (getLoc name) $ Name' "what") -- why?

lookupUniVar :: InfEffs es => UniVar -> Eff es (Either Scope Monotype)
lookupUniVar uni = maybe (internalError' $ "missing univar" <+> pretty uni) pure . EMap.lookup uni =<< get @UniVars

withUniVar :: InfEffs es => UniVar -> (Monotype -> Eff es a) -> Eff es ()
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
                    internalError (getLoc ty) $ "attempted to solve a solved univar " <> pretty uni
            Right _ -> pure Nothing
            Left scope -> pure $ Just scope
    cycle <- cycleCheck mbScope (Direct, Set.singleton uni) ty
    when (cycle == NoCycle) $ modify @UniVars $ EMap.insert uni (Right ty)
  where
    -- errors out on indirect cycles (i.e. a ~ Maybe a)
    -- returns False on direct univar cycles (i.e. a ~ b, b ~ c, c ~ a)
    -- returns True when there are no cycles
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
                            Just scope | scope' > scope -> modify @UniVars $ EMap.insert uni2 (Left scope')
                            _ -> pass
                        pure NoCycle
            MFn from to -> go (Indirect, acc) from >> go (Indirect, acc) to
            MQ _q _e closure -> go (Indirect, acc) closure.ty *> cycleCheckClosure acc closure
            MCon _ args -> NoCycle <$ traverse_ (go (Indirect, acc)) args
            MApp lhs rhs -> go (Indirect, acc) lhs >> go (Indirect, acc) rhs
            MVariantT row -> NoCycle <$ traverse_ (go (Indirect, acc)) row
            MRecordT row -> NoCycle <$ traverse_ (go (Indirect, acc)) row
            MVariant _ val -> go (Indirect, acc) val
            MRecord row -> NoCycle <$ traverse_ (go (Indirect, acc)) row
            MSigma x y -> go (Indirect, acc) x >> go (Indirect, acc) y
            MLambda closure -> cycleCheckClosure acc closure
            MCase _arg _matches -> internalError' "todo: cycleCheck stuck MCase" -- go (Indirect, acc) arg <* traverse_ _what matches
            MTyCon{} -> pure NoCycle
            MSkolem{} -> pure NoCycle
            MPrim{} -> pure NoCycle

        cycleCheckClosure :: EnumSet UniVar -> MonoClosure a -> Eff es Cycle
        cycleCheckClosure acc closure = do
            skolem <- freshSkolem $ toSimpleName closure.var
            go (Indirect, acc) =<< appMono closure skolem
    unwrap = traverse \case
        uni2@(MUniVar var) ->
            lookupUniVar var >>= \case
                Right refTy -> unLoc <$> unwrap refTy
                Left{} -> pure uni2
        other -> pure other

skolemScope :: InfEffs es => Skolem -> Eff es Scope
skolemScope skolem =
    maybe (internalError (getLoc skolem) $ "missing skolem" <+> pretty skolem) pure
        . Map.lookup skolem
        =<< get @(_ Skolem _)

-- looks up a type of a binding. Global bindings take precedence over local ones (should they?)
lookupSig :: InfEffs es => Name -> Eff es TypeDT
lookupSig name = do
    topLevel <- get
    locals <- asks @Env (.locals)
    case (Map.lookup name topLevel, Map.lookup name locals) of
        (Just ty, _) -> pure ty
        (_, Just ty) -> pure ty
        (Nothing, Nothing) -> do
            -- assuming that type checking is performed after name resolution,
            -- we may just treat unbound names as holes
            -- every occurence of an unbound name should get a new UniVar
            -- (even then, unbound names are supposed to have unique ids)
            Located (getLoc name) <$> freshUniVar

-- | `local` monomorphised to `Env`
local' :: Reader Env :> es => (Env -> Env) -> Eff es a -> Eff es a
local' = local

declareTopLevel :: InfEffs es => IdMap Name Type' -> Eff es ()
declareTopLevel types = modify (types <>)

declareTopLevel' :: InfEffs es => Name -> Type' -> Eff es ()
declareTopLevel' name ty = modify $ Map.insert name ty

declare :: Name -> TypeDT -> Env -> Env
declare name ty env = env{locals = LMap.insert name ty env.locals}

declareMany :: IdMap Name TypeDT -> Env -> Env
declareMany typeMap env = env{locals = typeMap <> env.locals}

define :: Name -> Value -> Env -> Env
define name val env = env{values = env.values{V.values = LMap.insert name val env.values.values}}

defineMany :: IdMap Name Value -> Env -> Env
defineMany valMap env = env{values = env.values{V.values = valMap <> env.values.values}}

-- defineMany :: EnumMap Name Value -> Env -> Env
-- defineMany vals env = env{values = env.values{V.values = vals <> env.values.values}}

generalise :: InfEffs es => Eff es TypeDT -> Eff es TypeDT
generalise = fmap runIdentity . generaliseAll . fmap Identity

generaliseAll :: (Traversable t, InfEffs es) => Eff es (t TypeDT) -> Eff es (t TypeDT)
generaliseAll action = do
    Scope n <- asks @Env (.scope)
    types <- local' (\e -> e{scope = Scope $ succ n}) action
    traverse generaliseOne types
  where
    generaliseOne ty@(Located loc _) = do
        env <- ask @Env
        (ty', vars) <- runState EMap.empty $ evalState 'a' $ go env.scope =<< V.quote ty
        let forallVars = hashNub . lefts $ toList vars
        pure $
            Located loc $
                V.evalCore env.values $
                    foldr (\var body -> Located loc $ C.Q Forall Implicit Erased var (type_ loc) body) ty' forallVars
    type_ loc = Located loc $ C.TyCon $ Located loc TypeName

    go :: InfEffs es => Scope -> CoreTerm -> Eff (State Char : State (EnumMap UniVar (Either Name CoreTerm)) : es) CoreTerm
    go scope (Located loc term) =
        Located loc <$> case term of
            C.UniVar uni -> do
                whenNothingM (fmap toTypeVar <$> gets @(EnumMap UniVar (Either Name CoreTerm)) (EMap.lookup uni)) do
                    lookupUniVar uni >>= \case
                        -- don't generalise outer-scoped vars
                        Left varScope | varScope <= scope -> pure $ C.UniVar uni
                        innerScoped -> do
                            newTy <- bitraverse (const $ freshTypeVar loc) (go scope <=< V.quote . unMono) innerScoped
                            modify @(EnumMap UniVar (Either Name CoreTerm)) $ EMap.insert uni newTy
                            pure $ toTypeVar newTy
            C.Skolem skolem -> do
                skScope <- skolemScope skolem
                if skScope > scope
                    then do
                        -- if the skolem would escape its scope, we just convert it to an existential
                        -- i.e. \x -> runST (newSTRef x) : forall a. a -> STRef (exists s. s) a
                        -- wait, a skolem may occur to the left of a function arrow, so such a conversion
                        -- is not always correct
                        var <- freshTypeVar loc
                        pure $ C.Q Exists Implicit Erased var (type_ loc) $ Located (getLoc var) $ C.Name var
                    else pure $ C.Skolem skolem
            -- simple recursive cases
            C.Function l r -> C.Function <$> go scope l <*> go scope r
            C.App lhs rhs -> C.App <$> go scope lhs <*> go scope rhs
            C.RecordT row -> C.RecordT <$> traverse (go scope) row
            C.VariantT row -> C.VariantT <$> traverse (go scope) row
            C.Record row -> C.Record <$> traverse (go scope) row
            C.Sigma x y -> C.Sigma <$> go scope x <*> go scope y
            C.Q q vis e var ty body -> C.Q q vis e var <$> go scope ty <*> go scope body
            C.Lambda var body -> C.Lambda var <$> go scope body
            C.Con name args -> C.Con name <$> traverse (go scope) args
            -- terminal cases
            C.Name name -> pure $ C.Name name
            C.TyCon name -> pure $ C.TyCon name
            C.Literal v -> pure $ C.Literal v
            C.Variant con -> pure $ C.Variant con
            C.Case arg matches -> C.Case arg <$> for matches \(pat, body) -> (pat,) <$> go scope body
            C.Let name _ _ -> internalError (getLoc name) "unexpected let in a quoted type"

    toTypeVar = either C.Name unLoc

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
    V.Var var -> internalError (getLoc var) $ "mono: dangling var" <+> pretty var
    V.Con name args -> MCon name <$> traverse go args
    V.TyCon name -> pure $ MTyCon name
    V.Skolem skolem -> pure $ MSkolem skolem
    V.UniVar uni -> pure $ MUniVar uni
    V.App lhs rhs -> MApp <$> go lhs <*> go rhs
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
    V.Case arg matches -> MCase <$> go arg <*> pure (fmap monoPatternClosure matches)
    V.Lambda closure -> pure $ MLambda MonoClosure{var = closure.var, variance, env = closure.env, ty = (), body = closure.body}
  where
    go = mono' variance
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
    MTyCon name -> V.TyCon name
    MSkolem skolem -> V.Skolem skolem
    MUniVar uniVar -> V.UniVar uniVar
    MApp lhs rhs -> V.App (unMono' lhs) (unMono' rhs)
    MFn from to -> V.Function (unMono' from) (unMono' to)
    MVariantT row -> V.VariantT $ fmap unMono' row
    MRecordT row -> V.RecordT $ fmap unMono' row
    MVariant name val -> V.Variant name (unMono' val)
    MRecord row -> V.Record (fmap unMono' row)
    MSigma x y -> V.Sigma (unMono' x) (unMono' y)
    MLambda MonoClosure{var, ty, env, body} -> V.Lambda V.Closure{var, ty, env, body}
    MQ q e MonoClosure{var, ty, env, body} -> V.Q q Visible e V.Closure{var, ty = unMono' ty, env, body}
    MPrim val -> V.PrimValue val
    MCase arg matches -> V.Case (unMono' arg) (fmap toPatternClosure matches)
  where
    toPatternClosure MonoPatternClosure{pat, ty, env, body} = V.PatternClosure{pat, ty, env, body}

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
