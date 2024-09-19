{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE NoFieldSelectors #-}

module TypeChecker (
    run,
    runWithFinalEnv,
    infer,
    inferPattern,
    inferBinding,
    check,
    checkPattern,
    subtype,
    inferTypeVars,
    normalise,
    Builtins (..),
    InfState (..),
    TypeError (..),
    InfEffs,
    typecheck,
) where

import CheckerTypes
import Control.Monad (foldM)
import Data.Foldable1 (foldr1)
import Data.HashMap.Strict qualified as HashMap
import Data.HashSet qualified as HashSet
import Data.Text qualified as Text
import Data.Traversable (for)
import Effectful
import Effectful.Error.Static (Error, runErrorNoCallStack, throwError)
import Effectful.Reader.Static (Reader, ask, asks, runReader)
import Effectful.State.Static.Local (State, get, gets, modify, runState)
import GHC.IsList qualified as IsList
import NameGen
import Prettyprinter (Doc, Pretty, pretty, (<+>))
import Relude hiding (Reader, State, Type, ask, asks, bool, get, gets, modify, put, runReader, runState)
import Syntax
import Syntax.Declaration qualified as D
import Syntax.Expression qualified as E
import Syntax.Pattern qualified as P
import Syntax.Row (ExtRow (..))
import Syntax.Row qualified as Row
import Syntax.Type qualified as T
import Prelude (show)

type Expr = Expression Name
type Pattern' = Pattern Name

type Type = Type' Name

data Monotype
    = MName Name
    | MSkolem Skolem
    | MUniVar UniVar
    | MVar Name -- a (probably out of scope) type var
    | MApp Monotype Monotype
    | MFn Monotype Monotype
    | MVariant (ExtRow Monotype)
    | MRecord (ExtRow Monotype)
    deriving (Show, Eq)

-- а type whose outer constructor is monomorphic
data MonoLayer
    = MLName Name
    | MLSkolem Skolem
    | MLUniVar UniVar
    | MLVar Name
    | MLApp Type Type
    | MLFn Type Type
    | MLVariant (ExtRow Type)
    | MLRecord (ExtRow Type)
    deriving (Show, Eq)

newtype TypeError = TypeError (Doc ()) deriving (Show)

newtype Builtins a = Builtins
    { subtypeRelations :: [(a, a)]
    }
    deriving (Show, Functor, Foldable, Traversable)

-- calling an uninferred type closure should introduce all of the inferred bindings
-- into the global scope
newtype UninferredType = UninferredType (forall es. InfEffs es => Eff es Type)
instance Show UninferredType where
    show _ = "<closure>"

type TopLevelBindings = HashMap Name (Either UninferredType Type)

data InfState = InfState
    { nextUniVarId :: Int
    , nextTypeVar :: Char
    , currentScope :: Scope
    , topLevel :: TopLevelBindings
    -- ^ top level bindings that may or may not have a type signature.
    --       only solved types may appear here, but it's not clear whether
    --       it's worth it to make that distinction at type level
    , locals :: HashMap Name Type -- local variables
    , vars :: HashMap UniVar (Either Scope Monotype) -- contains either the scope of an unsolved var or a type
    }
    deriving (Show)

type InfEffs es = (NameGen :> es, State InfState :> es, Error TypeError :> es, Reader (Builtins Name) :> es)

instance Pretty Monotype where
    pretty = pretty . unMono

instance Pretty MonoLayer where
    pretty = pretty . unMonoLayer

-- helpers

typecheck
    :: NameGen :> es
    => HashMap Name Type -- imports
    -> Builtins Name
    -> [Declaration Name]
    -> Eff es (Either TypeError (HashMap Name Type))
typecheck env builtins decls = run (Right <$> env) builtins $ traverse normalise =<< inferDecls decls

run
    :: TopLevelBindings
    -> Builtins Name
    -> Eff (Error TypeError : Reader (Builtins Name) : State InfState : es) a
    -> Eff es (Either TypeError a)
run env builtins = fmap fst . runWithFinalEnv env builtins

runWithFinalEnv
    :: TopLevelBindings
    -> Builtins Name
    -> Eff (Error TypeError : Reader (Builtins Name) : State InfState : es) a
    -> Eff es (Either TypeError a, InfState)
runWithFinalEnv env builtins = do
    runState
        InfState
            { nextUniVarId = 0
            , nextTypeVar = 'a'
            , currentScope = Scope 0
            , topLevel = env
            , locals = HashMap.empty
            , vars = HashMap.empty
            }
        . runReader builtins
        . runErrorNoCallStack

typeError :: InfEffs es => Doc () -> Eff es a
typeError err = throwError $ TypeError err

freshUniVar :: InfEffs es => Eff es (Type' n)
freshUniVar = do
    -- and this is where I wish I had lens
    var <- UniVar <$> gets @InfState (.nextUniVarId) <* modify @InfState \s -> s{nextUniVarId = succ s.nextUniVarId}
    scope <- gets @InfState (.currentScope)
    modify \s -> s{vars = HashMap.insert var (Left scope) s.vars}
    pure $ T.UniVar var

freshSkolem :: InfEffs es => Name -> Eff es Type
freshSkolem (Name name _) = T.Skolem . Skolem <$> freshName name
freshSkolem _ = T.Skolem . Skolem <$> freshName "what" -- why? 

freshTypeVar :: InfEffs es => Eff es Name
freshTypeVar = do
    id' <- freshId
    letter <- gets @InfState (.nextTypeVar) <* modify \s -> s{nextTypeVar = cycleChar s.nextTypeVar}
    pure $ Name (Text.singleton letter) id'
  where
    cycleChar 'z' = 'a'
    cycleChar c = succ c

lookupUniVar :: InfEffs es => UniVar -> Eff es (Either Scope Monotype)
lookupUniVar uni = maybe (typeError $ "missing univar " <> pretty uni) pure . HashMap.lookup uni =<< gets @InfState (.vars)

withUniVar :: InfEffs es => UniVar -> (Monotype -> Eff es a) -> Eff es ()
withUniVar uni f =
    lookupUniVar uni >>= \case
        Left _ -> pass
        Right ty -> void $ f ty

solveUniVar, overrideUniVar :: InfEffs es => UniVar -> Monotype -> Eff es ()
solveUniVar = alterUniVar False
overrideUniVar = alterUniVar True

data SelfRef = Direct | Indirect

alterUniVar :: InfEffs es => Bool -> UniVar -> Monotype -> Eff es ()
alterUniVar override uni ty = do
    -- here comes the magic. If the new type contains other univars, we change their scope
    lookupUniVar uni >>= \case
        Right _ | not override -> typeError $ "Internal error (probably a bug): attempted to solve a solved univar " <> pretty uni
        Right _ -> pass
        Left scope -> rescope scope ty
    noCycle <- cycleCheck (Direct, HashSet.singleton uni) ty
    when noCycle $ modify \s -> s{vars = HashMap.insert uni (Right ty) s.vars}
  where
    foldUniVars :: InfEffs es => (UniVar -> Eff es ()) -> Monotype -> Eff es ()
    foldUniVars action = \case
        MUniVar v -> action v >> lookupUniVar v >>= either (const pass) (foldUniVars action)
        MApp lhs rhs -> foldUniVars action lhs >> foldUniVars action rhs
        MFn from to -> foldUniVars action from >> foldUniVars action to
        MVariant row -> traverse_ (foldUniVars action) row
        MRecord row -> traverse_ (foldUniVars action) row
        MName _ -> pass
        MSkolem _ -> pass
        MVar _ -> pass

    -- errors out on indirect cycles (i.e. a ~ Maybe a)
    -- returns False on direct univar cycles (i.e. a ~ b, b ~ c, c ~ a)
    -- returns True when there are no cycles
    cycleCheck (selfRefType, acc) = \case
        MUniVar uni2 | HashSet.member uni2 acc -> case selfRefType of
            Direct -> pure False
            Indirect -> typeError "self-referential type"
        MUniVar uni2 ->
            lookupUniVar uni2 >>= \case
                Left _ -> pure True
                Right ty' -> cycleCheck (selfRefType, HashSet.insert uni2 acc) ty'
        MFn from to -> cycleCheck (Indirect, acc) from >> cycleCheck (Indirect, acc) to
        MApp lhs rhs -> cycleCheck (Indirect, acc) lhs >> cycleCheck (Indirect, acc) rhs
        MVariant row -> True <$ traverse_ (cycleCheck (Indirect, acc)) row
        MRecord row -> True <$ traverse_ (cycleCheck (Indirect, acc)) row
        MName _ -> pure True
        MSkolem _ -> pure True
        MVar _ -> pure True

    rescope scope = foldUniVars \v -> lookupUniVar v >>= either (rescopeVar v scope) (const pass)
    rescopeVar v scope oldScope = modify \s -> s{vars = HashMap.insert v (Left $ min oldScope scope) s.vars}

-- looks up a type of a binding. If it's an uninferred global binding, it infers it first
lookupSig :: InfEffs es => Name -> Eff es Type
lookupSig name = do
    InfState{topLevel, locals} <- get @InfState
    case HashMap.lookup name topLevel of
        Just (Left (UninferredType closure)) -> closure
        Just (Right ty) -> pure ty
        Nothing -> case HashMap.lookup name locals of
            Just ty -> pure ty
            Nothing -> do
                -- assuming that type checking is performed after name resolution,
                -- all encountered names have to be in scope
                uni <- freshUniVar
                uni <$ updateSig name uni

updateSig :: InfEffs es => Name -> Type -> Eff es ()
updateSig name ty = modify \s -> s{locals = HashMap.insert name ty s.locals}

declareAll :: InfEffs es => HashMap Name Type -> Eff es ()
declareAll types = modify \s -> s{locals = types <> s.locals}

declareTopLevel :: InfEffs es => HashMap Name Type -> Eff es ()
declareTopLevel types = modify \s -> s{topLevel = Right <$> types <> s.locals}

builtin :: Reader (Builtins Name) :> es => (Builtins Name -> a) -> Eff es a
builtin = asks @(Builtins Name)

-- | run the given action and discard signature updates
scoped :: InfEffs es => Eff es a -> Eff es a
scoped action = do
    locals <- gets @InfState (.locals)
    action <* modify \s -> s{locals}

-- turns out it's tricky to get this function right.
-- just taking all of the new univars and turning them into type vars is not enough,
-- since a univar may be produced when specifying a univar from parent scope (i.e. `#a` to `#b -> #c`)
forallScope :: InfEffs es => Eff es Type -> Eff es Type
forallScope action = do
    start <- gets @InfState (.nextUniVarId)
    modify \s@InfState{currentScope = Scope n} -> s{currentScope = Scope $ succ n}
    out <- action
    modify \s@InfState{currentScope = Scope n} -> s{currentScope = Scope $ pred n}
    end <- pred <$> gets @InfState (.nextUniVarId)
    outerScope <- gets @InfState (.currentScope)
    -- I'm not sure whether it's sound to convert all skolems in scope
    -- skolems may need a scope approach similar to univars
    -- skolemsToExists =<<
    foldM (applyVar outerScope) out (UniVar <$> [start .. end])
  where
    applyVar outerScope bodyTy uni =
        lookupUniVar uni >>= \case
            Right ty -> do
                substituteTy (T.UniVar uni) ty bodyTy
            Left scope | scope > outerScope && isRelevant uni bodyTy -> do
                tyVar <- freshTypeVar
                solveUniVar uni (MVar tyVar)
                pure $ T.Forall tyVar bodyTy
            Left _ -> pure bodyTy
    isRelevant uni = \case
        T.UniVar v -> v == uni
        T.Forall _ body' -> isRelevant uni body'
        T.Exists _ body' -> isRelevant uni body'
        T.Function from to -> isRelevant uni from || isRelevant uni to
        T.Application lhs rhs -> isRelevant uni lhs || isRelevant uni rhs
        T.Variant row -> any (isRelevant uni) row
        T.Record row -> any (isRelevant uni) row
        T.Name _ -> False
        T.Var _ -> False
        T.Skolem _ -> False

--

data Variance = In | Out | Inv

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
mono :: InfEffs es => Variance -> Type -> Eff es Monotype
mono variance = \case
    v@T.Var{} -> typeError $ "unbound type variable" <+> pretty v
    T.Name name -> pure $ MName name
    T.Skolem skolem -> pure $ MSkolem skolem
    T.UniVar uni -> pure $ MUniVar uni
    T.Application lhs rhs -> MApp <$> go lhs <*> go rhs
    T.Function from to -> MFn <$> mono (flipVariance variance) from <*> go to
    T.Variant row -> MVariant <$> traverse go row
    T.Record row -> MRecord <$> traverse go row
    T.Forall var body -> go =<< substitute variance var body
    T.Exists var body -> go =<< substitute (flipVariance variance) var body
  where
    go = mono variance

flipVariance :: Variance -> Variance
flipVariance = \case
    In -> Out
    Out -> In
    Inv -> Inv

unMono :: Monotype -> Type
unMono = \case
    MName name -> T.Name name
    MSkolem skolem -> T.Skolem skolem
    MUniVar uniVar -> T.UniVar uniVar
    MVar var -> T.Var var
    MApp lhs rhs -> T.Application (unMono lhs) (unMono rhs)
    MFn from to -> T.Function (unMono from) (unMono to)
    MVariant row -> T.Variant $ fmap unMono row
    MRecord row -> T.Record $ fmap unMono row

{- unwraps forall/exists clauses in a type until a monomorphic constructor is encountered

> monoLayer Out (forall a. a -> a)
> -- ?a -> ?a
> monoLayer In (forall a. a -> a)
> -- #a -> #a
> monoLayer Out (forall a. forall b. a -> b -> a)
> -- forall b. ?a -> b -> ?a
> monoLayer Out (forall a. (forall b. b -> a) -> a)
> -- (forall b. b -> ?a) -> ?a
-}
monoLayer :: InfEffs es => Variance -> Type -> Eff es MonoLayer
monoLayer variance = \case
    v@T.Var{} -> typeError $ "unbound type variable" <+> pretty v
    T.Name name -> pure $ MLName name
    T.Skolem skolem -> pure $ MLSkolem skolem
    T.UniVar uni -> pure $ MLUniVar uni
    T.Application lhs rhs -> pure $ MLApp lhs rhs
    T.Function from to -> pure $ MLFn from to
    T.Variant row -> pure $ MLVariant row
    T.Record row -> pure $ MLRecord row
    T.Forall var body -> monoLayer variance =<< substitute variance var body
    T.Exists var body -> monoLayer variance =<< substitute (flipVariance variance) var body

unMonoLayer :: MonoLayer -> Type
unMonoLayer = \case
    MLName name -> T.Name name
    MLSkolem skolem -> T.Skolem skolem
    MLUniVar uni -> T.UniVar uni
    MLVar name -> T.Var name
    MLApp lhs rhs -> T.Application lhs rhs
    MLFn lhs rhs -> T.Function lhs rhs
    MLVariant row -> T.Variant row
    MLRecord row -> T.Record row

substitute :: InfEffs es => Variance -> Name -> Type -> Eff es Type
substitute variance var ty = do
    someVar <- freshSomething var variance
    go someVar ty
  where
    go replacement = \case
        T.Var v | v == var -> pure replacement
        T.Var name -> pure $ T.Var name
        T.UniVar uni -> pure $ T.UniVar uni
        T.Forall v body
            | v /= var -> T.Forall v <$> go replacement body
            | otherwise -> pure $ T.Forall v body
        T.Exists v body
            | v /= var -> T.Exists v <$> go replacement body
            | otherwise -> pure $ T.Exists v body
        T.Function from to -> T.Function <$> go replacement from <*> go replacement to
        T.Application lhs rhs -> T.Application <$> go replacement lhs <*> go replacement rhs
        T.Variant row -> T.Variant <$> traverse (go replacement) row
        T.Record row -> T.Record <$> traverse (go replacement) row
        name@T.Name{} -> pure name
        skolem@T.Skolem{} -> pure skolem

    -- freshUniVar or freshSkolem, depending on variance
    -- should it be the other way around?
    --
    -- out: forall a. Int -> a
    -- in: forall a. a -> Int
    freshSomething name = \case
        In -> freshUniVar
        Out -> freshSkolem name
        Inv -> freshSkolem name

-- `substituteTy` shouldn't be used for type vars, because it fails in cases like `forall a. (forall a. body)`
-- normally those are removed by name resolution, but they may still occur when checking, say `f (f x)`
substituteTy :: InfEffs es => Type -> Monotype -> Type -> Eff es Type
substituteTy from to = go
  where
    go = \case
        ty | ty == from -> pure $ unMono to
        T.UniVar uni -> T.UniVar uni <$ withUniVar uni (pure . unMono >=> go >=> mono Inv >=> overrideUniVar uni)
        T.Forall v body -> T.Forall v <$> go body
        T.Exists v body -> T.Exists v <$> go body
        T.Function in' out' -> T.Function <$> go in' <*> go out'
        T.Application lhs rhs -> T.Application <$> go lhs <*> go rhs
        T.Variant row -> T.Variant <$> traverse go row
        T.Record row -> T.Record <$> traverse go row
        v@T.Var{} -> pure v
        skolem@T.Skolem{} -> pure skolem
        name@T.Name{} -> pure name

-- gets rid of all univars
normalise :: InfEffs es => Type -> Eff es Type
normalise = uniVarsToForall {->=> skolemsToExists-} >=> go
  where
    go = \case
        T.UniVar uni ->
            lookupUniVar uni >>= \case
                Left _ -> typeError $ "dangling univar " <> pretty uni
                Right body -> go (unMono body)
        T.Forall var body -> T.Forall var <$> go body
        T.Exists var body -> T.Exists var <$> go body
        T.Function from to -> T.Function <$> go from <*> go to
        T.Application lhs rhs -> T.Application <$> go lhs <*> go rhs
        T.Variant row -> T.Variant <$> traverse go row
        T.Record row -> T.Record <$> traverse go row
        v@T.Var{} -> pure v
        name@T.Name{} -> pure name
        skolem@T.Skolem{} -> pure skolem -- typeError $ "skolem " <> pretty skolem <> " remains in code"

    -- this is an alternative to forallScope that's only suitable at the top level
    -- it also compresses any records found along the way, because I don't feel like
    -- making that a different pass, and `compress` uses `mono` under the hood, which
    -- means that it has to be run early
    uniVarsToForall ty = uncurry (foldr T.Forall) <$> runState HashMap.empty (uniGo ty)
    uniGo :: InfEffs es => Type -> Eff (State (HashMap UniVar Name) : es) Type
    uniGo = \case
        T.UniVar uni -> do
            gets @(HashMap UniVar Name) (HashMap.lookup uni) >>= \case
                Just var -> pure $ T.Var var
                Nothing ->
                    lookupUniVar uni >>= \case
                        Left _ -> do
                            tyVar <- freshTypeVar
                            modify $ HashMap.insert uni tyVar
                            pure $ T.Var tyVar
                        Right body -> uniGo $ unMono body
        T.Forall var body -> T.Forall var <$> uniGo body
        T.Exists var body -> T.Exists var <$> uniGo body
        T.Function from to -> T.Function <$> uniGo from <*> uniGo to
        T.Application lhs rhs -> T.Application <$> uniGo lhs <*> uniGo rhs
        T.Variant row -> T.Variant <$> (traverse uniGo =<< compress Variant row)
        T.Record row -> T.Record <$> (traverse uniGo =<< compress Record row)
        v@T.Var{} -> pure v
        name@T.Name{} -> pure name
        skolem@T.Skolem{} -> pure skolem

-- these two functions have the same problem as the old `forallScope` - they capture skolems from an outer scope
-- it's not clear whether anything should be done about them
-- the only problem I can see is a univar unifying with a type var from an inner scope, but I'm not sure how would that happen
--
-- it is still safe to use these at the top-level, however
skolemsToExists, skolemsToForall :: forall es. InfEffs es => Type -> Eff es Type
-- ∃a. a -> a <: b
-- ?a -> ?a <: b
-- b ~ ∃a. a -> a
skolemsToExists = replaceSkolems T.Exists
-- b <: ∀a. a -> a
-- b <: ?a -> ?a
-- b ~ ∀a. a -> a
skolemsToForall = replaceSkolems T.Forall

replaceSkolems :: InfEffs es => (Name -> Type -> Type) -> Type -> Eff es Type
replaceSkolems con ty = uncurry (foldr con) <$> runState HashMap.empty (go ty)
  where
    go :: InfEffs es => Type -> Eff (State (HashMap Skolem Name) : es) Type
    go = \case
        T.Skolem skolem ->
            get @(HashMap Skolem Name) >>= \acc -> case HashMap.lookup skolem acc of
                Just tyVar -> pure $ T.Var tyVar
                Nothing -> do
                    tyVar <- freshTypeVar
                    modify $ HashMap.insert skolem tyVar
                    pure $ T.Var tyVar
        T.UniVar uni ->
            lookupUniVar uni >>= \case
                Left _ -> pure $ T.UniVar uni
                Right body -> do
                    body' <- go $ undefined body
                    overrideUniVar uni $ undefined body'
                    pure body'
        T.Forall var body -> T.Forall var <$> go body
        T.Exists var body -> T.Exists var <$> go body
        T.Function from to -> T.Function <$> go from <*> go to
        T.Application lhs rhs -> T.Application <$> go lhs <*> go rhs
        T.Record row -> T.Record <$> traverse go row
        T.Variant row -> T.Variant <$> traverse go row
        v@T.Var{} -> pure v
        name@T.Name{} -> pure name

-- what to match
data RecordOrVariant = Record | Variant deriving (Eq)
conOf :: RecordOrVariant -> ExtRow Type -> Type
conOf Record = T.Record
conOf Variant = T.Variant

-- lookup a field in a type, assuming that the type is a row type
-- if a univar is encountered, it's solved to a row type
--
-- I'm not sure how to handle polymorphism here yet, so I'll go
-- with Inv just in case
--
-- Note: repetitive calls of deepLookup on an open row turn it into a chain of singular extensions
-- you should probably call `compress` after that
deepLookup :: InfEffs es => RecordOrVariant -> Row.OpenName -> Type -> Eff es (Maybe Type)
deepLookup whatToMatch k = mono In >=> go >=> pure . fmap unMono -- todo: monoLayer instead of mono
  where
    go :: InfEffs es => Monotype -> Eff es (Maybe Monotype)
    go = \case
        MRecord nextRow
            | whatToMatch == Record -> deepLookup' nextRow
            | otherwise -> pure Nothing
        MVariant nextRow
            | whatToMatch == Variant -> deepLookup' nextRow
            | otherwise -> pure Nothing
        MUniVar uni ->
            lookupUniVar uni >>= \case
                Right ty -> go ty
                Left _ -> do
                    fieldType <- mono Inv =<< freshUniVar
                    rowVar <- mono Inv =<< freshUniVar
                    let con = case whatToMatch of
                            Variant -> MVariant
                            Record -> MRecord
                    solveUniVar uni $ con $ ExtRow (one (k, fieldType)) rowVar
                    pure $ Just fieldType

        -- once again, the cases are listed so that I don't forget to
        -- update them if I ever need to add a new Monotype constructor
        -- _ -> pure Nothing
        MSkolem{} -> pure Nothing
        MName{} -> pure Nothing
        MApp{} -> pure Nothing
        MFn{} -> pure Nothing
        MVar{} -> pure Nothing

    deepLookup' :: InfEffs es => ExtRow Monotype -> Eff es (Maybe Monotype)
    deepLookup' extRow = case Row.lookup k extRow.row of
        Just v -> pure $ Just v
        Nothing -> case Row.extension extRow of
            Nothing -> pure Nothing
            Just ext -> go ext

{- | compresses known row extensions of a row

@{ x : Int | y : Double | z : Char | r } -> { x : Int, y : Double, z : Char | r }@
-}
compress :: InfEffs es => RecordOrVariant -> ExtRow Type -> Eff es (ExtRow Type)
compress _ row@NoExtRow{} = pure row
compress whatToMatch r@(ExtRow row ext) = go ext
  where
    go =
        mono In >=> \case
            MRecord nextRow
                | whatToMatch == Record -> Row.extend row <$> go (T.Record $ unMono <$> nextRow)
                | otherwise -> pure r
            MVariant nextRow
                | whatToMatch == Variant -> Row.extend row <$> go (T.Variant $ unMono <$> nextRow)
                | otherwise -> pure r
            MUniVar uni ->
                lookupUniVar uni >>= \case
                    Right ty -> go $ unMono ty
                    Left _ -> pure r
            -- once again, the cases are listed so that I don't forget to
            -- update them if I ever need to add a new Monotype constructor
            -- _ -> pure r
            MSkolem{} -> pure r
            MName{} -> pure r
            MApp{} -> pure r
            MFn{} -> pure r
            MVar{} -> pure r

-- first record minus fields that match with the second one
diff :: InfEffs es => RecordOrVariant -> ExtRow Type -> Row Type -> Eff es (ExtRow Type)
diff whatToMatch lhsUncompressed rhs = do
    lhs <- compress whatToMatch lhsUncompressed
    pure $ lhs{row = Row.diff lhs.row rhs}

-- finds all type parameters used in a type and creates corresponding forall clauses
-- doesn't work with type vars (univars?), because the intended use case is pre-processing user-supplied types
inferTypeVars :: Type -> Type
inferTypeVars = uncurry (foldr T.Forall) . second snd . runPureEff . runState (HashSet.empty, HashSet.empty) . go
  where
    go :: Type -> Eff '[State (HashSet Name, HashSet Name)] Type
    go = \case
        T.Var var -> do
            isNew <- not . HashSet.member var <$> gets @(HashSet Name, HashSet Name) snd
            when isNew $ modify @(HashSet Name, HashSet Name) (second $ HashSet.insert var)
            pure $ T.Var var
        T.Forall var body -> modify @(HashSet Name, HashSet Name) (first $ HashSet.insert var) >> T.Forall var <$> go body
        T.Exists var body -> modify @(HashSet Name, HashSet Name) (first $ HashSet.insert var) >> T.Exists var <$> go body
        T.Function from to -> T.Function <$> go from <*> go to
        T.Application lhs rhs -> T.Application <$> go lhs <*> go rhs
        T.Variant row -> T.Variant <$> traverse go row
        T.Record row -> T.Record <$> traverse go row
        uni@T.UniVar{} -> pure uni
        skolem@T.Skolem{} -> pure skolem
        name@T.Name{} -> pure name

-- | check / infer types of a list of declarations that may reference each other
inferDecls :: InfEffs es => [Declaration Name] -> Eff es (HashMap Name Type)
inferDecls decls = do
    traverse_ updateTopLevel decls
    let (values, sigs) = second HashMap.fromList $ foldr getValueDecls ([], []) decls
    foldr (<>) HashMap.empty <$> for values \(binding, locals) ->
        (=<<) (`HashMap.lookup` sigs) (listToMaybe $ collectNamesInBinding binding) & \case
            Just ty -> do
                checkBinding binding ty
                pure $
                    HashMap.mapMaybe (`HashMap.lookup` sigs) $
                        HashMap.fromList $
                            (\x -> (x, x)) <$> collectNamesInBinding binding
            Nothing -> scoped do
                declareAll =<< inferDecls locals
                typeMap <- inferBinding binding
                typeMap <$ declareTopLevel typeMap
  where
    updateTopLevel = \case
        D.Signature name sig ->
            modify \s -> s{topLevel = HashMap.insert name (Right $ inferTypeVars sig) s.topLevel}
        D.Value binding@(E.FunctionBinding name _ _) locals -> insertBinding name binding locals
        D.Value binding@(E.ValueBinding (P.Var name) _) locals -> insertBinding name binding locals
        D.Value E.ValueBinding{} _ -> pass -- todo
        D.Type name vars constrs ->
            for_ (mkConstrSigs name vars constrs) \(con, sig) ->
                modify \s -> s{topLevel = HashMap.insert con (Right sig) s.topLevel}
        D.Alias{} -> pass

    insertBinding name binding locals =
        let closure = UninferredType $ forallScope $ scoped do
                declareAll =<< inferDecls locals
                nameTypePairs <- inferBinding binding
                declareTopLevel nameTypePairs
                case HashMap.lookup name nameTypePairs of
                    -- this can only happen if `inferBinding` returns an incorrect map of types
                    Nothing -> typeError $ "Internal error: type closure for" <+> pretty name <+> "didn't infer its type"
                    Just ty -> pure ty
         in modify \s ->
                s{topLevel = HashMap.insertWith (\_ x -> x) name (Left closure) s.topLevel}

    getValueDecls decl (values, sigs) = case decl of
        D.Value binding locals -> ((binding, locals) : values, sigs)
        D.Signature name sig -> (values, (name, sig) : sigs)
        D.Type name vars constrs -> (values, mkConstrSigs name vars constrs ++ sigs)
        D.Alias{} -> (values, sigs)

    mkConstrSigs :: Name -> [Name] -> [(Name, [Type])] -> [(Name, Type)]
    mkConstrSigs name vars constrs =
        second (\conParams -> foldr T.Forall (foldr T.Function (T.Name name) conParams) vars)
            <$> constrs

-- | unifies two monotypes by instantiating free vars
unify :: InfEffs es => Monotype -> Monotype -> Eff es ()
unify lhs rhs = subtype (unMono lhs) (unMono rhs)

subtype :: InfEffs es => Type -> Type -> Eff es ()
subtype lhs_ rhs_ = join $ match <$> monoLayer In lhs_ <*> monoLayer Out rhs_
  where
    match = \cases
        lhs rhs | lhs == rhs -> pass -- simple cases, i.e. two type constructors, two univars or two exvars
        lhs (MLUniVar uni) -> solveOr (mono In $ unMonoLayer lhs) (subtype (unMonoLayer lhs) . unMono) uni
        (MLUniVar uni) rhs -> solveOr (mono Out $ unMonoLayer rhs) ((`subtype` unMonoLayer rhs) . unMono) uni
        (MLName lhs) (MLName rhs) ->
            unlessM (elem (lhs, rhs) <$> asks @(Builtins Name) (.subtypeRelations)) $
                typeError ("cannot unify" <+> pretty lhs <+> "with" <+> pretty rhs)
        (MLFn inl outl) (MLFn inr outr) -> do
            subtype inr inl
            subtype outl outr
        (MLApp lhs rhs) (MLApp lhs' rhs') -> do
            -- note that we assume the same variance for all type parameters
            -- some kind of kind system is needed to track variance and prevent stuff like `Maybe a b`
            -- higher-kinded types are also problematic when it comes to variance, i.e.
            -- is `f a` a subtype of `f b` when a is `a` subtype of `b` or the other way around?
            --
            -- QuickLook just assumes that all constructors are invariant and -> is a special case
            subtype lhs lhs'
            subtype rhs rhs'
        (MLVariant lhs) (MLVariant rhs) -> rowCase Variant lhs rhs
        (MLRecord lhs) (MLRecord rhs) -> rowCase Record lhs rhs
        lhs rhs -> typeError $ pretty lhs <+> "is not a subtype of" <+> pretty rhs

    rowCase whatToMatch lhsRow rhsRow = do
        let con = conOf whatToMatch
        for_ (IsList.toList lhsRow.row) \(name, lhsTy) ->
            deepLookup whatToMatch name (con rhsRow) >>= \case
                Nothing ->
                    typeError $
                        pretty (con lhsRow)
                            <+> "is not a subtype of"
                            <+> pretty (con rhsRow)
                            <> ": right hand side does not contain"
                            <+> pretty name
                Just rhsTy -> subtype lhsTy rhsTy
        -- if the lhs has an extension, it should be compatible with rhs without the already matched fields
        for_ (Row.extension lhsRow) \ext -> subtype ext . con =<< diff whatToMatch rhsRow lhsRow.row

    -- turns out it's different enough from `withUniVar`
    solveOr :: InfEffs es => Eff es Monotype -> (Monotype -> Eff es ()) -> UniVar -> Eff es ()
    solveOr solveWith whenSolved uni = lookupUniVar uni >>= either (const $ solveUniVar uni =<< solveWith) whenSolved

check :: InfEffs es => Expr -> Type -> Eff es ()
check e type_ = scoped $ match e type_
  where
    match = \cases
        -- the cases for E.Name and E.Constructor are redundant, since
        -- `infer` just looks up their types anyway
        (E.Lambda arg body) (T.Function from to) -> scoped do
            -- `checkPattern` updates signatures of all mentioned variables
            checkPattern arg from
            check body to
        (E.Annotation expr annTy) ty -> do
            check expr annTy
            subtype annTy ty
        (E.If cond true false) ty -> do
            check cond $ T.Name BoolName
            check true ty
            check false ty
        (E.Case arg matches) ty -> do
            argTy <- infer arg
            for_ matches \(pat, body) -> do
                checkPattern pat argTy
                check body ty
        (E.List items) (T.Application (T.Name ListName) itemTy) -> for_ items (`check` itemTy)
        (E.Record row) ty -> do
            for_ (IsList.toList row) \(name, expr) ->
                deepLookup Record name ty >>= \case
                    Nothing -> typeError $ pretty ty <+> "does not contain field" <+> pretty name
                    Just fieldTy -> check expr fieldTy
        expr (T.UniVar uni) ->
            lookupUniVar uni >>= \case
                Right ty -> check expr $ unMono ty
                Left _ -> do
                    newTy <- mono In =<< infer expr
                    lookupUniVar uni >>= \case
                        Left _ -> solveUniVar uni newTy
                        Right _ -> pass
        expr (T.Forall var body) -> check expr =<< substitute Out var body
        expr (T.Exists var body) -> check expr =<< substitute In var body
        expr ty -> do
            inferredTy <- infer expr
            subtype inferredTy ty

checkBinding :: InfEffs es => Binding Name -> Type -> Eff es ()
checkBinding binding ty = case binding of
    E.FunctionBinding _ args body -> check (foldr E.Lambda body args) ty
    E.ValueBinding pat body -> checkPattern pat ty >> check body ty

checkPattern :: InfEffs es => Pattern' -> Type -> Eff es ()
checkPattern = \cases
    -- we need this case, since inferPattern only infers monotypes for var patterns
    (P.Var name) ty -> updateSig name ty
    -- we probably do need a case for P.Constructor for the same reason
    (P.Variant name arg) ty ->
        deepLookup Variant name ty >>= \case
            Nothing -> typeError $ pretty ty <+> "does not contain variant" <+> pretty name
            Just argTy -> checkPattern arg argTy
    (P.Record patRow) ty -> do
        for_ (IsList.toList patRow) \(name, pat) ->
            deepLookup Record name ty >>= \case
                Nothing -> typeError $ pretty ty <+> "does not contain field" <+> pretty name
                Just fieldTy -> checkPattern pat fieldTy
    pat ty -> do
        inferredTy <- inferPattern pat
        subtype inferredTy ty

infer :: InfEffs es => Expr -> Eff es Type
infer =
    scoped . \case
        E.Name name -> lookupSig name
        E.Constructor name -> lookupSig name
        E.Variant name -> {-forallScope-} do
            var <- freshUniVar
            rowVar <- freshUniVar
            -- #a -> [Name #a | #r]
            pure $ T.Function var (T.Variant $ ExtRow (fromList [(name, var)]) rowVar)
        E.Application f x -> do
            fTy <- infer f
            inferApp fTy x
        E.Lambda arg body -> {-forallScope-} do
            argTy <- inferPattern arg
            T.Function argTy <$> infer body
        E.Let binding body -> do
            declareAll =<< inferBinding binding
            infer body
        E.Annotation expr ty -> ty <$ check expr ty
        E.If cond true false -> do
            check cond $ T.Name BoolName
            result <- unMono <$> (mono In =<< infer true)
            check false result
            pure result
        E.Case arg matches -> do
            argTy <- infer arg
            result <- freshUniVar
            for_ matches \(pat, body) -> do
                checkPattern pat argTy
                check body result
            pure result
        E.Match [] -> typeError "empty match expression"
        E.Match ((firstPats, firstBody) : ms) -> {-forallScope-} do
            bodyType <- infer firstBody
            patTypes <- traverse inferPattern firstPats
            for_ ms \(pats, body) -> do
                traverse_ (`checkPattern` bodyType) pats
                check body bodyType
            unless (all ((== length patTypes) . length . fst) ms) $
                typeError "different amount of arguments in a match statement"
            pure $ foldr T.Function bodyType patTypes
        E.List items -> do
            itemTy <- freshUniVar
            traverse_ (`check` itemTy) items
            pure $ T.Application (T.Name ListName) itemTy
        E.Record row -> T.Record . NoExtRow <$> traverse infer row
        E.RecordLens fields -> do
            recordParts <- for fields \field -> do
                rowVar <- freshUniVar
                pure \nested -> T.Record $ ExtRow (one (field, nested)) rowVar
            let mkNestedRecord = foldr1 (.) recordParts
            a <- freshUniVar
            b <- freshUniVar
            pure $
                T.Name LensName
                    `T.Application` mkNestedRecord a
                    `T.Application` mkNestedRecord b
                    `T.Application` a
                    `T.Application` b
        E.IntLiteral num
            | num >= 0 -> pure $ T.Name NatName
            | otherwise -> pure $ T.Name IntName
        E.TextLiteral _ -> pure $ T.Name TextName
        E.CharLiteral _ -> pure $ T.Name TextName

-- infers the type of a function / variables in a pattern
-- does not implicitly declare anything
inferBinding :: InfEffs es => Binding Name -> Eff es (HashMap Name Type)
inferBinding = \case
    E.ValueBinding pat body -> scoped do
        bodyTy <- infer body
        checkPattern pat bodyTy
        traverse lookupSig (HashMap.fromList $ (\x -> (x, x)) <$> collectNames pat)
    E.FunctionBinding name args body -> do
        argTypes <- traverse inferPattern args
        bodyTy <- infer body
        let ty = foldr T.Function bodyTy argTypes
        pure $ HashMap.singleton name ty

-- \| collects all to-be-declared names in a pattern
collectNames :: Pattern a -> [a]
collectNames = \case
    P.Var name -> [name]
    P.Annotation pat _ -> collectNames pat
    P.Variant _ pat -> collectNames pat
    P.Constructor _ pats -> foldMap collectNames pats
    P.List pats -> foldMap collectNames pats
    P.Record row -> foldMap collectNames $ toList row
    -- once again, exhaustiveness checking is worth writing some boilerplate
    P.IntLiteral{} -> []
    P.TextLiteral{} -> []
    P.CharLiteral{} -> []

collectNamesInBinding :: Binding a -> [a]
collectNamesInBinding = \case
    E.FunctionBinding name _ _ -> [name]
    E.ValueBinding pat _ -> collectNames pat

inferPattern :: InfEffs es => Pattern' -> Eff es Type
inferPattern = \case
    P.Var name -> do
        uni <- freshUniVar
        updateSig name uni
        pure uni
    P.Annotation pat ty -> ty <$ checkPattern pat ty
    p@(P.Constructor name args) -> do
        (resultType, argTypes) <- conArgTypes name
        unless (length argTypes == length args) $ typeError $ "incorrect arg count in pattern" <+> pretty p
        zipWithM_ checkPattern args argTypes
        pure resultType
    P.List pats -> do
        result <- freshUniVar
        traverse_ (`checkPattern` result) pats
        pure $ T.Application (T.Name ListName) result
    P.Variant name arg -> {-forallScope-} do
        argTy <- inferPattern arg
        T.Variant . ExtRow (fromList [(name, argTy)]) <$> freshUniVar
    P.Record row -> do
        typeRow <- traverse inferPattern row
        T.Record . ExtRow typeRow <$> freshUniVar
    P.IntLiteral num
        | num >= 0 -> pure $ T.Name NatName
        | otherwise -> pure $ T.Name IntName
    P.TextLiteral _ -> pure $ T.Name TextName
    P.CharLiteral _ -> pure $ T.Name TextName
  where
    -- conArgTypes and the zipM may be unified into a single function
    conArgTypes = lookupSig >=> go
    go =
        monoLayer In >=> \case
            MLFn arg rest -> second (arg :) <$> go rest
            -- univars should never appear as the rightmost argument of a value constructor type
            -- i.e. types of value constructors have the shape `a -> b -> c -> d -> ConcreteType a b c d`
            --
            -- solved univars cannot appear here either, since `lookupSig` on a pattern returns a type with no univars
            MLUniVar uni -> typeError $ "unexpected univar" <+> pretty uni <+> "in a constructor type"
            -- this kind of repetition is necessary to retain missing pattern warnings
            MLName name -> pure (T.Name name, [])
            MLApp lhs rhs -> pure (T.Application lhs rhs, [])
            MLVariant row -> pure (T.Variant row, [])
            MLRecord row -> pure (T.Record row, [])
            MLSkolem skolem -> pure (T.Skolem skolem, [])
            MLVar var -> pure (T.Var var, [])

inferApp :: InfEffs es => Type -> Expr -> Eff es Type
inferApp fTy arg =
    monoLayer In fTy >>= \case
        MLUniVar v -> do
            from <- mono In =<< infer arg
            lookupUniVar v >>= \case
                Left _ -> do
                    to <- mono Inv =<< freshUniVar
                    solveUniVar v $ MFn from to
                    pure $ unMono to
                Right newTy -> do
                    to <- mono Inv =<< freshUniVar
                    unify newTy (MFn from to)
                    pure $ unMono to
        MLFn from to -> to <$ check arg from
        _ -> typeError $ pretty fTy <+> "is not a function type"
