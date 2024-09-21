{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE NoFieldSelectors #-}

module TypeChecker.Backend where

import CheckerTypes
import Control.Monad (foldM)
import Data.HashMap.Strict qualified as HashMap
import Data.HashSet qualified as HashSet
import Effectful
import Effectful.Error.Static (Error, runErrorNoCallStack, throwError)
import Effectful.Reader.Static (Reader, asks, runReader)
import Effectful.State.Static.Local (State, get, gets, modify, runState)
import NameGen
import Prettyprinter (Doc, Pretty, pretty, (<+>))
import Relude hiding (Reader, State, Type, ask, asks, bool, get, gets, modify, put, runReader, runState)
import Syntax
import Syntax.Row
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

instance Pretty Monotype where
    pretty = pretty . unMono

instance Pretty MonoLayer where
    pretty = pretty . unMonoLayer

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
    pure $ Name (one letter) id'
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
    case (HashMap.lookup name topLevel, HashMap.lookup name locals) of
        (Just (Right ty), _) -> pure ty
        (_, Just ty) -> pure ty
        (Just (Left (UninferredType closure)), _) -> closure
        (Nothing, Nothing) -> do
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