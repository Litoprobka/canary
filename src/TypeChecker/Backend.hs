{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE NoFieldSelectors #-}
{-# OPTIONS_GHC -Wno-missing-export-lists #-}

module TypeChecker.Backend where

import Common
import Data.HashMap.Strict qualified as HashMap
import Data.HashSet qualified as HashSet
import Data.List (nub)
import Diagnostic (Diagnose, fatal)
import Effectful
import Effectful.Dispatch.Dynamic (interpret, reinterpret)
import Effectful.Error.Static (runErrorNoCallStack, throwError)
import Effectful.Reader.Static (Reader, asks, runReader)
import Effectful.State.Static.Local (State, get, gets, modify, runState)
import Effectful.TH
import Error.Diagnose (Report (..))
import Error.Diagnose qualified as M (Marker (..))
import LensyUniplate
import NameGen
import Prettyprinter (Doc, Pretty, pretty, (<+>))
import Prettyprinter.Render.Terminal (AnsiStyle)
import Relude hiding (
    Reader,
    State,
    Type,
    ask,
    asks,
    bool,
    break,
    cycle,
    evalState,
    get,
    gets,
    modify,
    put,
    runReader,
    runState,
 )
import Syntax
import Syntax.Row
import Syntax.Row qualified as Row
import Syntax.Type qualified as T
import Prelude (show)

type Expr = Expression 'Fixity
type Pat = Pattern 'Fixity

type Type = Type' 'DuringTypecheck

data Monotype
    = MName Name
    | MSkolem Skolem
    | MUniVar Loc UniVar
    | MVar Name -- a (probably out of scope) type var
    | MApp Monotype Monotype
    | MFn Loc Monotype Monotype
    | MVariant Loc (ExtRow Monotype)
    | MRecord Loc (ExtRow Monotype)
    deriving (Show, Eq)

uniplateMono :: Traversal' Monotype Monotype
uniplateMono f = \case
    MApp lhs rhs -> MApp <$> f lhs <*> f rhs
    MFn loc lhs rhs -> MFn loc <$> f lhs <*> f rhs
    MVariant loc row -> MVariant loc <$> traverse f row
    MRecord loc row -> MRecord loc <$> traverse f row
    term -> pure term

-- а type whose outer constructor is monomorphic
data MonoLayer
    = MLName Name
    | MLSkolem Skolem
    | MLUniVar Loc UniVar
    | MLVar Name
    | MLApp Type Type
    | MLFn Loc Type Type
    | MLVariant Loc (ExtRow Type)
    | MLRecord Loc (ExtRow Type)
    deriving (Show, Eq)

instance HasLoc MonoLayer where
    getLoc = \case
        MLName name -> getLoc name
        MLSkolem skolem -> getLoc skolem
        MLUniVar loc _ -> loc
        MLVar name -> getLoc name
        MLApp lhs rhs -> zipLocOf lhs rhs
        MLFn loc _ _ -> loc
        MLVariant loc _ -> loc
        MLRecord loc _ -> loc

newtype Builtins a = Builtins
    { subtypeRelations :: [(a, a)]
    }
    deriving (Show, Functor, Foldable, Traversable)

-- calling an uninferred type closure should introduce all of the inferred bindings
-- into the global scope
newtype UninferredType = UninferredType (forall es. InfEffs es => Eff es (Type' 'Fixity))
instance Show UninferredType where
    show _ = "<closure>"

type TopLevelBindings = HashMap Name (Either UninferredType (Type' 'Fixity))

data InfState = InfState
    { nextUniVarId :: Int
    , nextTypeVar :: Char
    , currentScope :: Scope
    , topLevel :: TopLevelBindings
    -- ^ top level bindings that may or may not have a type signature
    , locals :: HashMap Name Type -- local variables
    , vars :: HashMap UniVar (Either Scope Monotype) -- contains either the scope of an unsolved var or a type
    , skolems :: HashMap Skolem Scope -- skolem scopes
    }
    deriving (Show)

data TypeError
    = Internal Loc (Doc AnsiStyle)
    | CannotUnify Name Name
    | NotASubtype Type Type (Maybe OpenName)
    | MissingField Type OpenName
    | MissingVariant Type OpenName
    | EmptyMatch Loc -- empty match expression
    | ArgCountMismatch Loc -- "different amount of arguments in a match statement"
    | ArgCountMismatchPattern Pat Int Int
    | NotAFunction Loc Type -- pretty fTy <+> "is not a function type"
    | SelfReferential Type

typeError :: Diagnose :> es => TypeError -> Eff es a
typeError =
    fatal . one . \case
        Internal loc doc ->
            Err
                Nothing
                ("Internal error:" <+> doc)
                (mkNotes [(loc, M.This "arising from")])
                []
        CannotUnify lhs rhs ->
            Err
                Nothing
                ("cannot unify" <+> pretty lhs <+> "with" <+> pretty rhs)
                (mkNotes [(getLoc lhs, M.This $ pretty lhs <+> "originates from"), (getLoc rhs, M.This $ pretty rhs <+> "originates from")])
                []
        NotASubtype lhs rhs mbField ->
            Err
                Nothing
                (pretty lhs <+> "is not a subtype of" <+> pretty rhs <> fieldMsg)
                (mkNotes [(getLoc lhs, M.This "lhs"), (getLoc rhs, M.This "rhs")])
                []
          where
            fieldMsg = case mbField of
                Nothing -> ""
                Just field -> ": right hand side does not contain" <+> pretty field
        MissingField ty field ->
            Err
                Nothing
                (pretty ty <+> "does not contain field" <+> pretty field)
                (mkNotes [(getLoc ty, M.This "type arising from"), (getLoc field, M.This "field arising from")])
                []
        MissingVariant ty variant ->
            Err
                Nothing
                (pretty ty <+> "does not contain variant" <+> pretty variant)
                (mkNotes [(getLoc ty, M.This "type arising from"), (getLoc variant, M.This "variant arising from")])
                []
        EmptyMatch loc ->
            Err
                Nothing
                "empty match expression"
                (mkNotes [(loc, M.This "")])
                []
        ArgCountMismatch loc ->
            Err
                Nothing
                "different amount of arguments in a match statement"
                (mkNotes [(loc, M.This "")])
                []
        ArgCountMismatchPattern pat expected got ->
            Err
                Nothing
                ("incorrect arg count (" <> pretty got <> ") in pattern" <+> pretty pat <> ". Expected" <+> pretty expected)
                (mkNotes [(getLoc pat, M.This "")])
                []
        NotAFunction loc ty ->
            Err
                Nothing
                (pretty ty <+> "is not a function type")
                (mkNotes [(loc, M.This "arising from function application")])
                []
        SelfReferential ty ->
            Err
                Nothing
                ("self-referential type" <+> pretty ty)
                (mkNotes [(getLoc ty, M.This "arising from")])
                []

type InfEffs es = (NameGen :> es, State InfState :> es, Diagnose :> es, Reader (Builtins Name) :> es)

data Declare :: Effect where
    UpdateSig :: Name -> Type -> Declare m ()

makeEffect ''Declare

-- | run the given action and discard signature updates
scoped :: InfEffs es => Eff (Declare : es) a -> Eff es a
scoped action =
    runDeclare action & \action' -> do
        locals <- gets @InfState (.locals)
        action' <* modify (\s -> s{locals})

-- | interpret `updateSig` as an update of InfState
runDeclare :: State InfState :> es => Eff (Declare : es) a -> Eff es a
runDeclare = interpret \_ (UpdateSig name ty) -> modify \s -> s{locals = HashMap.insert name ty s.locals}

data Break err :: Effect where
    Break :: err -> Break err m a

makeEffect ''Break

runBreak :: forall err a es. Eff (Break err : es) a -> Eff es (Either err a)
runBreak = reinterpret (runErrorNoCallStack @err) \_ (Break val) -> throwError @err val

instance Pretty Monotype where
    pretty = pretty . unMono

instance Pretty MonoLayer where
    pretty = pretty . unMonoLayer

run
    :: TopLevelBindings
    -> Builtins Name
    -> Eff (Declare : Reader (Builtins Name) : State InfState : es) a
    -> Eff es a
run env builtins = fmap fst . runWithFinalEnv env builtins

runWithFinalEnv
    :: TopLevelBindings
    -> Builtins Name
    -> Eff (Declare : Reader (Builtins Name) : State InfState : es) a
    -> Eff es (a, InfState)
runWithFinalEnv env builtins = do
    runState
        InfState
            { nextUniVarId = 0
            , nextTypeVar = 'a'
            , currentScope = Scope 0
            , topLevel = env
            , locals = HashMap.empty
            , vars = HashMap.empty
            , skolems = HashMap.empty
            }
        . runReader builtins
        . runDeclare

freshUniVar :: InfEffs es => Loc -> Eff es Type
freshUniVar loc = T.UniVar loc <$> freshUniVar'

freshUniVar' :: InfEffs es => Eff es UniVar
freshUniVar' = do
    -- and this is where I wish I had lens
    var <- UniVar <$> gets @InfState (.nextUniVarId) <* modify @InfState \s -> s{nextUniVarId = succ s.nextUniVarId}
    scope <- gets @InfState (.currentScope)
    modify \s -> s{vars = HashMap.insert var (Left scope) s.vars}
    pure var

freshSkolem :: InfEffs es => Name -> Eff es Type
freshSkolem name = do
    skolem <- Skolem <$> mkName name
    scope <- gets @InfState (.currentScope)
    modify \s -> s{skolems = HashMap.insert skolem scope s.skolems}
    pure $ T.Skolem skolem
  where
    mkName (Located loc (Name txtName _)) = Located loc <$> freshName_ (Name' txtName)
    mkName _ = freshName (Located Blank $ Name' "what") -- why?

freshTypeVar :: Loc -> InfEffs es => Eff es Name
freshTypeVar loc = do
    id' <- freshId
    letter <- gets @InfState (.nextTypeVar) <* modify \s -> s{nextTypeVar = cycleChar s.nextTypeVar}
    pure $ Located loc $ Name (one letter) id'
  where
    cycleChar 'z' = 'a'
    cycleChar c = succ c

lookupUniVar :: InfEffs es => UniVar -> Eff es (Either Scope Monotype)
lookupUniVar uni = maybe (typeError $ Internal Blank $ "missing univar" <+> pretty uni) pure . HashMap.lookup uni =<< gets @InfState (.vars)

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

alterUniVar :: InfEffs es => Bool -> UniVar -> Monotype -> Eff es ()
alterUniVar override uni ty = do
    -- here comes the magic. If the new type contains other univars, we change their scope
    lookupUniVar uni >>= \case
        Right _
            | not override ->
                typeError $ Internal Blank $ "Internal error (probably a bug): attempted to solve a solved univar " <> pretty uni
        Right _ -> pass
        Left scope -> rescope scope ty
    cycle <- cycleCheck (Direct, HashSet.singleton uni) ty
    when (cycle == NoCycle) $ modify \s -> s{vars = HashMap.insert uni (Right ty) s.vars}
  where
    -- errors out on indirect cycles (i.e. a ~ Maybe a)
    -- returns False on direct univar cycles (i.e. a ~ b, b ~ c, c ~ a)
    -- returns True when there are no cycles
    cycleCheck (selfRefType, acc) = \case
        MUniVar _ uni2 | HashSet.member uni2 acc -> case selfRefType of
            Direct -> pure DirectCycle
            Indirect -> typeError $ SelfReferential (unMono ty)
        MUniVar _ uni2 ->
            lookupUniVar uni2 >>= \case
                Left _ -> pure NoCycle
                Right ty' -> cycleCheck (selfRefType, HashSet.insert uni2 acc) ty'
        MFn _ from to -> cycleCheck (Indirect, acc) from >> cycleCheck (Indirect, acc) to
        MApp lhs rhs -> cycleCheck (Indirect, acc) lhs >> cycleCheck (Indirect, acc) rhs
        MVariant _ row -> NoCycle <$ traverse_ (cycleCheck (Indirect, acc)) row
        MRecord _ row -> NoCycle <$ traverse_ (cycleCheck (Indirect, acc)) row
        MName{} -> pure NoCycle
        MSkolem{} -> pure NoCycle
        MVar{} -> pure NoCycle

    rescope scope = foldUniVars \v -> lookupUniVar v >>= either (rescopeVar v scope) (const pass)
    rescopeVar v scope oldScope = modify \s -> s{vars = HashMap.insert v (Left $ min oldScope scope) s.vars}

foldUniVars :: InfEffs es => (UniVar -> Eff es ()) -> Monotype -> Eff es ()
foldUniVars action =
    void . transformM uniplateMono \case
        var@(MUniVar _ v) -> do
            action v
            lookupUniVar v >>= either (const pass) (foldUniVars action)
            pure var
        other -> pure other

skolemScope :: InfEffs es => Skolem -> Eff es Scope
skolemScope skolem =
    maybe (typeError $ Internal (getLoc skolem) $ "missing skolem" <+> pretty skolem) pure
        . HashMap.lookup skolem
        =<< gets @InfState (.skolems)

-- looks up a type of a binding. Local binding take precedence over uninferred globals, but not over inferred ones
lookupSig :: (InfEffs es, Declare :> es) => Name -> Eff es Type
lookupSig name = do
    InfState{topLevel, locals} <- get @InfState
    case (HashMap.lookup name topLevel, HashMap.lookup name locals) of
        (Just (Right ty), _) -> pure $ cast (T.uniplate' id T.UniVar T.Skolem) ty
        (_, Just ty) -> pure ty
        (Just (Left (UninferredType closure)), _) -> cast (T.uniplate' id T.UniVar T.Skolem) <$> closure
        (Nothing, Nothing) -> do
            -- assuming that type checking is performed after name resolution,
            -- all encountered names have to be in scope
            uni <- freshUniVar (getLoc name)
            uni <$ updateSig name uni

declareAll :: Declare :> es => HashMap Name Type -> Eff es ()
declareAll = traverse_ (uncurry updateSig) . HashMap.toList

declareTopLevel :: InfEffs es => HashMap Name (Type' 'Fixity) -> Eff es ()
declareTopLevel types = modify \s -> s{topLevel = fmap Right types <> s.topLevel}

builtin :: Reader (Builtins Name) :> es => (Builtins Name -> a) -> Eff es a
builtin = asks @(Builtins Name)

generalise :: InfEffs es => Eff es Type -> Eff es Type
generalise = fmap runIdentity . generaliseAll . fmap Identity

-- TODO: this function should also handle the generalisation of skolems
generaliseAll :: (Traversable t, InfEffs es) => Eff es (t Type) -> Eff es (t Type)
generaliseAll action = do
    modify \s@InfState{currentScope = Scope n} -> s{currentScope = Scope $ succ n}
    types <- action
    modify \s@InfState{currentScope = Scope n} -> s{currentScope = Scope $ pred n}
    outerScope <- gets @InfState (.currentScope)
    traverse (generaliseOne outerScope) types
  where
    generaliseOne scope ty = do
        ((ty', vars), skolems) <- runState HashMap.empty $ runState HashMap.empty $ go scope ty
        let forallVars = nub . mapMaybe (getFreeVar skolems) $ toList vars
        pure $ foldr (T.Forall (getLoc ty)) (foldr (T.Exists (getLoc ty)) ty' skolems) forallVars

    -- get all univars that have been solved to unique type variables
    getFreeVar :: HashMap k Name -> Type -> Maybe Name
    getFreeVar skolems (T.Var name)
        | name `notElem` skolems = Just name
    getFreeVar _ _ = Nothing

    go :: InfEffs es => Scope -> Type -> Eff (State (HashMap UniVar Type) : State (HashMap Skolem Name) : es) Type
    go scope = transformM' T.uniplate \case
        T.UniVar loc uni -> fmap Left do
            whenNothingM (gets @(HashMap UniVar Type) (HashMap.lookup uni)) do
                lookupUniVar uni >>= \case
                    -- don't generalise outer-scoped vars
                    Left varScope | varScope <= scope -> pure $ T.UniVar loc uni
                    innerScoped -> do
                        newTy <- either (const $ T.Var <$> freshTypeVar loc) (go scope . unMono) innerScoped
                        modify @(HashMap UniVar Type) $ HashMap.insert uni newTy
                        pure newTy
        T.Skolem skolem -> fmap Left do
            whenNothingM (gets @(HashMap Skolem Name) (fmap T.Var . HashMap.lookup skolem)) do
                skScope <- skolemScope skolem
                if skScope > scope
                    then do
                        var <- freshTypeVar (getLoc skolem)
                        modify @(HashMap Skolem Name) $ HashMap.insert skolem var
                        pure $ T.Var var
                    else pure $ T.Skolem skolem
        other -> pure $ Right other

-- perform an action at top level
-- at the moment this function doesn't work as intended
topLevelScope :: InfEffs es => Eff es a -> Eff es a
topLevelScope action = do
    InfState{currentScope} <- get
    modify @InfState \s -> s{currentScope = Scope 0}
    out <- action
    modify @InfState \s -> s{currentScope}
    pure out

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
    T.Var var -> typeError $ Internal (getLoc var) $ "mono: dangling var" <+> pretty var -- pure $ MVar var
    T.Name name -> pure $ MName name
    T.Skolem skolem -> pure $ MSkolem skolem
    T.UniVar loc uni -> pure $ MUniVar loc uni
    T.Application lhs rhs -> MApp <$> go lhs <*> go rhs
    T.Function loc from to -> MFn loc <$> mono (flipVariance variance) from <*> go to
    T.Variant loc row -> MVariant loc <$> traverse go row
    T.Record loc row -> MRecord loc <$> traverse go row
    T.Forall _ var body -> go =<< substitute variance var body
    T.Exists _ var body -> go =<< substitute (flipVariance variance) var body
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
    MUniVar loc uniVar -> T.UniVar loc uniVar
    MVar var -> T.Var var
    MApp lhs rhs -> T.Application (unMono lhs) (unMono rhs)
    MFn loc from to -> T.Function loc (unMono from) (unMono to)
    MVariant loc row -> T.Variant loc $ fmap unMono row
    MRecord loc row -> T.Record loc $ fmap unMono row

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
    T.Var var -> typeError $ Internal (getLoc var) $ "monoLayer: dangling var" <+> pretty var -- pure $ MLVar var
    T.Name name -> pure $ MLName name
    T.Skolem skolem -> pure $ MLSkolem skolem
    T.UniVar loc uni -> pure $ MLUniVar loc uni
    T.Application lhs rhs -> pure $ MLApp lhs rhs
    T.Function loc from to -> pure $ MLFn loc from to
    T.Variant loc row -> pure $ MLVariant loc row
    T.Record loc row -> pure $ MLRecord loc row
    T.Forall _ var body -> monoLayer variance =<< substitute variance var body
    T.Exists _ var body -> monoLayer variance =<< substitute (flipVariance variance) var body

unMonoLayer :: MonoLayer -> Type
unMonoLayer = \case
    MLName name -> T.Name name
    MLSkolem skolem -> T.Skolem skolem
    MLUniVar loc uni -> T.UniVar loc uni
    MLVar name -> T.Var name
    MLApp lhs rhs -> T.Application lhs rhs
    MLFn loc lhs rhs -> T.Function loc lhs rhs
    MLVariant loc row -> T.Variant loc row
    MLRecord loc row -> T.Record loc row

substitute :: InfEffs es => Variance -> Name -> Type -> Eff es Type
substitute variance var ty = do
    someVar <- freshSomething Blank var variance
    go someVar ty
  where
    go replacement = transformM' T.uniplate \case
        T.Var v | v == var -> pure $ Left replacement
        T.Var name -> pure $ Left $ T.Var name
        T.UniVar loc uni ->
            Left
                <$> ( T.UniVar loc uni
                        <$ withUniVar uni \body -> overrideUniVar uni =<< mono In =<< go replacement (unMono body)
                    )
        T.Forall loc v body
            | v /= var -> Left . T.Forall loc v <$> go replacement body
            | otherwise -> pure $ Left $ T.Forall loc v body
        T.Exists loc v body
            | v /= var -> Left . T.Exists loc v <$> go replacement body
            | otherwise -> pure $ Left $ T.Exists loc v body
        other -> pure $ Right other

    -- freshUniVar or freshSkolem, depending on variance
    -- should it be the other way around?
    --
    -- out: forall a. Int -> a
    -- in: forall a. a -> Int
    freshSomething loc name = \case
        In -> freshUniVar loc
        Out -> freshSkolem name
        Inv -> freshSkolem name

-- what to match
data RecordOrVariant = Record | Variant deriving (Eq)
conOf :: RecordOrVariant -> Loc -> ExtRow Type -> Type
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
        MRecord _ nextRow
            | whatToMatch == Record -> deepLookup' nextRow
            | otherwise -> pure Nothing
        MVariant _ nextRow
            | whatToMatch == Variant -> deepLookup' nextRow
            | otherwise -> pure Nothing
        MUniVar loc uni ->
            lookupUniVar uni >>= \case
                Right ty -> go ty
                Left _ -> do
                    fieldType <- MUniVar loc <$> freshUniVar'
                    rowVar <- MUniVar loc <$> freshUniVar'
                    let con = case whatToMatch of
                            Variant -> MVariant
                            Record -> MRecord
                    solveUniVar uni $ con loc $ ExtRow (one (k, fieldType)) rowVar
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
            MRecord loc nextRow
                | whatToMatch == Record -> Row.extend row <$> go (T.Record loc $ unMono <$> nextRow)
                | otherwise -> pure r
            MVariant loc nextRow
                | whatToMatch == Variant -> Row.extend row <$> go (T.Variant loc $ unMono <$> nextRow)
                | otherwise -> pure r
            MUniVar _ uni ->
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
