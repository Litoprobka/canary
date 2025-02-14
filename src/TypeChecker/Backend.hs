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
import Diagnostic (Diagnose, fatal, internalError)
import Effectful
import Effectful.Dispatch.Dynamic (interpret, reinterpret)
import Effectful.Error.Static (runErrorNoCallStack, throwError)
import Effectful.State.Static.Local (State, get, gets, modify, runState)
import Effectful.TH
import Error.Diagnose (Report (..))
import Error.Diagnose qualified as M (Marker (..))
import LensyUniplate hiding (cast)
import NameGen
import Prettyprinter (Pretty, pretty, (<+>))
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
import Syntax.Term (plainBinder)
import Syntax.Term qualified as T
import Prelude (show)

type Pat = Pattern 'Fixity
type TypeDT = Type 'DuringTypecheck

data Monotype
    = MName Name
    | MSkolem Skolem
    | MUniVar Loc UniVar
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
    | -- | MLVar Name
      MLApp TypeDT TypeDT
    | MLFn Loc TypeDT TypeDT
    | MLVariant Loc (ExtRow TypeDT)
    | MLRecord Loc (ExtRow TypeDT)
    deriving (Show, Eq)

instance HasLoc MonoLayer where
    getLoc = \case
        MLName name -> getLoc name
        MLSkolem skolem -> getLoc skolem
        MLUniVar loc _ -> loc
        -- MLVar name -> getLoc name
        MLApp lhs rhs -> zipLocOf lhs rhs
        MLFn loc _ _ -> loc
        MLVariant loc _ -> loc
        MLRecord loc _ -> loc

-- calling an uninferred type closure should introduce all of the inferred bindings
-- into the global scope
newtype UninferredType = UninferredType (forall es. InfEffs es => Eff es (Type 'Fixity))
instance Show UninferredType where
    show _ = "<closure>"

type TopLevelBindings = HashMap Name (Either UninferredType (Type 'Fixity))

data InfState = InfState
    { nextUniVarId :: Int
    , nextTypeVar :: Char
    , currentScope :: Scope
    , topLevel :: TopLevelBindings
    -- ^ top level bindings that may or may not have a type signature
    , locals :: HashMap Name TypeDT -- local variables
    , vars :: HashMap UniVar (Either Scope Monotype) -- contains either the scope of an unsolved var or a type
    , skolems :: HashMap Skolem Scope -- skolem scopes
    }
    deriving (Show)

data TypeError
    = CannotUnify Name Name
    | NotASubtype TypeDT TypeDT (Maybe OpenName)
    | MissingField TypeDT OpenName
    | MissingVariant TypeDT OpenName
    | EmptyMatch Loc -- empty match expression
    | ArgCountMismatch Loc -- "different amount of arguments in a match statement"
    | ArgCountMismatchPattern Pat Int Int
    | NotAFunction Loc TypeDT -- pretty fTy <+> "is not a function type"
    | SelfReferential Loc UniVar TypeDT
    | NoVisibleTypeArgument (Expr 'Fixity) (Type 'Fixity) TypeDT

typeError :: Diagnose :> es => TypeError -> Eff es a
typeError =
    fatal . one . \case
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
        SelfReferential loc var ty ->
            Err
                Nothing
                ("self-referential type" <+> pretty var <+> "~" <+> pretty ty)
                (mkNotes [(loc, M.This "arising from"), (getLoc ty, M.Where "and from")])
                []
        NoVisibleTypeArgument expr tyArg ty ->
            Err
                Nothing
                "no visible type argument"
                ( mkNotes
                    [ (getLoc expr, M.This "when applying this expression")
                    , (getLoc tyArg, M.This "to this type")
                    , (getLoc ty, M.Where $ "where the expression has type" <+> pretty ty)
                    ]
                )
                []

type InfEffs es = (NameGen :> es, State InfState :> es, Diagnose :> es)

data Declare :: Effect where
    UpdateSig :: Name -> TypeDT -> Declare m ()

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
    -> Eff (Declare : State InfState : es) a
    -> Eff es a
run env = fmap fst . runWithFinalEnv env

runWithFinalEnv
    :: TopLevelBindings
    -> Eff (Declare : State InfState : es) a
    -> Eff es (a, InfState)
runWithFinalEnv env = do
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
        . runDeclare

freshUniVar :: InfEffs es => Loc -> Eff es TypeDT
freshUniVar loc = T.UniVar loc <$> freshUniVar'

freshUniVar' :: InfEffs es => Eff es UniVar
freshUniVar' = do
    -- and this is where I wish I had lens
    var <- UniVar <$> gets @InfState (.nextUniVarId) <* modify @InfState \s -> s{nextUniVarId = succ s.nextUniVarId}
    scope <- gets @InfState (.currentScope)
    modify \s -> s{vars = HashMap.insert var (Left scope) s.vars}
    pure var

freshSkolem :: InfEffs es => Name -> Eff es TypeDT
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
lookupUniVar uni = maybe (internalError Blank $ "missing univar" <+> pretty uni) pure . HashMap.lookup uni =<< gets @InfState (.vars)

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
                internalError Blank $ "Internal error (probably a bug): attempted to solve a solved univar " <> pretty uni
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
            Indirect -> do
                unwrappedTy <- unMono <$> unwrap ty
                typeError $ SelfReferential (getLoc $ unMono ty) uni unwrappedTy
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

    rescope scope = foldUniVars \v -> lookupUniVar v >>= either (rescopeVar v scope) (const pass)
    rescopeVar v scope oldScope = modify \s -> s{vars = HashMap.insert v (Left $ min oldScope scope) s.vars}

    unwrap = \case
        uni2@(MUniVar _ var) ->
            lookupUniVar var >>= \case
                Right refTy -> unwrap refTy
                Left{} -> pure uni2
        other -> pure other

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
    maybe (internalError (getLoc skolem) $ "missing skolem" <+> pretty skolem) pure
        . HashMap.lookup skolem
        =<< gets @InfState (.skolems)

-- looks up a type of a binding. Local binding take precedence over uninferred globals, but not over inferred ones
lookupSig :: (InfEffs es, Declare :> es) => Name -> Eff es TypeDT
lookupSig name = do
    InfState{topLevel, locals} <- get @InfState
    case (HashMap.lookup name topLevel, HashMap.lookup name locals) of
        (Just (Right ty), _) -> pure $ cast ty
        (_, Just ty) -> pure ty
        (Just (Left (UninferredType closure)), _) -> cast <$> closure
        (Nothing, Nothing) -> do
            -- assuming that type checking is performed after name resolution,
            -- all encountered names have to be in scope
            uni <- freshUniVar (getLoc name)
            uni <$ updateSig name uni

declareAll :: Declare :> es => HashMap Name TypeDT -> Eff es ()
declareAll = traverse_ (uncurry updateSig) . HashMap.toList

declareTopLevel :: InfEffs es => HashMap Name (Type 'Fixity) -> Eff es ()
declareTopLevel types = modify \s -> s{topLevel = fmap Right types <> s.topLevel}

generalise :: InfEffs es => Eff es TypeDT -> Eff es TypeDT
generalise = fmap runIdentity . generaliseAll . fmap Identity

-- TODO: this function should also handle the generalisation of skolems
generaliseAll :: (Traversable t, InfEffs es) => Eff es (t TypeDT) -> Eff es (t TypeDT)
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
        pure $ foldr (T.Forall (getLoc ty) . plainBinder) (foldr (T.Exists (getLoc ty) . plainBinder) ty' skolems) forallVars

    -- get all univars that have been solved to unique type variables
    getFreeVar :: HashMap k Name -> Either Name TypeDT -> Maybe Name
    getFreeVar skolems (Left name)
        | name `notElem` skolems = Just name
    getFreeVar _ _ = Nothing

    go
        :: InfEffs es => Scope -> TypeDT -> Eff (State (HashMap UniVar (Either Name TypeDT)) : State (HashMap Skolem Name) : es) TypeDT
    go scope = transformM' T.uniplate \case
        T.UniVar loc uni -> fmap Left do
            whenNothingM (fmap toTypeVar <$> gets @(HashMap UniVar (Either Name TypeDT)) (HashMap.lookup uni)) do
                lookupUniVar uni >>= \case
                    -- don't generalise outer-scoped vars
                    Left varScope | varScope <= scope -> pure $ T.UniVar loc uni
                    innerScoped -> do
                        newTy <- bitraverse (const $ freshTypeVar loc) (go scope . unMono) innerScoped
                        modify @(HashMap UniVar (Either Name TypeDT)) $ HashMap.insert uni newTy
                        pure $ toTypeVar newTy
        T.Skolem skolem -> fmap Left do
            whenNothingM (gets @(HashMap Skolem Name) (fmap T.Name . HashMap.lookup skolem)) do
                skScope <- skolemScope skolem
                if skScope > scope
                    then do
                        var <- freshTypeVar (getLoc skolem)
                        modify @(HashMap Skolem Name) $ HashMap.insert skolem var
                        pure $ T.Name var
                    else pure $ T.Skolem skolem
        other -> pure $ Right other
    toTypeVar = either T.Name id

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
mono :: InfEffs es => Variance -> TypeDT -> Eff es Monotype
mono variance = \case
    -- T.Var var -> internalError (getLoc var) $ "mono: dangling var" <+> pretty var -- pure $ MVar var
    T.Name name -> pure $ MName name
    T.Skolem skolem -> pure $ MSkolem skolem
    T.UniVar loc uni -> pure $ MUniVar loc uni
    T.Application lhs rhs -> MApp <$> go lhs <*> go rhs
    T.Function loc from to -> MFn loc <$> mono (flipVariance variance) from <*> go to
    T.VariantT loc row -> MVariant loc <$> traverse go row
    T.RecordT loc row -> MRecord loc <$> traverse go row
    T.Forall _ binder body -> go =<< substitute variance binder.var body
    T.Exists _ binder body -> go =<< substitute (flipVariance variance) binder.var body
    other -> internalError (getLoc other) "type-level expressions are not supported yet"
  where
    go = mono variance

flipVariance :: Variance -> Variance
flipVariance = \case
    In -> Out
    Out -> In
    Inv -> Inv

unMono :: Monotype -> TypeDT
unMono = \case
    MName name -> T.Name name
    MSkolem skolem -> T.Skolem skolem
    MUniVar loc uniVar -> T.UniVar loc uniVar
    MApp lhs rhs -> T.Application (unMono lhs) (unMono rhs)
    MFn loc from to -> T.Function loc (unMono from) (unMono to)
    MVariant loc row -> T.VariantT loc $ fmap unMono row
    MRecord loc row -> T.RecordT loc $ fmap unMono row

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
monoLayer :: InfEffs es => Variance -> TypeDT -> Eff es MonoLayer
monoLayer variance = \case
    -- T.Var var -> internalError (getLoc var) $ "monoLayer: dangling var" <+> pretty var -- pure $ MLVar var
    T.Name name -> pure $ MLName name
    T.Skolem skolem -> pure $ MLSkolem skolem
    T.UniVar loc uni -> pure $ MLUniVar loc uni
    T.Application lhs rhs -> pure $ MLApp lhs rhs
    T.Function loc from to -> pure $ MLFn loc from to
    T.VariantT loc row -> pure $ MLVariant loc row
    T.RecordT loc row -> pure $ MLRecord loc row
    T.Forall _ binder body -> monoLayer variance =<< substitute variance binder.var body
    T.Exists _ binder body -> monoLayer variance =<< substitute (flipVariance variance) binder.var body
    other -> internalError (getLoc other) "type-level expressions are not supported yet"

unMonoLayer :: MonoLayer -> TypeDT
unMonoLayer = \case
    MLName name -> T.Name name
    MLSkolem skolem -> T.Skolem skolem
    MLUniVar loc uni -> T.UniVar loc uni
    MLApp lhs rhs -> T.Application lhs rhs
    MLFn loc lhs rhs -> T.Function loc lhs rhs
    MLVariant loc row -> T.VariantT loc row
    MLRecord loc row -> T.RecordT loc row

substitute :: InfEffs es => Variance -> Name -> TypeDT -> Eff es TypeDT
substitute variance var ty = (.result) <$> substitute' variance var ty

data Subst = Subst {var :: TypeDT, result :: TypeDT}

-- substitute a type vairable with a univar / skolem depedening on variance
substitute' :: InfEffs es => Variance -> Name -> TypeDT -> Eff es Subst
substitute' variance var ty = do
    someVar <- freshSomething Blank var variance
    result <- go someVar ty
    pure Subst{var = someVar, result}
  where
    go replacement = transformM' T.uniplate \case
        T.Name v | v == var -> pure $ Left replacement
        T.Name name -> pure $ Left $ T.Name name
        T.UniVar loc uni ->
            Left
                <$> ( T.UniVar loc uni
                        <$ withUniVar uni \body -> overrideUniVar uni =<< mono In =<< go replacement (unMono body)
                    )
        T.Forall loc binder body
            | binder.var /= var -> Left . T.Forall loc binder <$> go replacement body
            | otherwise -> pure $ Left $ T.Forall loc binder body
        T.Exists loc binder body
            | binder.var /= var -> Left . T.Exists loc binder <$> go replacement body
            | otherwise -> pure $ Left $ T.Exists loc binder body
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
conOf :: RecordOrVariant -> Loc -> ExtRow TypeDT -> TypeDT
conOf Record = T.RecordT
conOf Variant = T.VariantT

-- lookup a field in a type, assuming that the type is a row type
-- if a univar is encountered, it's solved to a row type
--
-- I'm not sure how to handle polymorphism here yet, so I'll go
-- with Inv just in case
--
-- Note: repetitive calls of deepLookup on an open row turn it into a chain of singular extensions
-- you should probably call `compress` after that
deepLookup :: InfEffs es => RecordOrVariant -> Row.OpenName -> TypeDT -> Eff es (Maybe TypeDT)
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

    deepLookup' :: InfEffs es => ExtRow Monotype -> Eff es (Maybe Monotype)
    deepLookup' extRow = case Row.lookup k extRow.row of
        Just v -> pure $ Just v
        Nothing -> case Row.extension extRow of
            Nothing -> pure Nothing
            Just ext -> go ext

{- | compresses known row extensions of a row

@{ x : Int | y : Double | z : Char | r } -> { x : Int, y : Double, z : Char | r }@
-}
compress :: InfEffs es => RecordOrVariant -> ExtRow TypeDT -> Eff es (ExtRow TypeDT)
compress _ row@NoExtRow{} = pure row
compress whatToMatch r@(ExtRow row ext) = go ext
  where
    go =
        mono In >=> \case
            MRecord loc nextRow
                | whatToMatch == Record -> Row.extend row <$> go (T.RecordT loc $ unMono <$> nextRow)
                | otherwise -> pure r
            MVariant loc nextRow
                | whatToMatch == Variant -> Row.extend row <$> go (T.VariantT loc $ unMono <$> nextRow)
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

-- first record minus fields that match with the second one
diff :: InfEffs es => RecordOrVariant -> ExtRow TypeDT -> Row TypeDT -> Eff es (ExtRow TypeDT)
diff whatToMatch lhsUncompressed rhs = do
    lhs <- compress whatToMatch lhsUncompressed
    pure $ lhs{row = Row.diff lhs.row rhs}
