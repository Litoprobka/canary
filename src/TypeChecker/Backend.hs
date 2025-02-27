{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE NoFieldSelectors #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# OPTIONS_GHC -Wno-missing-export-lists #-}

module TypeChecker.Backend where

import Common
import Data.HashMap.Strict qualified as HashMap
import Data.HashSet qualified as HashSet
import Data.Traversable (for)
import Diagnostic (Diagnose, fatal, internalError)
import Effectful
import Effectful.Dispatch.Dynamic (interpret, reinterpret)
import Effectful.Error.Static (runErrorNoCallStack, throwError)
import Effectful.State.Static.Local (State, get, gets, modify, runState)
import Effectful.TH
import Error.Diagnose (Report (..))
import Error.Diagnose qualified as M (Marker (..))
import Interpreter (Value, ValueEnv)
import Interpreter qualified as V
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
import Syntax.Core qualified as C
import Syntax.Row
import Syntax.Row qualified as Row
import Syntax.Term (Quantifier(..), Visibility (..), Erased (..))

type Pat = Pattern 'Fixity
type TypeDT = Value
type Type' = Value

data Monotype
    = MCon Name [Monotype]
    | MTyCon Name
    | MLambda MonoClosure
    | MRecord (Row Monotype)
    | MVariant OpenName Monotype
    | MPrim Literal
    | -- types
      MFn Loc Monotype Monotype
    | MQ Loc Quantifier Erased MonoClosure
    | MVariantT Loc (ExtRow Monotype)
    | MRecordT Loc (ExtRow Monotype)
    | -- stuck computations
      MApp Monotype ~Monotype
    | MCase Monotype [(CorePattern, Monotype)]
    | -- typechecking metavars
      MUniVar Loc UniVar
    | MSkolem Skolem

data MonoClosure = MonoClosure {var :: Name, ty :: Monotype, env :: HashMap Name Value, body :: Monotype}

uniplateMono :: Traversal' Monotype Monotype
uniplateMono f = \case
    MCon name args -> MCon name <$> traverse f args
    MLambda _closure -> error "todo: uniplate monolambda" -- MLambda name \x -> f (body x)
    MApp lhs rhs -> MApp <$> f lhs <*> f rhs
    MFn loc lhs rhs -> MFn loc <$> f lhs <*> f rhs
    MVariantT loc row -> MVariantT loc <$> traverse f row
    MRecordT loc row -> MRecordT loc <$> traverse f row
    MRecord row -> MRecord <$> traverse f row
    MVariant name arg -> MVariant name <$> f arg
    MCase arg matches -> MCase <$> f arg <*> (traverse . traverse) f matches
    term -> pure term

-- а type whose outer constructor is monomorphic
data MonoLayer
    = MLCon Name [Value]
    | MLTyCon Name
    | MLLambda V.Closure
    | MLRecord (Row Value)
    | MLVariant OpenName Value
    | MLPrim Literal
    | MLPrimFunc Name (Value -> Value)
    | -- types
      MLFn Loc TypeDT TypeDT
    | MLQ Loc Quantifier Erased V.Closure
    | MLVariantT Loc (ExtRow TypeDT)
    | MLRecordT Loc (ExtRow TypeDT)
    | -- stuck computations
      MLApp Value ~Value
    | MLCase Value [(CorePattern, Value)]
    | -- typechecking metavars
      MLUniVar Loc UniVar
    | MLSkolem Skolem

instance HasLoc MonoLayer where
    getLoc = \case
        MLCon name _ -> getLoc name
        MLTyCon name -> getLoc name
        MLLambda closure -> getLoc closure.var -- fixme
        MLRecord _ -> Blank --
        MLVariant{} -> Blank --
        MLPrim val -> getLoc val
        MLPrimFunc name _ -> getLoc name -- to fix?
        MLFn loc _ _ -> loc
        MLQ loc _ _ _ -> loc
        MLVariantT loc _ -> loc
        MLRecordT loc _ -> loc
        MLApp{} -> Blank
        MLCase{} -> Blank
        MLUniVar loc _ -> loc
        MLSkolem skolem -> getLoc skolem

data InfState = InfState
    { nextUniVarId :: Int
    , nextTypeVar :: Char
    , currentScope :: Scope
    , -- the types of top-level bindings should not contain metavars
      -- this is not enforced at type level, though
      topLevel :: HashMap Name Type'
    -- ^ top level bindings that may or may not have a type signature
    , locals :: HashMap Name TypeDT -- local variables
    , vars :: HashMap UniVar (Either Scope Monotype) -- contains either the scope of an unsolved var or a type
    , skolems :: HashMap Skolem Scope -- skolem scopes
    }

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

type InfEffs es = (NameGen :> es, State InfState :> es, Diagnose :> es, State ValueEnv :> es)

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
    :: HashMap Name Type'
    -> Eff (Declare : State InfState : es) a
    -> Eff es a
run env = fmap fst . runWithFinalEnv env

runWithFinalEnv
    :: HashMap Name Type'
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
freshUniVar loc = V.UniVar loc <$> freshUniVar'

freshUniVar' :: InfEffs es => Eff es UniVar
freshUniVar' = do
    -- and this is where I wish I had lens
    var <- UniVar <$> gets @InfState (.nextUniVarId) <* modify @InfState \s -> s{nextUniVarId = succ s.nextUniVarId}
    scope <- gets @InfState (.currentScope)
    modify \s -> s{vars = HashMap.insert var (Left scope) s.vars}
    pure var

freshSkolem :: InfEffs es => SimpleName -> Eff es TypeDT
freshSkolem name = do
    skolem <- Skolem <$> mkName name
    scope <- gets @InfState (.currentScope)
    modify \s -> s{skolems = HashMap.insert skolem scope s.skolems}
    pure $ V.Skolem skolem
  where
    mkName (Located loc (Name' txtName)) = Located loc <$> freshName_ (Name' txtName)
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
    -- todo: we can infer equirecursive types (mu) when a cycle goes through a record / variant
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
        MQ loc _q _e _closure -> internalError loc "todo: cycleCheck MQ"
        MCon _ args -> NoCycle <$ traverse_ (cycleCheck (Indirect, acc)) args
        MApp lhs rhs -> cycleCheck (Indirect, acc) lhs >> cycleCheck (Indirect, acc) rhs
        MVariantT _ row -> NoCycle <$ traverse_ (cycleCheck (Indirect, acc)) row
        MRecordT _ row -> NoCycle <$ traverse_ (cycleCheck (Indirect, acc)) row
        MVariant _ val -> cycleCheck (Indirect, acc) val
        MRecord row -> NoCycle <$ traverse_ (cycleCheck (Indirect, acc)) row
        MLambda _f -> internalError Blank "todo: cycleCheck monolambda" -- NoCycle <$ cycleCheck (Indirect, acc) (f $ MPrim $ Located Blank $ TextLiteral "something")
        MCase arg matches -> cycleCheck (Indirect, acc) arg <* (traverse_ . traverse_) (cycleCheck (Indirect, acc)) matches
        MTyCon{} -> pure NoCycle
        MSkolem{} -> pure NoCycle
        MPrim{} -> pure NoCycle

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

-- looks up a type of a binding. Global bindings take precedence over local ones (should they?)
lookupSig :: (InfEffs es, Declare :> es) => Name -> Eff es TypeDT
lookupSig name = do
    InfState{topLevel, locals} <- get @InfState
    case (HashMap.lookup name topLevel, HashMap.lookup name locals) of
        (Just ty, _) -> pure ty
        (_, Just ty) -> pure ty
        (Nothing, Nothing) -> do
            -- assuming that type checking is performed after name resolution,
            -- we may just treat unbound names as holes
            uni <- freshUniVar (getLoc name)
            uni <$ updateSig name uni

declareAll :: Declare :> es => HashMap Name TypeDT -> Eff es ()
declareAll = traverse_ (uncurry updateSig) . HashMap.toList

declareTopLevel :: InfEffs es => HashMap Name Type' -> Eff es ()
declareTopLevel types = modify \s -> s{topLevel = types <> s.topLevel}

generalise :: InfEffs es => Eff es TypeDT -> Eff es TypeDT
generalise = fmap runIdentity . generaliseAll . fmap Identity

generaliseAll :: (Traversable t, InfEffs es) => Eff es (t TypeDT) -> Eff es (t TypeDT)
generaliseAll action = do
    modify \s@InfState{currentScope = Scope n} -> s{currentScope = Scope $ succ n}
    types <- action
    modify \s@InfState{currentScope = Scope n} -> s{currentScope = Scope $ pred n}
    outerScope <- gets @InfState (.currentScope)
    traverse (generaliseOne outerScope) types
  where
    generaliseOne scope ty = do
        (ty', vars) <- runState HashMap.empty $ go scope $ V.quote ty
        let forallVars = hashNub . lefts $ toList vars
        env <- get @ValueEnv
        pure $ V.evalCore env $ foldr (\var body -> C.Q (getLoc ty) Forall Implicit Erased var (type_ $ getLoc ty) body) ty' forallVars
    type_ loc = C.TyCon $ Located loc TypeName

    go
        :: InfEffs es => Scope -> CoreTerm -> Eff (State (HashMap UniVar (Either Name CoreTerm)) : es) CoreTerm
    go scope = \case
        C.UniVar loc uni -> do
            whenNothingM (fmap toTypeVar <$> gets @(HashMap UniVar (Either Name CoreTerm)) (HashMap.lookup uni)) do
                lookupUniVar uni >>= \case
                    -- don't generalise outer-scoped vars
                    Left varScope | varScope <= scope -> pure $ C.UniVar loc uni
                    innerScoped -> do
                        newTy <- bitraverse (const $ freshTypeVar loc) (go scope . V.quote . unMono) innerScoped
                        modify @(HashMap UniVar (Either Name CoreTerm)) $ HashMap.insert uni newTy
                        pure $ toTypeVar newTy
        C.Skolem skolem -> do
            skScope <- skolemScope skolem
            if skScope > scope
                then internalError (getLoc skolem) "the skolem\nhas escaped its scope\nyes\nYES\nthe skolem is out"
                else pure $ C.Skolem skolem
        -- simple recursive cases
        C.Function loc l r -> C.Function loc <$> go scope l <*> go scope r
        C.App lhs rhs -> C.App <$> go scope lhs <*> go scope rhs
        C.RecordT loc row -> C.RecordT loc <$> traverse (go scope) row
        C.VariantT loc row -> C.VariantT loc <$> traverse (go scope) row
        C.Record row -> C.Record <$> traverse (go scope) row
        C.Q loc q vis e var ty body -> C.Q loc q vis e var <$> go scope ty <*> go scope body
        C.Lambda var ty body -> C.Lambda var <$> go scope ty <*> go scope body
        C.Con name args -> C.Con name <$> traverse (go scope) args
        -- terminal cases
        C.Name name -> pure $ C.Name name
        C.TyCon name -> pure $ C.TyCon name
        C.Literal v -> pure $ C.Literal v
        C.Variant con -> pure $ C.Variant con
        C.Case arg matches -> C.Case arg <$> for matches \(pat, body) -> (pat,) <$> go scope body
        C.Let name _ _ -> internalError (getLoc name) "unexpected let in a quoted type"
    toTypeVar = either C.Name id

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
    V.Var var -> internalError (getLoc var) $ "mono: dangling var" <+> pretty var
    V.Con name args -> MCon name <$> traverse (mono variance) args
    V.TyCon name -> pure $ MTyCon name
    V.Skolem skolem -> pure $ MSkolem skolem
    V.UniVar loc uni -> pure $ MUniVar loc uni
    V.App lhs rhs -> MApp <$> go lhs <*> go rhs
    V.Function loc from to -> MFn loc <$> mono (flipVariance variance) from <*> go to
    V.VariantT loc row -> MVariantT loc <$> traverse go row
    V.RecordT loc row -> MRecordT loc <$> traverse go row
    V.Q loc q Visible e closure -> internalError loc "mono: monomorphise closures" -- pure $ MQ loc q e $ _toMonoClosure closure
    V.Q _ Forall vis _ closure -> go =<< substitute variance closure
    V.Q _ Exists vis _ closure -> go =<< substitute (flipVariance variance) closure
    V.PrimFunction{} -> internalError Blank "mono: prim function"
    V.PrimValue val -> pure $ MPrim val
    V.Record row -> MRecord <$> traverse (mono variance) row
    V.Variant name arg -> MVariant name <$> mono variance arg
    V.Case arg matches -> MCase <$> mono variance arg <*> traverse (bitraverse pure (mono variance)) matches
    l@V.Lambda{} -> internalError (getLoc l) "mono: type-level lambdas are not supported yet"
  where
    go = mono variance


flipVariance :: Variance -> Variance
flipVariance = \case
    In -> Out
    Out -> In
    Inv -> Inv

unMono :: Monotype -> TypeDT
unMono = \case
    MCon name args -> V.Con name (map unMono args)
    MTyCon name -> V.TyCon name
    MSkolem skolem -> V.Skolem skolem
    MUniVar loc uniVar -> V.UniVar loc uniVar
    MApp lhs rhs -> V.App (unMono lhs) (unMono rhs)
    MFn loc from to -> V.Function loc (unMono from) (unMono to)
    MVariantT loc row -> V.VariantT loc $ fmap unMono row
    MRecordT loc row -> V.RecordT loc $ fmap unMono row
    MVariant name val -> V.Variant name (unMono val)
    MRecord row -> V.Record (fmap unMono row)
    MLambda _closure -> error "todo: unMono MLambda; do lambdas even belong in Monotype?"
    MQ loc q e _closure -> V.Q loc q Visible e (error "todo: unMono Q")
    MPrim val -> V.PrimValue val
    MCase arg matches -> V.Case (unMono arg) ((map . second) unMono matches)

{- unwraps forall/exists clauses in a type until a monomorphic constructor is encountered

> monoLayer Out (forall a. a -> a)
> -- ?a -> ?a
> monoLayer In (forall a. a -> a)
> -- #a -> #a
> monoLayer Out (forall a. forall b. a -> b -> a)
> -- forall b. ?a -> b -> ?a -- wait, this is not quite right
> monoLayer Out (forall a. (forall b. b -> a) -> a)
> -- (forall b. b -> ?a) -> ?a
-}
monoLayer :: InfEffs es => Variance -> TypeDT -> Eff es MonoLayer
monoLayer variance = \case
    V.Var var -> internalError (getLoc var) $ "monoLayer: dangling var" <+> pretty var
    V.Con name args -> pure $ MLCon name args
    V.TyCon name -> pure $ MLTyCon name
    V.Skolem skolem -> pure $ MLSkolem skolem
    V.UniVar loc uni -> pure $ MLUniVar loc uni
    V.App lhs rhs -> pure $ MLApp lhs rhs
    V.Function loc from to -> pure $ MLFn loc from to
    V.VariantT loc row -> pure $ MLVariantT loc row
    V.RecordT loc row -> pure $ MLRecordT loc row
    V.Q loc q Visible e closure -> pure $ MLQ loc q e closure
    -- todo: I'm not sure how to handle erased vs retained vars yet
    -- in theory, no value may depend on an erased var
    V.Q _ Forall _ _e closure -> monoLayer variance =<< substitute variance closure
    V.Q _ Exists _ _e closure -> monoLayer variance =<< substitute (flipVariance variance) closure
    V.PrimFunction{} -> internalError Blank "monoLayer: prim function"
    V.Lambda closure -> pure $ MLLambda closure
    V.Record row -> pure $ MLRecord row
    V.Variant con arg -> pure $ MLVariant con arg
    V.PrimValue val -> pure $ MLPrim val
    V.Case arg matches -> pure $ MLCase arg matches

unMonoLayer :: MonoLayer -> TypeDT
unMonoLayer = \case
    MLCon name args -> V.Con name args
    MLTyCon name -> V.TyCon name
    MLLambda closure -> V.Lambda closure
    MLSkolem skolem -> V.Skolem skolem
    MLUniVar loc uni -> V.UniVar loc uni
    MLApp lhs rhs -> V.App lhs rhs
    MLFn loc lhs rhs -> V.Function loc lhs rhs
    MLQ loc q e closure -> V.Q loc q Visible e closure
    MLVariantT loc row -> V.VariantT loc row
    MLRecordT loc row -> V.RecordT loc row
    MLVariant name val -> V.Variant name val
    MLRecord row -> V.Record row
    MLPrim val -> V.PrimValue val
    MLPrimFunc name f -> V.PrimFunction name f
    MLCase arg matches -> V.Case arg matches

-- WARN: substitute doesn't traverse univars at the moment
substitute :: InfEffs es => Variance -> V.Closure -> Eff es TypeDT
substitute variance closure = (.result) <$> substitute' variance closure

data Subst = Subst {var :: TypeDT, result :: TypeDT}

-- substitute a type variable with a univar / skolem dependening on variance
substitute' :: InfEffs es => Variance -> V.Closure -> Eff es Subst
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
        In -> freshUniVar (getLoc closure.var)
        Out -> freshSkolem name
        Inv -> freshSkolem name

-- what to match
data RecordOrVariant = Record | Variant deriving (Eq)
conOf :: RecordOrVariant -> Loc -> ExtRow TypeDT -> TypeDT
conOf Record = V.RecordT
conOf Variant = V.VariantT

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
        MRecordT _ nextRow
            | whatToMatch == Record -> deepLookup' nextRow
            | otherwise -> pure Nothing
        MVariantT _ nextRow
            | whatToMatch == Variant -> deepLookup' nextRow
            | otherwise -> pure Nothing
        MUniVar loc uni ->
            lookupUniVar uni >>= \case
                Right ty -> go ty
                Left _ -> do
                    fieldType <- MUniVar loc <$> freshUniVar'
                    rowVar <- MUniVar loc <$> freshUniVar'
                    let con = case whatToMatch of
                            Variant -> MVariantT
                            Record -> MRecordT
                    solveUniVar uni $ con loc $ ExtRow (one (k, fieldType)) rowVar
                    pure $ Just fieldType

        -- there's no point in explicitly listing all of the cases, since
        -- deepLookup only looks at records, variants and univars
        _ -> pure Nothing

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
            MRecordT loc nextRow
                | whatToMatch == Record -> Row.extend row <$> go (V.RecordT loc $ unMono <$> nextRow)
                | otherwise -> pure r
            MVariantT loc nextRow
                | whatToMatch == Variant -> Row.extend row <$> go (V.VariantT loc $ unMono <$> nextRow)
                | otherwise -> pure r
            MUniVar _ uni ->
                lookupUniVar uni >>= \case
                    Right ty -> go $ unMono ty
                    Left _ -> pure r
            _ -> pure r

-- first record minus fields that match with the second one
diff :: InfEffs es => RecordOrVariant -> ExtRow TypeDT -> Row TypeDT -> Eff es (ExtRow TypeDT)
diff whatToMatch lhsUncompressed rhs = do
    lhs <- compress whatToMatch lhsUncompressed
    pure $ lhs{row = Row.diff lhs.row rhs}
