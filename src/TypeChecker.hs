{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedRecordDot #-}

module TypeChecker (run, runDefault, runWithFinalEnv, defaultEnv, inferIO, infer, inferPattern, check, checkPattern, inferTypeVars, normalise) where

import CheckerTypes
import Control.Monad (foldM)
import Data.Foldable1 (foldlM1)
import Data.HashMap.Strict qualified as HashMap
import Data.HashSet qualified as HashSet
import Data.List.NonEmpty qualified as NE
import Data.Text qualified as Text
import Data.Traversable (for)
import Prettyprinter (Doc, Pretty, line, pretty, (<+>))
import Prettyprinter.Render.Text (putDoc)
import Relude hiding (Type, bool)
import Syntax hiding (Name)
import Syntax.Expression qualified as E
import Syntax.Pattern qualified as P
import Syntax.Type qualified as T

type Expr = Expression Name
type Pattern' = Pattern Name

type Type = Type' Name

-- а type whose outer constructor is monomorphic
data MonoLayer
    = MName Name
    | MSkolem Skolem
    | MUniVar UniVar
    | MApp Type Type
    | MFn Type Type
    | MVariant (Row Type)
    | MRecord (Row Type)
    deriving (Show, Eq)

newtype TypeError = TypeError (Doc ()) deriving (Show)

data Builtins = Builtins
    { bool :: Name
    , list :: Name
    , int :: Name
    , text :: Name
    , char :: Name
    }
    deriving (Show)

data InfState = InfState
    { nextUniVarId :: Int
    , nextSkolemId :: Int
    , nextTypeVar :: Name
    , currentScope :: Scope
    , sigs :: HashMap Name Type -- known bindings and type constructors
    , vars :: HashMap UniVar (Either Scope Type) -- contains either the scope of an unsolved var or a type
    }
    deriving (Show)

type InfMonad = ExceptT TypeError (ReaderT Builtins (State InfState))

instance Pretty MonoLayer where
    pretty = pretty . unMono

-- helpers

runDefault :: InfMonad a -> Either TypeError a
runDefault = run defaultEnv

run :: HashMap Name Type -> InfMonad a -> Either TypeError a
run env = fst . runWithFinalEnv env

runWithFinalEnv :: HashMap Name Type -> InfMonad a -> (Either TypeError a, InfState)
runWithFinalEnv env =
    flip
        runState
        InfState
            { nextUniVarId = 0
            , nextSkolemId = 0
            , nextTypeVar = Name "a" 0
            , currentScope = Scope 0
            , sigs = env
            , vars = HashMap.empty
            }
        . flip runReaderT Builtins
            { bool = Name "Bool" 0
            , list = Name "List" 0
            , int = Name "Int" 0
            , text = Name "Text" 0
            , char = Name "Char" 0
            }
        . runExceptT

defaultEnv :: HashMap Name Type
defaultEnv =
    HashMap.fromList
        [ (Name "()" 0, T.Name $ Name "Unit" 0)
        , (Name "Nothing" 0, T.Forall a' $ T.Name (Name "Maybe" 0) `T.Application` a)
        , (Name "Just" 0, T.Forall a' $ a `T.Function` (T.Name (Name "Maybe" 0) `T.Application` a))
        , (Name "True" 0, T.Name $ Name "Bool" 0)
        , (Name "False" 0, T.Name $ Name "Bool" 0)
        , (Name "id" 0, T.Forall a' $ a `T.Function` a)
        , (Name "reverse" 0, T.Forall a' $ list a `T.Function` list a)
        ]
  where
    a' = Name "'a" 0
    a = T.Var a'
    list var = T.Name (Name "List" 0) `T.Application` var

inferIO :: Expr -> IO ()
inferIO = inferIO' defaultEnv

inferIO' :: HashMap Name Type -> Expr -> IO ()
inferIO' env expr = case run env $ fmap pretty . normalise =<< infer expr of
    Left (TypeError err) -> putDoc $ err <> line
    Right txt -> putDoc $ txt <> line

typeError :: Doc () -> InfMonad a
typeError err = ExceptT $ pure (Left $ TypeError err)

freshUniVar :: InfMonad UniVar
freshUniVar = do
    -- and this is where I wish I had lens
    var <- UniVar <$> gets (.nextUniVarId) <* modify \s -> s{nextUniVarId = succ s.nextUniVarId}
    scope <- gets (.currentScope)
    modify \s -> s{vars = HashMap.insert var (Left scope) s.vars}
    pure var

freshSkolem :: Name -> InfMonad Skolem
freshSkolem (Name name _) = Skolem . Name name <$> gets (.nextSkolemId) <* modify \s -> s{nextSkolemId = succ s.nextSkolemId}

freshTypeVar :: InfMonad Name
freshTypeVar = gets (.nextTypeVar) <* modify \s -> s{nextTypeVar = inc s.nextTypeVar}
  where
    inc (Name name n)
        | Text.head name < 'z' = Name (Text.singleton $ succ $ Text.head name) n
        | otherwise = Name "a" (succ n)

lookupUniVar :: UniVar -> InfMonad (Either Scope Type)
lookupUniVar uni = maybe (typeError $ "missing univar " <> pretty uni) pure . HashMap.lookup uni =<< gets (.vars)

withUniVar :: UniVar -> (Type -> InfMonad a) -> InfMonad ()
withUniVar uni f =
    lookupUniVar uni >>= \case
        Left _ -> pass
        Right ty -> void $ f ty

solveUniVar, overrideUniVar :: UniVar -> Type -> InfMonad ()
solveUniVar = alterUniVar False
overrideUniVar = alterUniVar True

data SelfRef = Direct | Indirect

alterUniVar :: Bool -> UniVar -> Type -> InfMonad ()
alterUniVar override uni ty = do
    -- here comes the magic. If the new type contains other univars, we change their scope
    lookupUniVar uni >>= \case
        Right _ | not override -> typeError $ "Internal error (probably a bug): attempted to solve a solved univar " <> pretty uni
        Right _ -> pass
        Left scope -> rescope scope ty
    modify \s -> s{vars = HashMap.insert uni (Right ty) s.vars}
    cycleCheck (Direct, HashSet.empty) ty
  where
    foldUniVars :: (UniVar -> InfMonad ()) -> Type -> InfMonad ()
    foldUniVars action = \case
        T.UniVar v -> action v >> lookupUniVar v >>= either (const pass) (foldUniVars action)
        T.Forall _ body -> foldUniVars action body
        T.Exists _ body -> foldUniVars action body
        T.Application lhs rhs -> foldUniVars action lhs >> foldUniVars action rhs
        T.Function from to -> foldUniVars action from >> foldUniVars action to
        T.Variant row -> traverse_ (foldUniVars action) row
        T.Record row -> traverse_ (foldUniVars action) row
        T.Var _ -> pass
        T.Name _ -> pass
        T.Skolem _ -> pass

    -- resolves direct univar cycles (i.e. a ~ b, b ~ c, c ~ a) to skolems
    -- errors out on indirect cycles (i.e. a ~ Maybe a)
    cycleCheck (selfRefType, acc) = \case
        T.UniVar uni2 | HashSet.member uni2 acc -> case selfRefType of
            Direct -> do
                skolem <- freshSkolem $ Name "q" 0
                modify \s -> s{vars = HashMap.insert uni2 (Right $ T.Skolem skolem) s.vars}
            Indirect -> typeError "self-referential type"
        T.UniVar uni2 -> withUniVar uni2 $ cycleCheck (selfRefType, HashSet.insert uni2 acc)
        T.Forall _ body -> cycleCheck (Indirect, acc) body
        T.Exists _ body -> cycleCheck (Indirect, acc) body
        T.Function from to -> cycleCheck (Indirect, acc) from >> cycleCheck (Indirect, acc) to
        T.Application lhs rhs -> cycleCheck (Indirect, acc) lhs >> cycleCheck (Indirect, acc) rhs
        T.Variant row -> traverse_ (cycleCheck (Indirect, acc)) row
        T.Record row -> traverse_ (cycleCheck (Indirect, acc)) row
        T.Var _ -> pass
        T.Name _ -> pass
        T.Skolem _ -> pass

    rescope scope = foldUniVars \v -> lookupUniVar v >>= either (rescopeVar v scope) (const pass)
    rescopeVar v scope oldScope = modify \s -> s{vars = HashMap.insert v (Left $ min oldScope scope) s.vars}

lookupSig :: Name -> InfMonad Type
lookupSig name = maybe (typeError "unbound name???") pure =<< gets (HashMap.lookup name . (.sigs))

updateSig :: Name -> Type -> InfMonad ()
updateSig name ty = modify \s -> s{sigs = HashMap.insert name ty s.sigs}

-- | run the given action and discard signature updates
scoped :: InfMonad a -> InfMonad a
scoped action = do
    sigs <- gets (.sigs)
    action <* modify \s -> s{sigs}

-- turns out it's tricky to get this function right.
-- just taking all of the new univars and turning them into type vars is not enough,
-- since a univar may be produced when specifying a univar from parent scope (i.e. `#a` to `#b -> #c`)
forallScope :: InfMonad Type -> InfMonad Type
forallScope action = do
    start <- gets (.nextUniVarId)
    modify \s@InfState{currentScope = Scope n} -> s{currentScope = Scope $ succ n}
    out <- action
    modify \s@InfState{currentScope = Scope n} -> s{currentScope = Scope $ pred n}
    end <- pred <$> gets (.nextUniVarId)
    outerScope <- gets (.currentScope)
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
                solveUniVar uni (T.Var tyVar)
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

{- | Unwraps a polytype until a simple constructor is encountered

> mono Out (forall a. a -> a)
> -- ?a -> ?a
> mono In (forall a. a -> a)
> -- #a -> #a
> mono Out (forall a. forall b. a -> b -> a)
> -- ?a -> ?b -> ?a
> mono Out (forall a. (forall b. b -> a) -> a)
> -- (forall b. b -> ?a) -> ?a
-}
mono :: Variance -> Type -> InfMonad MonoLayer
mono variance = \case
    v@T.Var{} -> typeError $ "unbound type variable " <> pretty v
    T.Name name -> pure $ MName name
    T.Skolem skolem -> pure $ MSkolem skolem
    T.UniVar uni -> pure $ MUniVar uni
    T.Application lhs rhs -> pure $ MApp lhs rhs
    T.Function from to -> pure $ MFn from to
    T.Variant row -> pure $ MVariant row
    T.Record row -> pure $ MRecord row
    T.Forall var body -> mono variance =<< substitute variance var body
    T.Exists var body -> mono variance =<< substitute (flipVariance variance) var body
  where
    flipVariance = \case
        In -> Out
        Out -> In
        Inv -> Inv

unMono :: MonoLayer -> Type
unMono = \case
    MName name -> T.Name name
    MSkolem skolem -> T.Skolem skolem
    MUniVar uniVar -> T.UniVar uniVar
    MApp lhs rhs -> T.Application lhs rhs
    MFn from to -> T.Function from to
    MVariant row -> T.Variant row
    MRecord row -> T.Record row

substitute :: Variance -> Name -> Type -> InfMonad Type
substitute variance var ty = do
    someVar <- freshSomething var variance
    go someVar ty
  where
    go replacement = \case
        T.Var v | v == var -> pure replacement
        T.Var name -> pure $ T.Var name
        T.UniVar uni -> T.UniVar uni <$ withUniVar uni (go replacement >=> overrideUniVar uni)
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
        In -> T.UniVar <$> freshUniVar
        Out -> T.Skolem <$> freshSkolem name
        Inv -> T.Skolem <$> freshSkolem name

-- `substituteTy` shouldn't be used for type vars, because it fails in cases like `forall a. (forall a. body)`
-- normally those are removed by name resolution, but they may still occur when checking, say `f (f x)`
substituteTy :: Type -> Type -> Type -> InfMonad Type
substituteTy from to = go
  where
    go = \case
        ty | ty == from -> pure to
        T.UniVar uni -> T.UniVar uni <$ withUniVar uni (go >=> overrideUniVar uni)
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
normalise :: Type -> InfMonad Type
normalise = uniVarsToForall >=> skolemsToExists >=> go
  where
    go = \case
        T.UniVar uni ->
            lookupUniVar uni >>= \case
                Left _ -> typeError $ "dangling univar " <> pretty uni
                Right body -> go body
        T.Forall var body -> T.Forall var <$> go body
        T.Exists var body -> T.Exists var <$> go body
        T.Function from to -> T.Function <$> go from <*> go to
        T.Application lhs rhs -> T.Application <$> go lhs <*> go rhs
        T.Variant row -> T.Variant <$> traverse go row
        T.Record row -> T.Record <$> traverse go row
        v@T.Var{} -> pure v
        name@T.Name{} -> pure name
        skolem@T.Skolem{} -> typeError $ "skolem " <> pretty skolem <> " remains in code"

    -- this is an alternative to forallScope that's only suitable at the top level
    uniVarsToForall ty = uncurry (foldr T.Forall) <$> uniGo HashSet.empty ty
    uniGo acc = \case
        T.UniVar uni ->
            lookupUniVar uni >>= \case
                Left _ -> do
                    tyVar <- freshTypeVar
                    solveUniVar uni (T.Var tyVar)
                    pure (T.Var tyVar, HashSet.insert tyVar acc)
                Right body -> first (const $ T.UniVar uni) <$> uniGo acc body
        T.Forall var body -> first (T.Forall var) <$> uniGo acc body
        T.Exists var body -> first (T.Exists var) <$> uniGo acc body
        T.Function from to -> do
            (from', acc') <- uniGo acc from
            (to', acc'') <- uniGo acc' to
            pure (T.Function from' to', acc'')
        T.Application lhs rhs -> do
            (lhs', acc') <- uniGo acc lhs
            (rhs', acc'') <- uniGo acc' rhs
            pure (T.Application lhs' rhs', acc'')
        T.Variant _ -> typeError "rows not supported yet"
        T.Record _ -> typeError "rows not supported yet"
        v@T.Var{} -> pure (v, acc)
        name@T.Name{} -> pure (name, acc)
        skolem@T.Skolem{} -> pure (skolem, acc)

-- these two functions have the same problem as the old `forallScope` - they capture skolems from an outer scope
-- it's not clear whether anything should be done about them
-- the only problem I can see is a univar unifying with a type var from an inner scope, but I'm not sure how would that happen
--
-- it is still safe to use these at the top-level, however
skolemsToExists, skolemsToForall :: Type -> InfMonad Type
(skolemsToExists, skolemsToForall) = (skolemsToExists', skolemsToForall')
  where
    -- ∃a. a -> a <: b
    -- ?a -> ?a <: b
    -- b ~ ∃a. a -> a
    skolemsToExists' ty = uncurry (foldr T.Exists) <$> go HashMap.empty ty
    -- b <: ∀a. a -> a
    -- b <: ?a -> ?a
    -- b ~ ∀a. a -> a
    skolemsToForall' ty = uncurry (foldr T.Forall) <$> go HashMap.empty ty

    go acc = \case
        T.Skolem skolem -> case HashMap.lookup skolem acc of
            Just tyVar -> pure (T.Var tyVar, acc)
            Nothing -> do
                tyVar <- freshTypeVar
                pure (T.Var tyVar, HashMap.insert skolem tyVar acc)
        T.UniVar uni ->
            lookupUniVar uni >>= \case
                Left _ -> pure (T.UniVar uni, acc)
                Right body -> do
                    (body', acc') <- go acc body
                    overrideUniVar uni body'
                    pure (body', acc')
        T.Forall var body -> first (T.Forall var) <$> go acc body
        T.Exists var body -> first (T.Exists var) <$> go acc body
        T.Function from to -> do
            (from', acc') <- go acc from
            (to', acc'') <- go acc' to
            pure (T.Function from' to', acc'')
        T.Application lhs rhs -> do
            (lhs', acc') <- go acc lhs
            (rhs', acc'') <- go acc' rhs
            pure (T.Application lhs' rhs', acc'')
        T.Record _ -> typeError "rows not yet supported"
        T.Variant _ -> typeError "rows not yet supported"
        v@T.Var{} -> pure (v, acc)
        name@T.Name{} -> pure (name, acc)

-- finds all type parameters used in a type and creates corresponding forall clauses
-- doesn't work with type vars (univars?), because the intended use case is pre-processing user-supplied types
inferTypeVars :: Type -> Type
inferTypeVars = uncurry (foldr T.Forall) . second snd . flip runState (HashSet.empty, HashSet.empty) . go
  where
    go = \case
        T.Var var -> do
            isNew <- not . HashSet.member var <$> gets snd
            when isNew $ modify' (second $ HashSet.insert var)
            pure $ T.Var var
        T.Forall var body -> modify' (first $ HashSet.insert var) >> T.Forall var <$> go body
        T.Exists var body -> modify' (first $ HashSet.insert var) >> T.Exists var <$> go body
        T.Function from to -> T.Function <$> go from <*> go to
        T.Application lhs rhs -> T.Application <$> go lhs <*> go rhs
        T.Variant row -> T.Variant <$> traverse go row
        T.Record row -> T.Record <$> traverse go row
        uni@T.UniVar{} -> pure uni
        skolem@T.Skolem{} -> pure skolem
        name@T.Name{} -> pure name

--

-- finds a "least common denominator" of two types, i.e.
-- @subtype a (supertype a b)@ and @subtype b (supertype a b)@
--
-- this is what you get when you try to preserve polytypes in univars
supertype :: Type -> Type -> InfMonad Type
supertype = \cases
    lhs rhs | lhs == rhs -> pure lhs
    lhs (T.UniVar uni) ->
        lookupUniVar uni >>= \case
            Left _ -> lhs <$ solveUniVar uni lhs
            Right rhs' -> supertype lhs rhs'
    lhs@T.UniVar{} rhs -> supertype rhs lhs
    -- and here comes the interesting part: we get back polymorphism by applying forallScope
    -- a similar function for existentials and skolems is TBD
    lhs rhs -> forallScope $ join $ match <$> mono In lhs <*> mono In rhs
  where
    match = \cases
        lhs rhs | lhs == rhs -> pure $ unMono lhs
        (MFn from to) (MFn from' to') -> T.Function <$> supertype from from' <*> supertype to to'
        (MApp lhs rhs) (MApp lhs' rhs') -> T.Application <$> supertype lhs lhs' <*> supertype rhs rhs'
        -- note that a fresh existential (i.e `exists a. a`) *is* a common supertype of any two types
        -- but using that would make type errors more confusing
        -- (i.e. instead of "Int is not a subtype of Char" we would suddenly get existentials everywhere)
        lhs rhs -> typeError $ "cannot unify" <+> pretty lhs <+> "and" <+> pretty rhs

-- | @subtype a b@ checks whether @a@ is a subtype of @b@
subtype :: Type -> Type -> InfMonad ()
subtype = \cases
    lhs rhs | lhs == rhs -> pass -- this case is a bit redundant, since we have to do the same after taking a mono layer anyway
    lhs (T.UniVar uni) -> solveOr lhs (subtype lhs) uni
    (T.UniVar uni) rhs -> solveOr rhs (`subtype` rhs) uni
    lhsTy rhsTy -> join $ match <$> mono In lhsTy <*> mono Out rhsTy
  where
    match = \cases
        lhs rhs | lhs == rhs -> pass -- simple cases, i.e. two type constructors, two univars or two exvars
        (MFn inl outl) (MFn inr outr) -> do
            subtype inr inl
            subtype outl outr
        (MApp lhs rhs) (MApp lhs' rhs') -> do
            -- note that we assume the same variance for all type parameters
            -- some kind of kind system is needed to track variance and prevent stuff like `Maybe a b`
            -- higher-kinded types are also problematic when it comes to variance, i.e.
            -- is `f a` a subtype of `g a`?
            --
            -- QuickLook just assumes that all constructors are invariant and -> is a special case
            subtype lhs lhs'
            subtype rhs rhs'
        lhs rhs -> typeError $ pretty lhs <> " is not a subtype of " <> pretty rhs

    -- turns out it's different enough from `withUniVar`
    solveOr :: Type -> (Type -> InfMonad ()) -> UniVar -> InfMonad ()
    solveOr solveWith whenSolved uni = lookupUniVar uni >>= either (const $ solveUniVar uni solveWith) whenSolved

check :: Expr -> Type -> InfMonad ()
check e = mono Out >=> match e
  where
    -- most of the cases don't need monomorphisation here
    -- it doesn't make a difference most of the time, since `subtype` monomorphises
    -- its arguments anyway
    --
    -- however, if, say, a lambda argument gets inferred to a univar, that univar would unify
    -- with a monomorphised type rather than a polytype
    --
    -- one option is to make `unMono` behave like univarsToForall / univarsToExists
    match = \cases
        (E.Name name) ty -> do
            ty' <- lookupSig name
            subtype ty' $ unMono ty
        (E.Constructor name) ty -> do
            ty' <- lookupSig name
            subtype ty' $ unMono ty
        (E.Lambda arg body) (MFn from to) -> scoped do
            -- `checkPattern` updates signatures of all mentioned variables
            checkPattern arg from
            check body to
        (E.Annotation expr ty') ty -> do
            subtype ty' $ unMono ty
            check expr ty'
        (E.If cond true false) ty -> do
            bool <- asks (.bool)
            check cond $ T.Name bool
            check true $ unMono ty
            check false $ unMono ty
        (E.Case arg matches) ty -> do
            argTy <- infer arg
            for_ matches \(pat, body) -> do
                checkPattern pat argTy
                check body $ unMono ty
        (E.List items) ty -> do
            list <- asks (.list)
            case ty of
                MApp (T.Name name) itemTy | name == list -> for_ items (`check` itemTy)
                other -> typeError $ "List is not a subtype of" <+> pretty other
        expr ty -> do
            ty' <- infer expr
            subtype ty' $ unMono ty

checkPattern :: Pattern' -> Type -> InfMonad ()
checkPattern = \cases
    (P.Var name) ty -> updateSig name ty
    -- it's not clear whether value constructors need a separate rule
    pat ty -> do
        ty' <- inferPattern pat
        subtype ty' ty

infer :: Expr -> InfMonad Type
infer = \case
    E.Name name -> lookupSig name
    E.Constructor name -> lookupSig name
    E.Variant name -> do
        var <- freshTypeVar
        -- rowVar <- freshTypeVar
        pure $ T.Forall var $ T.Function (T.Var var) (T.Variant $ fromList [(name, T.Var var)])
    E.Application f x -> do
        fTy <- infer f
        inferApp fTy x
    E.Lambda arg body -> {-forallScope-} do
        argTy <- inferPattern arg
        T.Function argTy <$> infer body
    E.Let binding body -> do
        inferBinding binding
        infer body
    E.Annotation expr ty -> ty <$ check expr ty
    E.If cond true false -> do
        bool <- asks (.bool)
        check cond $ T.Name bool
        trueTy <- infer true
        falseTy <- infer false
        supertype trueTy falseTy
    E.Case arg matches -> do
        argTy <- infer arg
        bodyTypes <- for matches \(pat, body) -> do
            -- overspecification *might* be a problem here if argTy gets inferred to a univar
            -- and the first Pattern' has a polymorphic type, like `Nothing : forall a. Maybe a`
            -- there's a test for this, and it passes. Weird.
            checkPattern pat argTy
            infer body
        firstTy <- T.UniVar <$> freshUniVar
        foldM supertype firstTy bodyTypes
    E.Match [] -> typeError "empty match expression"
    E.Match (m : ms) -> {-forallScope-} do
        (patTypes, bodyTypes) <-
            NE.unzip <$> for (m :| ms) \(pats, body) -> do
                patTypes <- traverse inferPattern pats
                bodyTy <- infer body
                pure (patTypes, bodyTy)
        unless (all ((== length (NE.head patTypes)) . length) patTypes) $
            typeError "different amount of arguments in a match statement"
        finalPatTypes <- foldlM1 (zipWithM supertype) patTypes
        resultType <- foldlM1 supertype bodyTypes
        pure $ foldr T.Function resultType finalPatTypes

    -- unless (length pats == length argTypes) $ typeError "incorrect arg count in a match"
    E.List items -> do
        itemTy <- T.UniVar <$> freshUniVar
        list <- asks (.list)
        T.Application (T.Name list) <$> (foldM supertype itemTy =<< traverse infer items)
    E.Record _ -> typeError "records are not supported yet"
    E.RecordLens _ -> typeError "record lens are not supported yet"
    E.IntLiteral _ -> T.Name <$> asks (.int)
    E.TextLiteral _ -> T.Name <$> asks (.text)
    E.CharLiteral _ -> T.Name <$> asks (.char)

inferBinding :: Binding Name -> InfMonad ()
inferBinding = \case
    E.ValueBinding pat body -> do
        bodyTy <- infer body
        checkPattern pat bodyTy
    E.FunctionBinding name args body -> do
        argTypes <- traverse inferPattern args
        bodyTy <- infer body
        updateSig name $ foldr T.Function bodyTy argTypes

inferPattern :: Pattern' -> InfMonad Type
inferPattern = \case
    P.Var name -> do
        uni <- T.UniVar <$> freshUniVar
        updateSig name uni
        pure uni
    p@(P.Constructor name args) -> do
        (resultType, argTypes) <- conArgTypes name
        unless (length argTypes == length args) $ typeError $ "incorrect arg count in Pattern'" <+> pretty p
        zipWithM_ checkPattern args argTypes
        pure resultType
    P.List pats -> do
        result <- T.UniVar <$> freshUniVar
        list <- asks (.list)
        T.Application (T.Name list) <$> (foldM supertype result =<< traverse inferPattern pats)
    P.Variant name arg -> do
        argTy <- inferPattern arg
        pure $ T.Variant $ fromList [(name, argTy)]
    P.Record _ -> typeError "record patterns are not supported yet"
    P.IntLiteral _ -> T.Name <$> asks (.int)
    P.TextLiteral _ -> T.Name <$> asks (.text)
    P.CharLiteral _ -> T.Name <$> asks (.char)
  where
    -- conArgTypes and the zipM may be unified into a single function
    conArgTypes = lookupSig >=> go
    go =
        mono In >=> \case
            MFn arg rest -> second (arg :) <$> go rest
            -- univars should never appear as the rightmost argument of a value constructor type
            -- i.e. types of value constructors have the shape `a -> b -> c -> d -> ConcreteType a b c d`
            --
            -- solved univars cannot appear here either, since `lookupSig` on a Pattern' returns a type with no univars
            MUniVar uni -> typeError $ "unexpected univar " <> pretty uni <> " in a constructor type"
            -- this kind of repetition is necessary to retain missing Pattern' warnings
            MName name -> pure (T.Name name, [])
            MApp lhs rhs -> pure (T.Application lhs rhs, [])
            MVariant row -> pure (T.Variant row, [])
            MRecord row -> pure (T.Record row, [])
            MSkolem skolem -> pure (T.Skolem skolem, [])

inferApp :: Type -> Expr -> InfMonad Type
inferApp fTy arg =
    mono In fTy >>= \case
        MUniVar v -> do
            from <- infer arg
            to <- freshUniVar
            lookupUniVar v >>= \case
                Left _ -> do
                    solveUniVar v $ T.Function from (T.UniVar to)
                    pure $ T.UniVar to
                Right newTy -> inferApp newTy arg
        MFn from to -> to <$ check arg from
        _ -> typeError $ pretty fTy <> " is not a function type"
