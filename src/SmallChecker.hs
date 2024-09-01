{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedRecordDot #-}

module SmallChecker where

import Control.Monad (foldM)
import Data.HashMap.Strict qualified as HashMap
import Data.HashSet qualified as HashSet
import Data.Text qualified as Text
import Relude hiding (Type)

-- a disambiguated name
data Name = Name Text Int deriving (Show, Eq, Generic, Hashable)
newtype UniVar = UniVar Int
    deriving (Show, Eq)
    deriving newtype (Hashable)
newtype Skolem = Skolem Name
    deriving (Show, Eq)
    deriving newtype (Hashable)
newtype Scope = Scope Int deriving (Show, Eq, Ord)

data Expr
    = EUnit
    | ENothing
    | EJust
    | EName Name
    | EApp Expr Expr
    | ELambda Name Expr
    | EAnn Expr Type
    deriving (Show, Eq)

data Type
    = TUnit
    | TVar Name
    | TSkolem Skolem
    | TUniVar UniVar -- unification variable
    | TMaybe Type
    | TForall Name Type -- ∀a. body
    | TExists Name Type -- ∃a. body
    | TFn Type Type
    deriving (Show, Eq)

newtype TypeError = TypeError Text deriving (Show)

data InfState = InfState
    { nextUniVarId :: Int
    , nextSkolemId :: Int
    , nextTypeVar :: Name
    , currentScope :: Scope
    , sigs :: HashMap Name Type
    , vars :: HashMap UniVar (Either Scope Type) -- contains either the scope of an unsolved var or a type
    }

type InfMonad = ExceptT TypeError (State InfState)

pretty :: Type -> Text
pretty = go False
  where
    go parens = \case
        TUnit -> "()"
        TVar (Name name n) -> name <> postfix n "#"
        TSkolem (Skolem (Name name n)) -> name <> "?" <> postfix n ""
        TUniVar (UniVar n) -> "#" <> show n
        TMaybe body -> mkParens $ "Maybe " <> go True body
        TForall name body -> mkParens $ "∀" <> go parens (TVar name) <> ". " <> go parens body
        TExists name body -> mkParens $ "∃" <> go parens (TVar name) <> ". " <> go parens body
        TFn from to -> mkParens $ go True from <> " -> " <> go False to
      where
        mkParens txt
            | parens = "(" <> txt <> ")"
            | otherwise = txt

    postfix 0 _ = ""
    postfix n sym = sym <> show n

-- helpers

run :: InfMonad a -> Either TypeError a
run =
    evaluatingState
        InfState
            { nextUniVarId = 0
            , nextSkolemId = 0
            , nextTypeVar = Name "a" 0
            , currentScope = Scope 0
            , sigs = HashMap.empty
            , vars = HashMap.empty
            }
        . runExceptT

inferIO :: Expr -> IO ()
inferIO expr = case run $ fmap pretty . normalise =<< infer expr of
    Left (TypeError err) -> putTextLn err
    Right txt -> putTextLn txt

typeError :: Text -> InfMonad a
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
lookupUniVar uni = maybe (typeError $ "missing univar " <> pretty (TUniVar uni)) pure . HashMap.lookup uni =<< gets (.vars)

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
        Right _ | not override -> typeError $ "Internal error (probably a bug): attempted to solve a solved univar " <> pretty (TUniVar uni)
        Right _ -> pass
        Left scope -> rescope scope ty
    modify \s -> s{vars = HashMap.insert uni (Right ty) s.vars}
    cycleCheck (Direct, HashSet.empty) ty
  where
    foldUniVars :: (UniVar -> InfMonad ()) -> Type -> InfMonad ()
    foldUniVars action = \case
        TUniVar v -> action v >> lookupUniVar v >>= either (const pass) (foldUniVars action)
        TMaybe body -> foldUniVars action body
        TForall _ body -> foldUniVars action body
        TExists _ body -> foldUniVars action body
        TFn from to -> foldUniVars action from >> foldUniVars action to
        _terminal -> pass

    -- resolves direct univar cycles (i.e. a ~ b, b ~ c, c ~ a) to skolems
    -- errors out on indirect cycles (i.e. a ~ Maybe a)
    cycleCheck (selfRefType, acc) = \case
        TUniVar uni2 | HashSet.member uni2 acc -> case selfRefType of
            Direct -> do
                skolem <- freshSkolem $ Name "q" 0
                modify \s -> s{vars = HashMap.insert uni2 (Right $ TSkolem skolem) s.vars}
            Indirect -> typeError "self-referential type"
        TUniVar uni2 -> withUniVar uni2 $ cycleCheck (selfRefType, HashSet.insert uni2 acc)
        TMaybe body -> cycleCheck (Indirect, acc) body
        TForall _ body -> cycleCheck (Indirect, acc) body
        TExists _ body -> cycleCheck (Indirect, acc) body
        TFn from to -> cycleCheck (Indirect, acc) from >> cycleCheck (Indirect, acc) to
        _terminal -> pass

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
                substituteTy (TUniVar uni) ty bodyTy
            Left scope | scope > outerScope && isRelevant uni bodyTy -> do
                tyVar <- freshTypeVar
                solveUniVar uni (TVar tyVar)
                pure $ TForall tyVar bodyTy
            Left _ -> pure bodyTy
    isRelevant uni = \case
        TUniVar v | v == uni -> True
        TMaybe body' -> isRelevant uni body'
        TForall _ body' -> isRelevant uni body'
        TExists _ body' -> isRelevant uni body'
        TFn from to -> isRelevant uni from || isRelevant uni to
        _terminal -> False

--

substitute :: Type -> Name -> Type -> InfMonad Type
substitute replacement var = go
  where
    go = \case
        TVar v | v == var -> pure replacement
        -- TExists (Skolem v) | v == var -> pure replacement -- this only works if existentials and foralls share the namespace
        TUniVar uni -> TUniVar uni <$ withUniVar uni (go >=> overrideUniVar uni)
        TMaybe body -> TMaybe <$> go body
        TForall v body | v /= var -> TForall v <$> go body
        -- we don't have to do anything in the 'v == var' case, because in `∀a. ∀a. body` the body can't mention the outer a
        TExists v body | v /= var -> TExists v <$> go body
        -- the same goes for ∃
        TFn in' out' -> TFn <$> go in' <*> go out'
        other -> pure other

-- `substituteTy` shouldn't be used for type vars, because it fails in cases like `forall a. (forall a. body)`
-- normall those are removed by name resolution, but they may still occur when checking, say `f (f x)`
substituteTy :: Type -> Type -> Type -> InfMonad Type
substituteTy from to = go
  where
    go = \case
        ty | ty == from -> pure to
        TUniVar uni -> TUniVar uni <$ withUniVar uni (go >=> overrideUniVar uni)
        TMaybe body -> TMaybe <$> go body
        TForall v body -> TForall v <$> go body
        TExists v body -> TExists v <$> go body
        TFn in' out' -> TFn <$> go in' <*> go out'
        other -> pure other

-- gets rid of all univars
normalise :: Type -> InfMonad Type
normalise = uniVarsToForall >=> skolemsToExists >=> go
  where
    go = \case
        TUniVar uni ->
            lookupUniVar uni >>= \case
                Left _ -> typeError $ "dangling univar " <> pretty (TUniVar uni)
                Right body -> go body
        TMaybe body -> TMaybe <$> go body
        TForall var body -> TForall var <$> go body
        TExists var body -> TExists var <$> go body
        TFn from to -> TFn <$> go from <*> go to
        terminal -> pure terminal

    -- this is an alternative to forallScope that's only suitable at the top level
    uniVarsToForall ty = uncurry (foldr TForall) <$> uniGo HashSet.empty ty
    uniGo acc = \case
        TUniVar uni ->
            lookupUniVar uni >>= \case
                Left _ -> do
                    tyVar <- freshTypeVar
                    solveUniVar uni (TVar tyVar)
                    pure (TVar tyVar, HashSet.insert tyVar acc)
                Right body -> first (const $ TUniVar uni) <$> uniGo acc body
        TMaybe body -> first TMaybe <$> uniGo acc body
        TForall var body -> first (TForall var) <$> uniGo acc body
        TFn from to -> do
            (from', acc') <- uniGo acc from
            (to', acc'') <- uniGo acc' to
            pure (TFn from' to', acc'')
        terminal -> pure (terminal, acc)

--

subtype :: Type -> Type -> InfMonad ()
subtype = \cases
    v@(TVar _) _ -> typeError $ "unbound type variable " <> pretty v
    _ v@(TVar _) -> typeError $ "unbound type variable " <> pretty v
    lhs rhs | lhs == rhs -> pass -- simple cases, i.e.  Unit-Unit, two univars or two exvars
    (TMaybe lhs) (TMaybe rhs) -> subtype lhs rhs
    (TFn inl outl) (TFn inr outr) -> do
        subtype inr inl
        subtype outl outr
    lhs (TForall var rhs) -> do
        skolem <- freshSkolem var
        rhs' <- substitute (TSkolem skolem) var rhs
        subtype lhs rhs'
    (TForall var lhs) rhs -> do
        uniVar <- freshUniVar
        lhs' <- substitute (TUniVar uniVar) var lhs
        subtype lhs' rhs
    lhs (TExists var rhs) -> do
        uniVar <- freshUniVar
        lhs' <- substitute (TUniVar uniVar) var lhs
        subtype lhs' rhs
    (TExists var lhs) rhs -> do
        skolem <- freshSkolem var
        rhs' <- substitute (TSkolem skolem) var rhs
        subtype lhs rhs'
    lhs (TUniVar uni) -> solveOr lhs (subtype lhs) uni
    (TUniVar uni) rhs -> solveOr rhs (`subtype` rhs) uni
    lhs rhs -> typeError $ pretty lhs <> " is not a subtype of " <> pretty rhs
  where
    -- turns out it's different enough from `withUniVar`
    solveOr :: Type -> (Type -> InfMonad ()) -> UniVar -> InfMonad ()
    solveOr solveWith whenSolved uni = lookupUniVar uni >>= either (const $ solveUniVar uni solveWith) whenSolved

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
    skolemsToExists' ty = uncurry (foldr TExists) <$> go HashMap.empty ty
    -- b <: ∀a. a -> a
    -- b <: ?a -> ?a
    -- b ~ ∀a. a -> a
    skolemsToForall' ty = uncurry (foldr TForall) <$> go HashMap.empty ty

    go acc = \case
        TSkolem skolem -> case HashMap.lookup skolem acc of
            Just tyVar -> pure (TVar tyVar, acc)
            Nothing -> do
                tyVar <- freshTypeVar
                pure (TVar tyVar, HashMap.insert skolem tyVar acc)
        TUniVar uni -> pure (TUniVar uni, acc) -- I'm not sure what to do with a univar boundary
        TMaybe body -> first TMaybe <$> go acc body
        TForall var body -> first (TForall var) <$> go acc body
        TFn from to -> do
            (from', acc') <- go acc from
            (to', acc'') <- go acc' to
            pure (TFn from' to', acc'')
        terminal -> pure (terminal, acc)

check :: Expr -> Type -> InfMonad ()
check = \cases
    EUnit TUnit -> pass
    ENothing (TMaybe _) -> pass
    EJust ty -> do -- this case may be redundant
        uniVar <- freshUniVar
        subtype (TFn (TUniVar uniVar) (TMaybe $ TUniVar uniVar)) ty
    (EName name) ty -> do
        ty' <- lookupSig name
        subtype ty' ty
    (ELambda arg body) (TFn from to) -> scoped do
        updateSig arg from
        check body to
    (EAnn expr ty') ty -> do
        subtype ty' ty
        check expr ty'
    expr (TForall var ty) -> do
        skolem <- freshSkolem var
        ty' <- substitute (TSkolem skolem) var ty
        check expr ty'
    expr (TExists var ty) -> do
        uniVar <- freshUniVar
        ty' <- substitute (TUniVar uniVar) var ty
        check expr ty'
    expr ty -> do
        ty' <- infer expr
        subtype ty' ty

infer :: Expr -> InfMonad Type
infer = \case
    EUnit -> pure TUnit
    -- if we convert dangling univars to a forall clause, we won't need forallScope here
    ENothing -> {-forallScope $-} TMaybe . TUniVar <$> freshUniVar
    EJust -> {-forallScope-} do
        uniVar <- freshUniVar
        pure $ TFn (TUniVar uniVar) (TMaybe $ TUniVar uniVar)
    EName name -> lookupSig name
    EApp f x -> do
        fTy <- infer f
        inferApp fTy x
    ELambda arg body -> {-forallScope-} do
        argTy <- freshUniVar
        updateSig arg (TUniVar argTy)
        TFn (TUniVar argTy) <$> infer body
    EAnn expr ty -> ty <$ check expr ty

inferApp :: Type -> Expr -> InfMonad Type
inferApp fTy arg = case fTy of
    TForall v body -> do
        var <- freshUniVar
        fTy' <- substitute (TUniVar var) v body
        inferApp fTy' arg
    TExists v body -> do
        skolem <- freshSkolem v
        fTy' <- substitute (TSkolem skolem) v body
        inferApp fTy' arg
    TUniVar v -> do
        from <- infer arg
        to <- freshUniVar
        lookupUniVar v >>= \case
            Left _ -> do
                solveUniVar v $ TFn from (TUniVar to)
                pure $ TUniVar to
            Right newTy -> inferApp newTy arg
    TFn from to -> to <$ check arg from
    _ -> typeError $ pretty fTy <> " is not a function type"
