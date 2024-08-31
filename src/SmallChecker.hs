{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedRecordDot #-}

module SmallChecker where

import Control.Monad (foldM)
import Data.HashMap.Strict qualified as HashMap
import Data.Text qualified as Text
import Relude hiding (Type)

-- a disambiguated name
data Name = Name Text Int deriving (Show, Eq, Generic, Hashable)
newtype UniVar = UniVar Int
    deriving (Show, Eq)
    deriving newtype (Hashable)
newtype Skolem = Skolem Name deriving (Show, Eq)
newtype Scope = Scope Int deriving (Show, Eq, Ord)

data Expr
    = EUnit
    | EName Name
    | EApp Expr Expr
    | ELambda Name Expr
    | EAnn Expr Type
    deriving (Show, Eq)

data Type
    = TUnit
    | TForall Name Type
    | TUniVar UniVar -- unification variable
    | TVar Name
    | TExists Skolem
    | -- | TSkolem Skolem -- I'm not sure whether it makes sense to differentiate between explicit 'exists' and skolems
      TFn Type Type
    deriving (Show, Eq)

data Monotype
    = MUnit
    | MVar Name
    | MExists Skolem
    | MFn Monotype Monotype

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
        TForall name body -> "∀" <> go parens (TVar name) <> ". " <> go parens body
        TUniVar (UniVar n) -> "#" <> show n
        TVar (Name name n) -> name <> postfix n "#"
        TExists (Skolem (Name name n)) -> name <> postfix n "?"
        -- TSkolem (Skolem n) -> "?" <> show n
        TFn from to
            | parens -> "(" <> go True from <> " -> " <> go False to <> ")"
            | otherwise -> go True from <> " -> " <> go False to

    postfix 0 _ = ""
    postfix n sym = sym <> show n

-- helpers

fromMonotype :: Monotype -> Type
fromMonotype = \case
    MUnit -> TUnit
    MVar v -> TVar v
    MExists v -> TExists v
    MFn in' out' -> TFn (fromMonotype in') (fromMonotype out')

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

alterUniVar :: Bool -> UniVar -> Type -> InfMonad ()
alterUniVar override uni ty
    | ty == TUniVar uni = typeError "infinite cycle in a uni var" -- the other option is to set the var to unsolved
    | otherwise = do
        -- here comes the magic. If the new type contains other univars, we change their scope
        lookupUniVar uni >>= \case
            Right _ | not override -> typeError $ "Internal error (probably a bug): attempted to solve a solved univar " <> pretty (TUniVar uni)
            Right _ -> pass
            Left scope -> rescope scope ty
        modify \s -> s{vars = HashMap.insert uni (Right ty) s.vars}
  where
    rescope scope = go
      where
        rescopeVar v oldScope = modify \s -> s{vars = HashMap.insert v (Left $ min oldScope scope) s.vars}
        go = \case
            TUniVar v -> lookupUniVar v >>= either (rescopeVar v) go
            TForall _ body' -> go body'
            TFn from to -> go from >> go to
            _terminal -> pass

lookupSig :: Name -> InfMonad Type
lookupSig name = maybe (typeError "unbound name???") pure =<< gets (HashMap.lookup name . (.sigs))

updateSig :: Name -> Type -> InfMonad ()
updateSig name ty = modify \s -> s{sigs = HashMap.insert name ty s.sigs}

-- | run the given action and discard signature updates
scoped :: InfMonad a -> InfMonad a
scoped action = do
    sigs <- gets (.sigs)
    action <* modify \s -> s{sigs}

-- unlike lookupUniVar, this function doesn't collapse nested univars
isUnsolved :: UniVar -> InfMonad Bool
isUnsolved uni =
    gets (HashMap.lookup uni . (.vars)) <&> \case
        Nothing -> True
        Just _ -> False

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
        TForall _ body' -> isRelevant uni body'
        TFn from to -> isRelevant uni from || isRelevant uni to
        _terminal -> False

--

substitute :: Type -> Name -> Type -> InfMonad Type
substitute replacement var = go
  where
    go = \case
        TVar v | v == var -> pure replacement
        TExists (Skolem v) | v == var -> pure replacement -- this only works if existentials and foralls share the namespace
        TFn in' out' -> TFn <$> go in' <*> go out'
        TForall v body
            | v /= var -> TForall v <$> go body
        -- we don't have to do anything in the 'v == var' case, because in `∀a. ∀a. body` the body can't mention the outer a
        TUniVar uni -> TUniVar uni <$ withUniVar uni (go >=> overrideUniVar uni)
        other -> pure other

substituteTy :: Type -> Type -> Type -> InfMonad Type
substituteTy from to = go
  where
    go = \case
        ty | ty == from -> pure to
        TFn in' out' -> TFn <$> go in' <*> go out'
        TForall v body -> TForall v <$> go body
        TUniVar uni -> TUniVar uni <$ withUniVar uni (go >=> overrideUniVar uni)
        other -> pure other

-- gets rid of all dangling UniVars
normalise :: Type -> InfMonad Type
normalise = \case
    TForall var body -> TForall var <$> normalise body
    TUniVar uni ->
        lookupUniVar uni >>= \case
            Left _ -> typeError $ "dangling univar " <> pretty (TUniVar uni)
            Right body -> normalise body
    TFn from to -> TFn <$> normalise from <*> normalise to
    terminal -> pure terminal

--

subtype :: Type -> Type -> InfMonad ()
subtype = \cases
    v@(TVar _) _ -> typeError $ "unbound type variable " <> pretty v
    _ v@(TVar _) -> typeError $ "unbound type variable " <> pretty v
    lhs rhs | lhs == rhs -> pass -- simple cases, i.e.  Unit-Unit, two univars or two exvars
    (TFn inl outl) (TFn inr outr) -> do
        subtype inr inl
        subtype outl outr
    lhs (TForall var rhs) -> do
        skolem <- freshSkolem var
        rhs' <- substitute (TExists skolem) var rhs
        subtype lhs rhs'
    (TForall var lhs) rhs -> do
        uniVar <- freshUniVar
        lhs' <- substitute (TUniVar uniVar) var lhs
        subtype lhs' rhs
    lhs (TUniVar uni) ->
        lookupUniVar uni >>= \case
            Right ty -> subtype lhs ty
            -- todo: cyclic ref check?
            Left _ -> solveUniVar uni lhs
    (TUniVar uni) rhs ->
        lookupUniVar uni >>= \case
            Right ty -> subtype ty rhs
            Left _ -> solveUniVar uni rhs
    {- -- seems like these two cases are redundant
    lhs v@(TExists _) -> do
        typeError $ pretty lhs <> " can't be a subtype of existential " <> pretty v
    v@(TExists _) rhs -> do
        typeError $ "existential " <> pretty v <> " can't be a subtype of " <> pretty rhs
    -}
    lhs rhs -> typeError $ pretty lhs <> " is not a subtype of " <> pretty rhs

check :: Expr -> Type -> InfMonad ()
check = \cases
    EUnit TUnit -> pass
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
        ty' <- substitute (TExists skolem) var ty
        check expr ty'
    expr ty -> do
        ty' <- infer expr
        subtype ty' ty

infer :: Expr -> InfMonad Type
infer = \case
    EUnit -> pure TUnit
    EName name -> lookupSig name
    EApp f x -> do
        fTy <- infer f
        inferApp fTy x
    ELambda arg body -> forallScope do
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

id' :: Expr
id' = ELambda x (EName x)
  where
    x = Name "x" 0

-- \x f -> f x
test :: Expr
test = ELambda x $ ELambda f $ EApp (EName f) (EName x)
  where
    x = Name "x" 0
    f = Name "f" 0

testTy :: Type
testTy = TForall a $ TFn (TVar a) $ TFn (TFn (TVar a) (TVar a)) (TVar a)
  where
    a = Name "a" 0

-- \x f -> f (f x)
test2 :: Expr
test2 = ELambda x $ ELambda f $ EApp (EName f) (EApp (EName f) (EName x))
  where
    x = Name "x" 0
    f = Name "f" 0

-- \x f -> f x x
test3 :: Expr
test3 = ELambda x $ ELambda f $ EApp (EApp (EName f) (EName x)) (EName x)
  where
    x = Name "x" 0
    f = Name "f" 0

-- \f x -> f x
test4 :: Expr
test4 = ELambda f $ ELambda x $ EApp (EName f) (EName x)
  where
    x = Name "x" 0
    f = Name "f" 0

{-
dropMarker :: ContextItem -> Context -> Context
dropMarker item = drop 1 . dropWhile (/=item)

substitute :: Type -> TypeVar -> Type -> Monotype
substitute replacement var = go where
    go = \case
        TVar v | v == var -> replacement
        TExists v | v == v' -> replacement
        TFn in' out' -> TFn (go in') (go out')
        -- I don't think this case needs to be handled at all, because name resolution
        TForall v body | v /= var -> TForall v (go body)
        other -> other

-- new var creation

mkVar :: InfMonad Var
mkVar = gets fst <* modify \(Var n, tv) -> (Var $ n + 1, tv)

typeVar :: InfMonad TypeVar
typeVar = gets snd <* modify \(v, TypeVar n) -> (v, TypeVar $ n + 1)

-- predicates (kind of)

existentials :: Context -> [TypeVar]
existentials = mapMaybe \case
    CUnsolved var -> Just var
    CSolved var _ -> Just var
    _ -> Nothing

freeTypeVars :: Type -> Set TypeVar
freeTypeVars = \case
    TUnit -> Set.empty
    TVar v -> one v
    TForall v body -> Set.delete v $ freeTypeVars body
    TExists v -> one v
    TFn in' out' -> freeTypeVars in' <> freeTypeVars out'

-- ???

-- substitute solved existential variables in a type, I guess?
-- this looks like a `fmap` for an open-recursive type, hmmm
apply :: Context -> Type -> Type
apply ctx = \case
    TUnit -> TUnit
    TVar v -> TVar v
    TForall v ty -> TForall v (apply ctx ty)
    TExists v -> case findSolved v of
        Nothing -> TExists v
        Just mono -> apply ctx $ fromMonotype mono
    TFn in' out' -> TFn (apply ctx in') (apply ctx out')
  where
    findSolved :: TypeVar -> Maybe Monotype
    findSolved var = listToMaybe [ty | CSolved var' ty <- ctx, var' == var]

-- todo: well-formedness checks everywhere

subtype :: Context -> Type -> Type -> InfMonad Context
subtype ctx (TVar a1) (TVar a2) | a1 == a2 = pure ctx
subtype ctx TUnit TUnit = pure ctx
subtype ctx (TExists a1) (TExists a2) | a1 == a2 && a1 `elem` existentials ctx = pure ctx
subtype ctx (TFn in1 out1) (TFn in2 out2) = do
    ctx' <- subtype ctx in2 in1
    subtype ctx' (apply ctx' out1) (apply ctx' out2)
subtype ctx ty (TForall a body) = do
    -- do we need alpha conversion here?
    -- I think... it's already handled by name resolution, but idk
    a' <- typeVar
    dropMarker (CForall a') <$> subtype (a' : ctx) ty (substitute (TVar a') a body)

subtype ctx (TForall a body) ty = do
    -- same here
    a' <- typeVar
    dropMarker (CMarker a') <$> subtype ([CMarker a', CExists a'] ++ ctx) (substitute (TExists a') a body) ty
subtype ctx ty (TExists a)
    | a `elem` existentials ctx && a `Set.notMember` freeTypeVars ty = instantiateL ctx a ty
subtype ctx (TExists a) ty
    | a `elem` existentials ctx && a `Set.notMember` freeTypeVars ty = instantiateR ctx ty a
subtype ctx ty1 ty2 = error $ "not a subtype " ++ show ty1 ++ " " ++ show ty2

instantiateL :: Context -> TypeVar -> Type -> InfMonad Context
instantiateL = undefined

instantiateR :: Context -> Type -> TypeVar -> InfMonad Context
instantiateR = undefined

check :: Context -> Expr -> Type -> InfMonad Context
check ctx = \cases
    EUnit TUnit -> pure ctx
    expr (TForall a body) -> do
        -- again, this should be redundant
        a' <- typeVar
        dropMarker (CForall a') <$> check (CForall a' : ctx) expr (substitute (TVar a') a body)
    (ELambda x body) (TFn in' out') -> do
        -- x' <- mkVar ?
        dropMarker (CVar x in') <$> check (CVar x in' : ctx) body out'
    expr ty -> do
        (inferred, ctx') <- infer body
        subtype ctx' (apply ctx' inferred) (apply ctx' ty)

infer :: Context -> Expr -> InfMonad (Type, Context)
infer ctx = \case
    EName x -> (findVarType ctx, ctx)
    EAnn expr ty -> (ty, ) <$> check ctx expr ty
    EUnit -> pure (TUnit, ctx)
    ELambda x body -> do
        -- x' <- mkVar -- we already have unique names here... I think
        in' <- typeVar
        out' <- typeVar
        ctx' <- dropMarker (CVar x (TExists in')) <$>
            check ([CExists in', CExists out', CVar x (TExists in')] ++ ctx) expr (TExists out')
        pure (TFn (TExists in') (TExists out'), ctx')
    EApp f arg -> do
        (fTy, ctx') <- infer ctx f
        inferApp ctx' (apply ctx' fTy) arg

inferApp :: Context -> Type -> Expr -> InfMonad (Type, Context)
inferApp ctx fTy arg = case fTy of
    TForall a body -> do
        a' <- typeVar
        inferApp (CExists a' : ctx) (substitute (TExists a') a body) arg
    TExists a -> do
        a1 <- typeVar
        a2 <- typeVar
        ctx <- check undefined
    TFn in' out' -> (out', ) <$> check ctx arg in'
    _ -> error $ "inferApp failed: " ++ show fty ++ " " ++ show arg

-}