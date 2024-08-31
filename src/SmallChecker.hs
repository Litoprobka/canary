{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedRecordDot #-}

module SmallChecker where

import Data.HashMap.Strict qualified as HashMap
import Data.Set qualified as Set
import Relude hiding (Type)

-- a disambiguated name
data Name = Name Text Int deriving (Show, Eq, Generic, Hashable)
newtype UniVar = UniVar Int deriving (Show, Eq)
    deriving newtype (Hashable)
newtype Skolem = Skolem Name deriving (Show, Eq)

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

pretty :: Type -> Text
pretty = go 0
  where
    go prec = \case
        TUnit -> "()"
        TForall name body -> "∀" <> go prec (TVar name) <> ". " <> go prec body
        TUniVar (UniVar n) -> "#" <> show n
        TVar (Name name n) -> name <> postfix n "#"
        TExists (Skolem (Name name n)) -> name <> postfix n "?"
        -- TSkolem (Skolem n) -> "?" <> show n
        TFn from to
            | prec == 0 -> go (succ prec) from <> " -> " <> go prec to
            | otherwise -> "(" <> go prec from <> " -> " <> go (pred prec) to <> ")"
      where
        postfix 0 sym = ""
        postfix n sym = sym <> show n

newtype TypeError = TypeError Text deriving (Show)

data InfState = InfState
    { nextId :: Int
    , sigs :: HashMap Name Type
    , vars :: HashMap UniVar Type
    }

type InfMonad = ExceptT TypeError (State InfState)

-- helpers

fromMonotype :: Monotype -> Type
fromMonotype = \case
    MUnit -> TUnit
    MVar v -> TVar v
    MExists v -> TExists v
    MFn in' out' -> TFn (fromMonotype in') (fromMonotype out')

run :: InfMonad a -> Either TypeError a
run = evaluatingState InfState{nextId = 0, sigs = HashMap.empty, vars = HashMap.empty} . runExceptT

typeError :: Text -> InfMonad a
typeError err = ExceptT $ pure (Left $ TypeError err)

fresh :: InfMonad Int
fresh = gets (.nextId) <* modify \s -> s{nextId = succ s.nextId}

freshUniVar :: InfMonad UniVar
freshUniVar = UniVar <$> fresh

freshSkolem :: Name -> InfMonad Skolem
freshSkolem (Name name _) = Skolem . Name name <$> fresh

freshTypeVar :: InfMonad Name
freshTypeVar = Name "a" <$> fresh

lookupUniVar :: UniVar -> InfMonad (Maybe Type)
lookupUniVar uni = gets $ HashMap.lookup uni . (.vars)

withUniVar :: UniVar -> (Type -> InfMonad a) -> InfMonad ()
withUniVar uni f =
    lookupUniVar uni >>= \case
        Nothing -> pass
        Just ty -> void $ f ty

solveUniVar :: UniVar -> Type -> InfMonad ()
solveUniVar uni ty = do
    lookupUniVar uni >>= \case
        Just prevTy | prevTy == TUniVar uni -> typeError "infinite cycle in a uni var" -- the other option is to set the var to unsolved
        _ -> pass
    modify \s -> s{vars = HashMap.insert uni ty s.vars}

lookupSig :: Name -> InfMonad Type
lookupSig name = maybe (typeError "unbound name???") pure =<< gets (HashMap.lookup name . (.sigs))

updateSig :: Name -> Type -> InfMonad ()
updateSig name ty = modify \s -> s{sigs = HashMap.insert name ty s.sigs}

-- | run the given action and discard signature updates
scoped :: InfMonad a -> InfMonad a
scoped action = do
    sigs <- gets (.sigs)
    action <* modify \s -> s{sigs}

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
        TUniVar uni -> TUniVar uni <$ withUniVar uni (go >=> solveUniVar uni)
        other -> pure other

substituteTy :: Type -> Type -> Type -> InfMonad Type
substituteTy from to = go where
    go = \case
        ty | ty == from -> pure to
        TFn in' out' -> TFn <$> go in' <*> go out'
        TForall v body -> TForall v <$> go body
        TUniVar uni -> TUniVar uni <$ withUniVar uni (go >=> solveUniVar uni)
        other -> pure other

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
            Just ty -> subtype lhs ty
            -- todo: cyclic ref check?
            Nothing -> solveUniVar uni lhs
    (TUniVar uni) rhs ->
        lookupUniVar uni >>= \case
            Just ty -> subtype ty rhs
            Nothing -> solveUniVar uni rhs
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
    ELambda arg body -> do -- note that this isn't scoped
        argTy <- freshUniVar
        updateSig arg (TUniVar argTy)
        resultTy <- infer body
        lookupUniVar argTy >>= \case
            Just ty -> TFn ty <$> substituteTy (TUniVar argTy) ty resultTy
            Nothing -> do
                argVar <- freshTypeVar
                TForall argVar . TFn (TVar argVar) <$> substituteTy (TUniVar argTy) (TVar argVar) resultTy
                
    EAnn expr ty -> ty <$ check expr ty

inferApp :: Type -> Expr -> InfMonad Type
inferApp fTy arg = case fTy of
    TForall v body -> do
        var <- freshUniVar
        fTy' <- substitute (TUniVar var) v body
        inferApp fTy' arg
    v@(TExists _) -> typeError $ pretty v <> " is not a function"
    TFn from to -> to <$ check arg from
    _ -> typeError $ "inferApp failed: " <> pretty fTy <> " " <> show arg

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