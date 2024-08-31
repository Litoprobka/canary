{-# LANGUAGE LambdaCase #-}
module SmallChecker where

import Relude hiding (Type)
import Data.Set qualified as Set

newtype TypeVar = TypeVar Int deriving (Eq)
newtype Var = Var Int deriving (Eq)

data Expr
    = EUnit
    | EName Var
    | EApp Expr Expr
    | ELambda Var Expr
    | EAnn Var Type
    deriving (Show, Eq)

data Type
    = TUnit
    | TForall TypeVar Type
    | TVar TypeVar
    | TExists TypeVar
    | TFn Type Type
    deriving (Show, Eq)

data Monotype
    = MUnit
    | MVar TypeVar
    | MExists TypeVar
    | MFn Monotype Monotype

data ContextItem
    = CForall TypeVar
    | CVar Var Type
    | CUnsolved TypeVar
    | CSolved TypeVar Monotype
    | CMarker TypeVar -- eh
    deriving Eq

type Context = [ContextItem]

type InfMonad = State (Var, TypeVar)

-- helpers

fromMonotype :: Monotype -> Type
fromMonotype = \case
    MUnit -> TUnit
    MVar v -> TVar v
    MExists v -> TExists v
    MFn in' out' -> TFn in' out'

dropMarker :: ContextItem -> Context -> Context
dropMarker item = drop 1 . dropWhile (/=item)

substitute :: Type -> TypeVar -> Type -> Monotype
substitute replacement var = go where
    go = \case
        TVar v | v == var = replacement
        TExists v | v == v' = replacement
        TFn in' out' = TFn (go in') (go out')
        -- I don't think this case needs to be handled at all, because name resolution
        TForall v body | v /= var = TForall v (go body)
        other -> other

-- new var creation

mkVar :: InfMonad Var
mkVar = gets fst <* modify \(Var n, tv) -> (Var $ n + 1, tv)

typeVar :: InfMonad TypeVar
typeVar = gets snd <* modify \(v, TypeVar n) -> (v, TypeVar $ n + 1)

-- predicates (kind of)

existentials :: Context -> [TypeVar]
existentials = concatMap \case
    CUnsolved var -> [var]
    CSolved var _ -> [var]
    _ -> []

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
    | a `elem` existentials ctx && a `Set.notMember` freeTypeVars ty -> instantiateL ctx a ty
subtype ctx (TExists a) ty = undefined
    | a `elem` existentials ctx && a `Set.notMember` freeTypeVars ty -> instantiateR ctx ty a
subtype ctx ty1 ty2 = error $ "not a subtype " ++ show ty1 ++ " " ++ show ty2

instantiateL :: Context -> TypeVar -> Type -> InfMonad Context

instantiateR :: Context -> Type -> TypeVar -> InfMonad Context

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
