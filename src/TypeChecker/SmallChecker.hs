{-# LANGUAGE DuplicateRecordFields #-}

module TypeChecker.SmallChecker where

import Common (Located (..), UniVar)
import Common qualified as C
import Data.EnumMap.Strict qualified as EMap
import Data.HashMap.Strict qualified as HashMap
import Data.List ((!!))
import Diagnostic (Diagnose, internalError, internalError')
import Effectful.State.Static.Local (State, get, gets, modify)
import IdMap qualified
import LangPrelude hiding (force, lift)
import NameGen (NameGen, freshId)
import Prettyprinter (parens)
import Syntax.Term (Visibility (..))
import Prelude qualified

data UniVarState = Solved Value | Unsolved deriving (Show)
type UniVars = EnumMap UniVar UniVarState

newtype Index = Index {getIndex :: Int} deriving (Show, Eq, Enum)
newtype Level = Level {getLevel :: Int} deriving (Show, Eq, Enum)

levelToIndex :: Level -> Level -> Index
levelToIndex (Level l) (Level x) = Index $ l - x - 1

type Name = Text

-- type RTerm = Located RTerm_
type RTerm = RTerm_
data RTerm_
    = RName Name
    | RApp Visibility RTerm RTerm
    | RLambda Visibility Name RTerm
    | RPi Visibility Name RTerm RTerm
    | RType

data Term
    = Name Name Index
    | App Visibility Term Term
    | Lambda Visibility Name Term
    | Pi Visibility Name Term Term
    | Type
    | UniVar UniVar
    | InsertedUniVar UniVar [BD]

instance Pretty Term where
    pretty = \case
        Name name ix -> pretty name <> "@" <> pretty ix.getIndex
        App vis lhs rhs -> parens $ pretty lhs <+> pretty rhs
        Lambda vis var body -> parens $ "\\" <> pretty var <+> "->" <+> pretty body
        Pi vis name ty body -> parens $ parens (pretty name <+> ":" <+> pretty ty) <+> "->" <+> pretty body
        Type -> "Type"
        UniVar uni -> "<uni>"
        InsertedUniVar{} -> "<inserted uni>"

instance Show Term where
    show = show . pretty

type Elaborated = Term

type Ty = Value

data Value
    = StuckVar Name Level Spine
    | VLambda Visibility Closure
    | VPi Visibility ~Ty Closure
    | VType
    | StuckUniVar UniVar Spine
    deriving (Show)

pattern Var :: Name -> Level -> Value
pattern Var txt lvl <- StuckVar txt lvl []
    where
        Var txt lvl = StuckVar txt lvl []

pattern VUniVar :: UniVar -> Value
pattern VUniVar uni <- StuckUniVar uni []
    where
        VUniVar uni = StuckUniVar uni []

type Spine = [(Visibility, Value)]

newtype Env = Env {getEnv :: [Value]} deriving (Show)

data Closure = Closure {env :: Env, var :: Name, body :: Term} deriving (Show)

eval :: Env -> UniVars -> Term -> Value
eval env unis = \case
    Name _ ix -> env.getEnv !! ix.getIndex
    App vis lhs rhs -> evalApp unis vis (eval env unis lhs) (eval env unis rhs)
    Lambda vis var body -> VLambda vis $ Closure env var body
    Pi vis var ty body -> VPi vis (eval env unis ty) $ Closure env var body
    Type -> VType
    UniVar uni -> forceUniVar uni unis
    InsertedUniVar uni bds -> appBDs unis env (forceUniVar uni unis) bds

eval' :: State UniVars :> es => Env -> Term -> Eff es Value
eval' env t = do
    unis <- get
    pure $ eval env unis t

evalApp :: UniVars -> Visibility -> Value -> Value -> Value
evalApp unis vis f x = case f of
    VLambda _ closure -> appClosure unis closure x
    StuckVar var lvl spine -> StuckVar var lvl ((vis, x) : spine)
    StuckUniVar uni spine -> StuckUniVar uni ((vis, x) : spine)
    _ -> error "invalid application"

evalApp' :: State UniVars :> es => Visibility -> Value -> Value -> Eff es Value
evalApp' vis lhs rhs = do
    unis <- get
    pure $ evalApp unis vis lhs rhs

appBDs :: UniVars -> Env -> Value -> [BD] -> Value
appBDs unis = \cases
    (Env []) val [] -> val
    (Env (t : env)) val (Bound : bds) -> evalApp unis Visible (appBDs unis (Env env) val bds) t
    (Env (_ : env)) val (Defined : bds) -> appBDs unis (Env env) val bds
    _ _ _ -> error "bound-defined / env mismatch"

appClosure :: UniVars -> Closure -> Value -> Value
appClosure unis closure val = eval (Env $ val : closure.env.getEnv) unis closure.body

appClosureEff :: State UniVars :> es => Closure -> Value -> Eff es Value
appClosureEff closure val = do
    unis <- get
    pure $ appClosure unis closure val

appSpine :: UniVars -> Value -> Spine -> Value
appSpine unis val = \case
    [] -> val
    (vis, arg) : spine -> evalApp unis vis (appSpine unis val spine) arg

quote :: UniVars -> Level -> Value -> Term
quote unis lvl = \case
    VLambda vis closure ->
        Lambda vis closure.var $
            quote unis (succ lvl) $
                appClosure unis closure (Var closure.var lvl)
    VPi vis ty closure ->
        Pi vis closure.var (quote unis lvl ty) $
            quote unis (succ lvl) $
                appClosure unis closure (Var closure.var lvl)
    VType -> Type
    StuckVar var vlvl spine -> quoteSpine (Name var $ levelToIndex lvl vlvl) spine
    StuckUniVar uni spine -> quoteSpine (UniVar uni) spine
  where
    quoteSpine = foldr (\(vis, arg) acc -> App vis acc (quote unis lvl arg))

lookupUniVar :: UniVar -> UniVars -> UniVarState
lookupUniVar uni unis = case EMap.lookup uni unis of
    Just mbSolved -> mbSolved
    Nothing -> error "out of scope univar"

forceUniVar :: UniVar -> UniVars -> Value
forceUniVar uni unis = case lookupUniVar uni unis of
    Solved val -> val
    Unsolved -> VUniVar uni

force' :: UniVars -> Value -> Value
force' unis = \case
    StuckUniVar uni spine
        | Solved val <- lookupUniVar uni unis ->
            force' unis (appSpine unis val spine)
    other -> other

force :: State UniVars :> es => Value -> Eff es Value
force val = gets @UniVars (`force'` val)

data BD = Bound | Defined deriving (Show)

data Context = Context
    { env :: Env
    , level :: Level
    , types :: HashMap Name (Level, Ty)
    , bounds :: [BD]
    }

emptyContext :: Context
emptyContext = Context{env = Env [], level = Level 0, bounds = [], types = HashMap.empty}

bind :: Name -> Ty -> Context -> Context
bind name ty ctx = define name (Var name ctx.level) ty ctx

define :: Name -> Value -> Ty -> Context -> Context
define name val ty ctx =
    ctx
        { level = succ ctx.level
        , env = Env $ val : ctx.env.getEnv
        , types = HashMap.insert name (ctx.level, ty) ctx.types
        }

check :: (Diagnose :> es, State UniVars :> es, NameGen :> es) => Context -> RTerm -> Ty -> Eff es Term
check ctx t {-(t :@ loc)-} ty = do
    ty' <- force ty
    case (t, ty') of
        (RLambda vis var body, VPi _vis argTy closure) -> do
            bodyTy <- closure `appClosureEff` Var var ctx.level
            Lambda vis var <$> check (bind var argTy ctx) body bodyTy
        (_, expected) -> do
            (elab, inferred) <- infer ctx t -- (t :@ loc)
            unify ctx.level expected inferred
            pure elab

infer :: (Diagnose :> es, State UniVars :> es, NameGen :> es) => Context -> RTerm -> Eff es (Term, Ty)
infer ctx t {-(t :@ loc)-} = case t of
    RName name -> case HashMap.lookup name ctx.types of
        Just (lvl, ty) -> pure (Name name (levelToIndex ctx.level lvl), ty)
        Nothing -> internalError' $ pretty name <+> "not in scope"
    RApp vis lhs rhs -> do
        (eLhs, lhsTy) <- infer ctx lhs
        (argTy, closure) <-
            force lhsTy >>= \case
                VPi _ argTy closure -> pure (argTy, closure)
                other -> do
                    argTy <- eval' ctx.env =<< freshUniVar ctx
                    closure <- Closure ctx.env "x" <$> freshUniVar (bind "x" argTy ctx)
                    unify ctx.level (VPi Visible argTy closure) other
                    pure (argTy, closure)
        eRhs <- check ctx rhs argTy
        resultTy <- closure `appClosureEff` lhsTy
        pure (App vis eLhs eRhs, resultTy)
    RLambda vis var body -> do
        argTy <- eval' ctx.env =<< freshUniVar ctx
        (eBody, bodyTy) <- infer (bind var argTy ctx) body
        unis <- get @UniVars
        pure (Lambda vis var eBody, VPi vis argTy $ Closure{env = ctx.env, var, body = quote unis (succ ctx.level) bodyTy})
    RPi vis var ty body -> do
        eTy <- check ctx ty VType
        tyV <- eval' ctx.env eTy
        eBody <- check (bind var tyV ctx) body VType
        pure (Pi vis var eTy eBody, VType)
    RType -> pure (Type, VType)

unify :: (Diagnose :> es, State UniVars :> es) => Level -> Ty -> Ty -> Eff es ()
unify lvl = \cases
    (VLambda vis closure) (VLambda vis2 closure2) | vis == vis2 -> do
        body <- closure `appClosureEff` Var closure.var lvl
        body2 <- closure2 `appClosureEff` Var closure.var lvl
        unify (succ lvl) body body2
    nonLambda (VLambda vis closure) -> do
        body <- evalApp' vis nonLambda (Var closure.var lvl)
        body2 <- closure `appClosureEff` Var closure.var lvl
        unify (succ lvl) body body2
    (VLambda vis closure) nonLambda -> do
        body <- closure `appClosureEff` Var closure.var lvl
        body2 <- evalApp' vis nonLambda (Var closure.var lvl)
        unify (succ lvl) body body2
    VType VType -> pass
    (VPi vis ty closure) (VPi vis2 ty2 closure2) | vis == vis2 -> do
        unify lvl ty ty2
        body <- closure `appClosureEff` Var closure.var lvl
        body2 <- closure2 `appClosureEff` Var closure.var lvl
        unify (succ lvl) body body2
    (StuckVar _ vlvl spine) (StuckVar _ vlvl2 spine2) | vlvl == vlvl2 -> do
        unifySpine lvl spine spine2
    (StuckUniVar uni spine) (StuckUniVar uni2 spine2) | uni == uni2 -> do
        unifySpine lvl spine spine2
    (StuckUniVar uni spine) ty -> solve lvl uni spine ty
    ty (StuckUniVar uni spine) -> solve lvl uni spine ty
    _lhs _rhs -> internalError' "unification error"

unifySpine :: (Diagnose :> es, State UniVars :> es) => Level -> Spine -> Spine -> Eff es ()
unifySpine lvl = \cases
    [] [] -> pass
    ((vis1, ty1) : s1) ((vis2, ty2) : s2) -> do
        unless (vis1 == vis2) $ internalError' "application visibility mismatch"
        unifySpine lvl s1 s2
        unify lvl ty1 ty2
    _ _ -> internalError' "spine length mismatch"

-- * Unification

freshUniVar :: (NameGen :> es, State UniVars :> es) => Context -> Eff es Term
freshUniVar ctx = do
    uni <- C.UniVar <$> freshId
    modify @UniVars $ EMap.insert uni Unsolved
    pure $ InsertedUniVar uni ctx.bounds

data PartialRenaming = PartialRenaming
    { domain :: Level
    , codomain :: Level
    , renaming :: EnumMap Level Level
    }

-- | add a variable to a partial renaming
lift :: PartialRenaming -> PartialRenaming
lift PartialRenaming{domain, codomain, renaming} =
    PartialRenaming
        { domain = succ domain
        , codomain = succ codomain
        , renaming = EMap.insert codomain domain renaming
        }

-- | convert a spine to a partial renaming
invert :: (Diagnose :> es, State UniVars :> es) => Level -> Spine -> Eff es PartialRenaming
invert codomain spine = do
    (domain, renaming) <- go spine
    pure $ PartialRenaming{domain, codomain, renaming}
  where
    go [] = pure (Level 0, EMap.empty)
    go ((_, ty) : rest) = do
        (domain, renaming) <- go rest
        force ty >>= \case
            Var _ vlvl | EMap.notMember vlvl renaming -> pure (succ domain, EMap.insert vlvl domain renaming)
            _ -> internalError' "non-var in spine"

rename :: (Diagnose :> es, State UniVars :> es) => UniVar -> PartialRenaming -> Value -> Eff es Term
rename uni = go
  where
    goSpine _ term [] = pure term
    goSpine pren term ((vis, ty) : spine) = App vis <$> goSpine pren term spine <*> go pren ty

    go pren ty =
        force ty >>= \case
            StuckUniVar uni2 spine
                | uni == uni2 -> internalError' "self-referential type"
                | otherwise -> goSpine pren (UniVar uni) spine
            StuckVar var lvl spine -> case EMap.lookup lvl pren.renaming of
                Nothing -> internalError' $ "escaping variable" <+> pretty var <> "#" <> pretty lvl.getLevel
                Just x -> goSpine pren (Name var $ levelToIndex pren.domain x) spine
            VLambda vis closure -> do
                bodyToRename <- closure `appClosureEff` Var closure.var pren.codomain
                Lambda vis closure.var <$> go (lift pren) bodyToRename
            VPi vis argTyV closure -> do
                argTy <- go pren argTyV
                bodyToRename <- closure `appClosureEff` Var closure.var pren.codomain
                Pi vis closure.var argTy <$> go (lift pren) bodyToRename
            VType -> pure Type

lambdas :: Level -> Term -> Term
lambdas lvl = go (Level 0)
  where
    go x term | x == lvl = term
    go x term = Lambda Visible "x" $ go (succ x) term

solve :: (Diagnose :> es, State UniVars :> es) => Level -> UniVar -> Spine -> Value -> Eff es ()
solve ctxLevel uni spine rhs = do
    pren <- invert ctxLevel spine
    rhs' <- rename uni pren rhs
    solution <- eval' (Env []) $ lambdas pren.domain rhs'
    modify @UniVars $ EMap.insert uni $ Solved solution
