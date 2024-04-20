{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedRecordDot #-}

module NameResolution where

import Relude hiding (error)

import Control.Monad (ap)
import Data.HashMap.Strict qualified as Map
import Data.These

import Syntax.All
import Syntax.Declaration qualified as D
import Syntax.Expression qualified as E
import Syntax.Pattern qualified as P
import Syntax.Type qualified as T

-- | a writer-like monad for scope warnings and errors
data ScopeErrors e w a
    = Clean a
    | Errors (These (Seq e) (Seq w)) a
    deriving (Show, Functor)

warn :: w -> ScopeErrors e w ()
warn w = Errors (That $ one w) ()

error :: e -> ScopeErrors e w ()
error e = Errors (This $ one e) ()

-- a derived instance wouldn't do
instance Applicative (ScopeErrors e w) where
    pure = Clean
    (<*>) = ap

instance Monad (ScopeErrors e w) where
    wrappedX >>= f = case wrappedX of
        Clean x -> f x
        Errors errs x -> case f x of
            Clean y -> Errors errs y
            Errors errs2 y -> Errors (errs <> errs2) y

-- * other types

newtype Id = Id {asInt :: Int} deriving (Show, Eq)

inc :: Id -> Id
inc (Id n) = Id $ n + 1

newtype Scope = Scope {table :: HashMap Text Id}

newtype UnboundVar = UnboundVar Text
data Warning = Shadowing Text | UnusedVar Text

type EnvMonad = StateT (Id, Scope) (ScopeErrors UnboundVar Warning)

data NameExists = Resolve | Add

-- | run a state action without changing the `Scope` part of the state
scoped :: EnvMonad a -> EnvMonad a
scoped action = do
    prevScope <- gets snd
    output <- action
    modify $ second (const prevScope)
    pure output

-- todo: handle duplicate names
addName :: Text -> EnvMonad Id
addName name = do
    (id', scope) <- get
    case Map.lookup name scope.table of
        Just _ -> lift $ warn (Shadowing name)
        Nothing -> pass
    put (inc id', Scope $ Map.insert name id' scope.table)
    pure id'

-- | looks up a name in the current scope
resolve :: Text -> EnvMonad Id
resolve name = do
    scope <- gets snd
    case scope.table & Map.lookup name of
        Just id' -> pure id'
        Nothing -> do
            lift $ error (UnboundVar name)
            -- this gives a unique id to every occurance of the same unbound name
            -- not sure whether it's the right way to go
            scoped $ addName name

resolveNames :: [Declaration Text] -> ScopeErrors UnboundVar Warning [Declaration Id]
resolveNames decls = evaluatingStateT emptyScope do
    mkGlobalScope
    traverse (scoped . resolveDec) decls
  where
    emptyScope = (Id 0, Scope Map.empty)

    -- this is going to handle imports at some point
    mkGlobalScope :: EnvMonad ()
    mkGlobalScope = collectNames decls

-- | adds declarations to the current scope
collectNames :: [Declaration Text] -> EnvMonad ()
collectNames decls = for_ decls \case
    D.Value name _ _ _ -> void $ addName name
    D.Type name _ _ -> void $ addName name
    D.Alias name _ -> void $ addName name
    D.Signature _ _ -> pass

-- | resolves names in a declaration. Doesn't change the current scope
resolveDec :: Declaration Text -> EnvMonad (Declaration Id)
resolveDec decl = scoped case decl of
    D.Value name args body locals -> do
        name' <- resolve name
        args' <- traverse resolvePat args -- todo: handle name conflicts in patterns
        collectNames locals
        locals' <- traverse resolveDec locals
        body' <- resolveExpr body
        pure $ D.Value name' args' body' locals'
    D.Type name vars constrs -> do
        name' <- resolve name
        vars' <- traverse resolve vars
        constrs' <-
            constrs & traverse \(con, args) -> do
                con' <- addName con
                args' <- traverse resolveType args
                pure (con', args')
        pure $ D.Type name' vars' constrs'
    D.Alias alias body -> D.Alias <$> resolve alias <*> resolveType body
    D.Signature name ty -> D.Signature <$> resolve name <*> resolveType ty

-- | resolves names in a pattern. Adds all new names to the current scope
resolvePat :: Pattern Text -> EnvMonad (Pattern Id)
resolvePat = undefined

-- | resolves names in an expression. Doesn't change the current scope
resolveExpr :: Expression Text -> EnvMonad (Expression Id)
resolveExpr = undefined

-- | resolves names in a type. Doesn't change the current scope
resolveType :: Type' Text -> EnvMonad (Type' Id)
resolveType = undefined