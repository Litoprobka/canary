{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedRecordDot #-}

module NameResolution (resolveNames, UnboundVar (..), Warning (..), ScopeErrors (..), Id) where

import Relude hiding (error)

import Control.Monad (ap)
import Data.HashMap.Strict qualified as Map
import Data.These
import Prelude qualified (show)

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

newtype Id = Id Int deriving (Eq)
instance Show Id where
    show (Id n) = "#" <> show n

inc :: Id -> Id
inc (Id n) = Id $ n + 1

newtype Scope = Scope {table :: HashMap Text Id}

newtype UnboundVar = UnboundVar Text deriving (Show)
data Warning = Shadowing Text | UnusedVar Text deriving (Show)

type EnvMonad = StateT (Id, Scope) (ScopeErrors UnboundVar Warning)

-- | run a state action without changing the `Scope` part of the state
scoped :: EnvMonad a -> EnvMonad a
scoped action = do
    prevScope <- gets snd
    output <- action
    modify $ second (const prevScope)
    pure output

-- todo: handle duplicate names (those that aren't just shadowing)
declare :: Text -> EnvMonad Id
declare name = do
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
            scoped $ declare name

resolveNames :: [Declaration Text] -> ScopeErrors UnboundVar Warning [Declaration Id]
resolveNames decls = evaluatingStateT emptyScope do
    mkGlobalScope
    traverse resolveDec decls
  where
    emptyScope = (Id 0, Scope Map.empty)

    -- this is going to handle imports at some point
    mkGlobalScope :: EnvMonad ()
    mkGlobalScope = collectNames decls

{- | adds declarations to the current scope
this function should be used very carefully, since it will
generate different IDs when called twice on the same data
-}
collectNames :: [Declaration Text] -> EnvMonad ()
collectNames decls = for_ decls \case
    D.Value (E.FunctionBinding name _ _) _ -> void $ declare name
    D.Value (E.ValueBinding pat _) _ -> void $ declarePat pat
    D.Type name _ _ -> void $ declare name
    D.Alias name _ -> void $ declare name
    D.Signature _ _ -> pass

-- | resolves names in a declaration. Doesn't change the current scope
resolveDec :: Declaration Text -> EnvMonad (Declaration Id)
resolveDec decl = scoped case decl of
    D.Value binding locals -> do
        binding' <- resolveBinding locals binding
        locals' <- traverse resolveDec locals
        pure $ D.Value binding' locals'
    D.Type name vars constrs -> do
        name' <- resolve name
        vars' <- traverse resolve vars
        constrs' <-
            constrs & traverse \(con, args) -> do
                con' <- declare con
                args' <- traverse resolveType args
                pure (con', args')
        pure $ D.Type name' vars' constrs'
    D.Alias alias body -> D.Alias <$> resolve alias <*> resolveType body
    D.Signature name ty -> D.Signature <$> resolve name <*> resolveType ty

{- | resolves names in a binding. Unlike the rest of the functions, it also
takes local definitions as an argument, and uses them after resolving the name / pattern
-}
resolveBinding :: [Declaration Text] -> Binding Text -> EnvMonad (Binding Id)
resolveBinding locals = \case
    E.FunctionBinding name args body -> do
        name' <- resolve name
        args' <- traverse declarePat args
        collectNames locals
        body' <- resolveExpr body
        pure $ E.FunctionBinding name' args' body'
    E.ValueBinding pat body -> do
        pat' <- traverse resolve pat -- `traverse` finally works
        collectNames locals
        body' <- resolveExpr body
        pure $ E.ValueBinding pat' body'

{- | resolves names in a pattern. Adds all new names to the current scope

this is *almost* the definition of `traverse` for Pattern, except for `Constructor`
should I use a separate var and make it a Bitraversable instead?
-}
declarePat :: Pattern Text -> EnvMonad (Pattern Id)
declarePat = \case
    P.Constructor con pats -> P.Constructor <$> resolve con <*> traverse declarePat pats
    nothingToResolve -> traverse declare nothingToResolve

{- | resolves names in an expression. Doesn't change the current scope

same story here. Most of the expressions use names, but a couple define them
-}
resolveExpr :: Expression Text -> EnvMonad (Expression Id)
resolveExpr e = scoped case e of
    E.Lambda args body -> do
        args' <- traverse declarePat args
        body' <- resolveExpr body
        pure $ E.Lambda args' body'
    E.Application f arg -> E.Application <$> resolveExpr f <*> resolveExpr arg
    E.Let binding expr -> do
        binding' <- resolveBinding [] binding
        expr' <- resolveExpr expr
        pure $ E.Let binding' expr'
    E.Case body matches ->
        E.Case <$> resolveExpr body <*> forM matches \(pat, expr) -> scoped do
            pat' <- declarePat pat
            expr' <- resolveExpr expr
            pure (pat', expr')
    E.Match matches ->
        E.Match <$> forM matches \(pats, expr) -> scoped do
            pats' <- traverse declarePat pats
            expr' <- resolveExpr expr
            pure (pats', expr')
    E.Annotation body ty -> E.Annotation <$> resolveExpr body <*> resolveType ty
    nothingToDeclare -> traverse resolve nothingToDeclare

-- | resolves names in a type. Doesn't change the current scope
resolveType :: Type' Text -> EnvMonad (Type' Id)
resolveType ty = scoped case ty of
    T.Forall vars body -> do
        vars' <- traverse declare vars
        body' <- resolveType body
        pure $ T.Forall vars' body'
    T.Exists vars body -> do
        vars' <- traverse declare vars
        body' <- resolveType body
        pure $ T.Forall vars' body'
    nothingToDeclare -> traverse resolve nothingToDeclare
