{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedRecordDot #-}

module NameResolution (resolveNames, UnboundVar (..), Warning (..)) where

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

-- | adds declarations to the current scope
collectNames :: [Declaration Text] -> EnvMonad ()
collectNames decls = for_ decls \case
    D.Value name _ _ _ -> void $ declare name
    D.Type name _ _ -> void $ declare name
    D.Alias name _ -> void $ declare name
    D.Signature _ _ -> pass

-- | resolves names in a declaration. Doesn't change the current scope
resolveDec :: Declaration Text -> EnvMonad (Declaration Id)
resolveDec decl = scoped case decl of
    D.Value name args body locals -> do
        name' <- resolve name
        args' <- traverse declarePat args -- todo: handle name conflicts in patterns
        collectNames locals
        body' <- resolveExpr body
        locals' <- traverse resolveDec locals
        pure $ D.Value name' args' body' locals'
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

{- | resolves names in a pattern. Adds all new names to the current scope

this is *almost* the definition of `traverse` for Pattern, except for `Constructor`
should I use a separate var and make it a Bitraversable instead?
-}
declarePat :: Pattern Text -> EnvMonad (Pattern Id)
declarePat = \case
    P.Var name -> P.Var <$> declare name
    P.Constructor con pats -> P.Constructor <$> resolve con <*> traverse declarePat pats
    P.Variant con pats -> P.Variant con <$> traverse declarePat pats
    P.Record fields -> P.Record <$> traverse declarePat fields
    P.List pats -> P.List <$> traverse declarePat pats
    P.IntLiteral n -> pure $ P.IntLiteral n
    P.TextLiteral txt -> pure $ P.TextLiteral txt
    P.CharLiteral txt -> pure $ P.CharLiteral txt

{- | resolves names in an expression. Doesn't change the current scope

same story here. Most of the expressions use names, but a couple define them
-}
resolveExpr :: Expression Text -> EnvMonad (Expression Id)
resolveExpr e = scoped case e of
    E.Lambda args body -> do
        args' <- traverse declarePat args
        body' <- resolveExpr body
        pure $ E.Lambda args' body'
    E.Application f args -> E.Application <$> resolveExpr f <*> traverse resolveExpr args
    E.Let (pat, body) expr -> do
        pat' <- declarePat pat
        body' <- resolveExpr body -- should I allow recursive bindings in `let`?
        expr' <- resolveExpr expr
        pure $ E.Let (pat', body') expr'
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
    E.If cond true false -> E.If <$> resolveExpr cond <*> resolveExpr true <*> resolveExpr false
    E.Annotation body ty -> E.Annotation <$> resolveExpr body <*> resolveType ty
    E.Name name -> E.Name <$> resolve name
    E.Constructor name -> E.Name <$> resolve name
    E.Variant name -> pure $ E.Variant name
    E.Record fields -> E.Record <$> traverse resolveExpr fields
    E.List exprs -> E.List <$> traverse resolveExpr exprs
    -- terminals
    E.RecordLens fields -> pure $ E.RecordLens fields
    E.IntLiteral n -> pure $ E.IntLiteral n
    E.TextLiteral txt -> pure $ E.TextLiteral txt
    E.CharLiteral txt -> pure $ E.CharLiteral txt

-- | resolves names in a type. Doesn't change the current scope
resolveType :: Type' Text -> EnvMonad (Type' Id)
resolveType ty = scoped case ty of
    T.Name name -> T.Name <$> resolve name
    T.Var var -> T.Var <$> resolve var
    T.Application fty args -> T.Application <$> resolveType fty <*> traverse resolveType args
    T.Forall vars body -> do
        vars' <- traverse declare vars
        body' <- resolveType body
        pure $ T.Forall vars' body'
    T.Exists vars body -> do
        vars' <- traverse declare vars
        body' <- resolveType body
        pure $ T.Forall vars' body'
    T.Variant variants -> T.Variant <$> traverse (traverse resolveType) variants
    T.Record fields -> T.Record <$> traverse resolveType fields
