{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module NameResolution (runNameResolution, runScopeErrors, resolveNames, resolveExpr, resolveType, declare, Scope(..), UnboundVar (..), Warning (..), ScopeErrors (..)) where

import Relude hiding (State, runState, evalState, error, get, put, modify)

import CheckerTypes hiding (Scope)
import Data.HashMap.Strict qualified as Map
import Data.Traversable (for)
import Syntax
import Syntax.Declaration qualified as D
import Syntax.Expression qualified as E
import Syntax.Pattern qualified as P
import Syntax.Type qualified as T
import NameGen
import Effectful (Effect, Eff, (:>))
import Effectful.TH (makeEffect)
import Effectful.State.Static.Local (State, runState, evalState, get, put, modify)
import Effectful.Dispatch.Dynamic (reinterpret)
import qualified Data.Sequence as Seq


data ScopeErrors = ScopeErrors {errors :: Seq UnboundVar, warnings :: Seq Warning}

-- | a writer-like effect for scope warnings and errors
data ScopeErrorE :: Effect where
    Warn :: Warning -> ScopeErrorE m ()
    Error :: UnboundVar -> ScopeErrorE m ()

-- * other types

newtype Scope = Scope {table :: HashMap Text Name}

newtype UnboundVar = UnboundVar Text deriving (Show)
data Warning = Shadowing Text | UnusedVar Text deriving (Show)

makeEffect ''ScopeErrorE

runScopeErrors :: Eff (ScopeErrorE : es) a -> Eff es (a, ScopeErrors)
runScopeErrors = reinterpret (runState $ ScopeErrors Seq.empty Seq.empty) \_ -> \case
    Warn warning -> modify @ScopeErrors \se -> se{warnings = se.warnings Seq.|> warning}
    Error error' -> modify @ScopeErrors \se -> se{errors = se.errors Seq.|> error'}


type EnvEffs es = (State Scope :> es, NameGen :> es, ScopeErrorE :> es)

-- | run a state action without changing the `Scope` part of the state
scoped :: (EnvEffs es) => Eff es a -> Eff es a
scoped action = do
    prevScope <- get @Scope
    output <- action
    put prevScope
    pure output

-- todo: handle duplicate names (those that aren't just shadowing)
declare :: EnvEffs es => Text -> Eff es Name
-- each wildcard gets a unique id
declare "_" = freshName "_"
declare name = do
    scope <- get @Scope
    disambiguatedName <- freshName name
    case Map.lookup name scope.table of
        Just _ -> warn (Shadowing name)
        Nothing -> pass
    put $ Scope $ Map.insert name disambiguatedName scope.table
    pure disambiguatedName

-- | looks up a name in the current scope
resolve :: EnvEffs es => Text -> Eff es Name
resolve name = do
    scope <- get @Scope
    case scope.table & Map.lookup name of
        Just id' -> pure id'
        Nothing -> do
            error (UnboundVar name)
            -- this gives a unique id to every occurance of the same unbound name
            scoped $ declare name

runNameResolution :: HashMap Text Name -> Eff (State Scope : ScopeErrorE : es) a -> Eff es (a, ScopeErrors)
runNameResolution env = runScopeErrors . evalState (Scope env) 

resolveNames :: (NameGen :> es) => HashMap Text Name -> [Declaration Text] -> Eff es ([Declaration Name], ScopeErrors)
resolveNames env decls = runNameResolution env do
    mkGlobalScope
    traverse resolveDec decls
  where
    -- this is going to handle imports at some point
    mkGlobalScope :: EnvEffs es => Eff es ()
    mkGlobalScope = collectNames decls

{- | adds declarations to the current scope
this function should be used very carefully, since it will
generate different IDs when called twice on the same data
-}
collectNames :: EnvEffs es => [Declaration Text] -> Eff es ()
collectNames decls = for_ decls \case
    D.Value (E.FunctionBinding name _ _) _ -> void $ declare name
    D.Value (E.ValueBinding pat _) _ -> void $ declarePat pat
    D.Type name _ _ -> void $ declare name
    D.Alias name _ -> void $ declare name
    D.Signature _ _ -> pass

-- | resolves names in a declaration. Doesn't change the current scope
resolveDec :: EnvEffs es => Declaration Text -> Eff es (Declaration Name)
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
resolveBinding :: EnvEffs es => [Declaration Text] -> Binding Text -> Eff es (Binding Name)
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
declarePat :: EnvEffs es => Pattern Text -> Eff es (Pattern Name)
declarePat = \case
    P.Constructor con pats -> P.Constructor <$> resolve con <*> traverse declarePat pats
    nothingToResolve -> traverse declare nothingToResolve

{- | resolves names in an expression. Doesn't change the current scope

same story here. Most of the expressions use names, but a couple define them
-}
resolveExpr :: EnvEffs es => Expression Text -> Eff es (Expression Name)
resolveExpr e = scoped case e of
    E.Lambda arg body -> do
        arg' <- declarePat arg
        body' <- resolveExpr body
        pure $ E.Lambda arg' body'
    E.Application f arg -> E.Application <$> resolveExpr f <*> resolveExpr arg
    E.Let binding expr -> do
        -- resolveBinding is intended for top-level bindings and where clauses,
        -- so we have to declare the new vars with `collectNames`
        --
        -- yes, this is hacky
        collectNames [D.Value binding []]
        binding' <- resolveBinding [] binding
        expr' <- resolveExpr expr
        pure $ E.Let binding' expr'
    E.Case arg matches ->
        E.Case <$> resolveExpr arg <*> for matches \(pat, expr) -> scoped do
            pat' <- declarePat pat
            expr' <- resolveExpr expr
            pure (pat', expr')
    E.Match matches ->
        E.Match <$> for matches \(pats, expr) -> scoped do
            pats' <- traverse declarePat pats
            expr' <- resolveExpr expr
            pure (pats', expr')
    E.Annotation body ty -> E.Annotation <$> resolveExpr body <*> resolveType ty
    nothingToDeclare -> traverse resolve nothingToDeclare

-- | resolves names in a type. Doesn't change the current scope
resolveType :: EnvEffs es => Type' Text -> Eff es (Type' Name)
resolveType ty = scoped case ty of
    T.Forall var body -> do
        var' <- declare var
        body' <- resolveType body
        pure $ T.Forall var' body'
    T.Exists var body -> do
        var' <- declare var
        body' <- resolveType body
        pure $ T.Exists var' body'
    nothingToDeclare -> traverse resolve nothingToDeclare
