{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}

module NameResolution (
    runNameResolution,
    runDeclare,
    resolveNames,
    resolveExpr,
    resolveType,
    resolve,
    declare,
    declarePat,
    Scope (..),
    Declare,
) where

import Common hiding (Scope)
import Data.HashMap.Strict qualified as Map
import Data.List (partition)
import Data.List.NonEmpty qualified as NE
import Data.Traversable (for)
import Diagnostic
import Effectful.Dispatch.Dynamic (interpret)
import Effectful.State.Static.Local (State, evalState, get, modify, put)
import Error.Diagnose (Report (..))
import Error.Diagnose qualified as M
import LangPrelude hiding (error)
import NameGen
import Syntax
import Syntax.Declaration qualified as D
import Syntax.Expression (DoStatement)
import Syntax.Expression qualified as E
import Syntax.Pattern qualified as P
import Syntax.Type qualified as T

{-
The name resolution pass. Transforms 'Parse AST into 'NameRes AST. It doesn't short-circuit on errors
-}

{- | a one-off effect to differentiate functions that do and don't declare stuff
| on type level
-}
data Declare :: Effect where
    Declare :: SimpleName -> Declare m Name

makeEffect ''Declare

-- * other types

newtype Scope = Scope {table :: HashMap SimpleName_ Name}
data Warning = Shadowing SimpleName Loc | UnusedVar SimpleName deriving (Show)
newtype Error = UnboundVar SimpleName

warn :: Diagnose :> es => Warning -> Eff es ()
warn =
    nonFatal . \case
        Shadowing name loc ->
            Warn
                Nothing
                ("The binding" <+> pretty name <+> "shadows an earlier binding")
                (mkNotes [(getLoc name, M.This "new binding"), (loc, M.Where "previously bound at")])
                []
        UnusedVar name ->
            Warn
                Nothing
                ("The binding" <+> pretty name <+> "is unused")
                (mkNotes [(getLoc name, M.This "bound at")])
                []

error :: Diagnose :> es => Error -> Eff es ()
error =
    nonFatal . \case
        UnboundVar name ->
            Err
                Nothing
                ("The variable" <+> pretty name <+> "is unbound")
                (mkNotes [(getLoc name, M.This "")])
                []

-- | run a state action without changing the `Scope` part of the state
scoped :: EnvEffs es => Eff (Declare : es) a -> Eff es a
scoped action' =
    runDeclare action' & \action -> do
        prevScope <- get @Scope
        output <- action
        put prevScope
        pure output

-- todo: handle duplicate names (those that aren't just shadowing)
runDeclare :: EnvEffs es => Eff (Declare : es) a -> Eff es a
runDeclare = interpret \_ -> \case
    -- each wildcard gets a unique id
    Declare w@(Located _ Wildcard'{}) -> freshName w
    Declare name@(Located _ name_) -> do
        scope <- get @Scope
        disambiguatedName <- freshName name
        case Map.lookup name_ scope.table of
            Just oldName -> warn (Shadowing name $ getLoc oldName)
            Nothing -> pass
        put $ Scope $ Map.insert name_ disambiguatedName scope.table
        pure disambiguatedName

type EnvEffs es = (State Scope :> es, NameGen :> es, Diagnose :> es)

-- | looks up a name in the current scope
resolve :: EnvEffs es => SimpleName -> Eff es Name
resolve name@(Located loc name_) = do
    scope <- get @Scope
    case scope.table & Map.lookup name_ of
        Just (Located _ id') -> pure $ Located loc id'
        Nothing -> do
            error (UnboundVar name)
            -- this gives a unique id to every occurance of the same unbound name
            scoped $ declare name

runNameResolution
    :: (NameGen :> es, Diagnose :> es) => HashMap SimpleName_ Name -> Eff (Declare : State Scope : es) a -> Eff es a
runNameResolution env = evalState (Scope env) . runDeclare

resolveNames :: (EnvEffs es, Declare :> es) => [Declaration 'Parse] -> Eff es [Declaration 'NameRes]
resolveNames decls = do
    mkGlobalScope
    let (valueDecls, rest) = partition isValueDecl decls
    valueDecls' <- traverse resolveDec rest
    otherDecls <- traverse resolveDec valueDecls
    pure $ valueDecls' <> otherDecls
  where
    -- this is going to handle imports at some point
    mkGlobalScope :: (EnvEffs es, Declare :> es) => Eff es ()
    mkGlobalScope = collectNames decls

    isValueDecl D.Value{} = True
    isValueDecl _ = False

{- | adds declarations to the current scope
this function should be used very carefully, since it will
generate different IDs when called twice on the same data
-}
collectNames :: (EnvEffs es, Declare :> es) => [Declaration 'Parse] -> Eff es ()
collectNames decls = for_ decls \case
    D.Value _ (E.FunctionBinding name _ _) _ -> void $ declare name
    D.Value _ (E.ValueBinding pat _) _ -> void $ declarePat pat
    D.Type _ name _ _ -> void $ declare name
    D.Signature{} -> pass
    D.Fixity{} -> pass

-- | resolves names in a declaration. Adds type constructors to the current scope
resolveDec :: EnvEffs es => Declaration 'Parse -> Eff es (Declaration 'NameRes)
resolveDec decl = case decl of
    D.Value loc binding locals -> scoped do
        binding' <- resolveBinding locals binding
        locals' <- traverse resolveDec locals
        pure $ D.Value loc binding' locals'
    D.Type loc name vars constrs -> do
        (name', vars', constrsToDeclare) <- scoped do
            name' <- resolve name
            vars' <- traverse declare vars
            constrsToDeclare <-
                constrs & traverse \(D.Constructor conLoc con args) -> do
                    con' <- declare con
                    args' <- traverse resolveType args
                    pure (con, D.Constructor conLoc con' args')
            pure (name', vars', constrsToDeclare)
        -- this is a bit of a crutch, since we want name' and vars' to be scoped and constrs to be global
        -- NAMESPACES: constrs should be declared in a corresponding type namespace
        for_ constrsToDeclare \(Located _ name_, D.Constructor _ conName _) ->
            modify \(Scope table) -> Scope (Map.insert name_ conName table)
        pure $ D.Type loc name' vars' (snd <$> constrsToDeclare)
    D.Signature loc name ty -> D.Signature loc <$> resolve name <*> resolveType ty
    D.Fixity loc fixity name rels -> D.Fixity loc fixity <$> resolve name <*> traverse resolve rels

{- | resolves names in a binding. Unlike the rest of the functions, it also
takes local definitions as an argument, and uses them after resolving the name / pattern
-}
resolveBinding :: EnvEffs es => [Declaration 'Parse] -> Binding 'Parse -> Eff es (Binding 'NameRes)
resolveBinding locals =
    scoped . \case
        E.FunctionBinding name args body -> do
            name' <- resolve name
            args' <- traverse declarePat args
            collectNames locals
            body' <- resolveExpr body
            pure $ E.FunctionBinding name' args' body'
        E.ValueBinding pat body -> do
            pat' <- resolvePat pat
            collectNames locals
            body' <- resolveExpr body
            pure $ E.ValueBinding pat' body'

-- resolves / declares names in a binding. The intended use case is let bindings
declareBinding :: (EnvEffs es, Declare :> es) => Binding 'Parse -> Eff es (Binding 'NameRes)
declareBinding = \case
    E.FunctionBinding name args body -> do
        name' <- declare name
        scoped do
            args' <- traverse declarePat args
            body' <- resolveExpr body
            pure $ E.FunctionBinding name' args' body'
    E.ValueBinding pat body -> do
        pat' <- declarePat pat
        body' <- resolveExpr body
        pure $ E.ValueBinding pat' body'

-- this could have been a Traversable instance
-- resolves names in a pattern, assuming that all new bindings have already been declared
resolvePat :: EnvEffs es => Pattern 'Parse -> Eff es (Pattern 'NameRes)
resolvePat = \case
    P.Constructor con pats -> P.Constructor <$> resolve con <*> traverse resolvePat pats
    P.Annotation pat ty -> P.Annotation <$> resolvePat pat <*> resolveType ty
    P.Record loc row -> P.Record loc <$> traverse resolvePat row
    P.Variant openName arg -> P.Variant openName <$> resolvePat arg
    P.Var name -> P.Var <$> resolve name
    P.List loc pats -> P.List loc <$> traverse resolvePat pats
    P.Wildcard loc name -> pure $ P.Wildcard loc name
    P.Literal lit -> pure $ P.Literal lit

-- | resolves names in a pattern. Adds all new names to the current scope
declarePat :: (EnvEffs es, Declare :> es) => Pattern 'Parse -> Eff es (Pattern 'NameRes)
declarePat = \case
    P.Constructor con pats -> P.Constructor <$> resolve con <*> traverse declarePat pats
    P.Annotation pat ty -> P.Annotation <$> declarePat pat <*> resolveType ty
    P.Record loc row -> P.Record loc <$> traverse declarePat row
    P.Variant openName arg -> P.Variant openName <$> declarePat arg
    P.Var name -> P.Var <$> declare name
    P.List loc pats -> P.List loc <$> traverse declarePat pats
    P.Wildcard loc name -> pure $ P.Wildcard loc name
    P.Literal lit -> pure $ P.Literal lit

{- | resolves names in an expression. Doesn't change the current scope

same story here. Most of the expressions use names, but a couple define them
-}
resolveExpr :: EnvEffs es => Expression 'Parse -> Eff es (Expression 'NameRes)
resolveExpr e = scoped case e of
    E.Lambda loc arg body -> do
        arg' <- declarePat arg
        body' <- resolveExpr body
        pure $ E.Lambda loc arg' body'
    E.WildcardLambda loc args body -> do
        args' <- traverse declare args
        body' <- resolveExpr body
        pure $ E.WildcardLambda loc args' body'
    E.Application f arg -> E.Application <$> resolveExpr f <*> resolveExpr arg
    E.Let loc binding expr -> do
        binding' <- declareBinding binding
        expr' <- resolveExpr expr
        pure $ E.Let loc binding' expr'
    E.LetRec loc bindings expr -> do
        collectNames $ map (\b -> D.Value loc b []) $ NE.toList bindings
        bindings' <- traverse (resolveBinding []) bindings
        expr' <- resolveExpr expr
        pure $ E.LetRec loc bindings' expr'
    E.Case loc arg matches ->
        E.Case loc <$> resolveExpr arg <*> for matches \(pat, expr) -> scoped do
            pat' <- declarePat pat
            expr' <- resolveExpr expr
            pure (pat', expr')
    E.Match loc matches ->
        E.Match loc <$> for matches \(pats, expr) -> scoped do
            pats' <- traverse declarePat pats
            expr' <- resolveExpr expr
            pure (pats', expr')
    E.Annotation body ty -> E.Annotation <$> resolveExpr body <*> resolveType ty
    E.If loc cond true false -> E.If loc <$> resolveExpr cond <*> resolveExpr true <*> resolveExpr false
    E.Record loc row -> E.Record loc <$> traverse resolveExpr row
    E.List loc items -> E.List loc <$> traverse resolveExpr items
    E.Do loc stmts lastAction -> E.Do loc <$> traverse resolveStmt stmts <*> resolveExpr lastAction
    E.Infix pairs last' ->
        E.Infix
            <$> traverse (bitraverse resolveExpr (traverse resolve)) pairs
            <*> resolveExpr last'
    E.Name name -> E.Name <$> resolve name
    E.Constructor name -> E.Constructor <$> resolve name
    E.RecordLens loc lens -> pure $ E.RecordLens loc lens
    E.Variant openName -> pure $ E.Variant openName
    E.Literal lit -> pure $ E.Literal lit

resolveStmt :: (EnvEffs es, Declare :> es) => DoStatement 'Parse -> Eff es (DoStatement 'NameRes)
resolveStmt = \case
    E.Bind pat body -> do
        body' <- resolveExpr body
        pat' <- declarePat pat
        pure $ E.Bind pat' body'
    E.With loc pat body -> do
        body' <- resolveExpr body
        pat' <- declarePat pat
        pure $ E.With loc pat' body'
    E.DoLet loc binding -> E.DoLet loc <$> declareBinding binding
    E.Action expr -> E.Action <$> resolveExpr expr

-- | resolves names in a type. Doesn't change the current scope
resolveType :: EnvEffs es => Type' 'Parse -> Eff es (Type' 'NameRes)
resolveType ty = scoped case ty of
    T.Forall loc var body -> do
        var' <- declare var
        body' <- resolveType body
        pure $ T.Forall loc var' body'
    T.Exists loc var body -> do
        var' <- declare var
        body' <- resolveType body
        pure $ T.Exists loc var' body'
    T.Application lhs rhs -> T.Application <$> resolveType lhs <*> resolveType rhs
    T.Function loc from to -> T.Function loc <$> resolveType from <*> resolveType to
    T.Name name -> T.Name <$> resolve name
    T.Var var -> T.Var <$> resolve var
    T.Variant loc row -> T.Variant loc <$> traverse resolveType row
    T.Record loc row -> T.Record loc <$> traverse resolveType row
