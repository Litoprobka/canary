{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}

module NameResolution (
    runNameResolution,
    runScopeErrors,
    runDeclare,
    resolveNames,
    resolveExpr,
    resolveType,
    resolve,
    declare,
    declarePat,
    Scope (..),
    UnboundVar (..),
    Warning (..),
    ScopeErrors (..),
) where

import Relude hiding (State, error, evalState, get, modify, put, runState)

import Common hiding (Scope)
import Data.HashMap.Strict qualified as Map
import Data.List (partition)
import Data.Sequence qualified as Seq
import Data.Traversable (for)
import Effectful (Eff, Effect, (:>))
import Effectful.Dispatch.Dynamic (interpret, reinterpret)
import Effectful.State.Static.Local (State, evalState, get, modify, put, runState)
import Effectful.TH (makeEffect)
import NameGen
import Syntax
import Syntax.Declaration qualified as D
import Syntax.Expression qualified as E
import Syntax.Pattern qualified as P
import Syntax.Type qualified as T

{-
The name resolution pass. Transforms 'Parse AST into 'NameRes AST. It doesn't short-circuit on errors
-}

data ScopeErrors = ScopeErrors {errors :: Seq UnboundVar, warnings :: Seq Warning}

-- | a writer-like effect for scope warnings and errors
data ScopeErrorE :: Effect where
    Warn :: Warning -> ScopeErrorE m ()
    Error :: UnboundVar -> ScopeErrorE m ()

{- | a one-off effect to differentiate functions that do and don't declare stuff
| on type level
-}
data Declare :: Effect where
    Declare :: SimpleName -> Declare m Name

-- * other types

newtype Scope = Scope {table :: HashMap Text Name}

newtype UnboundVar = UnboundVar SimpleName deriving (Show)
data Warning = Shadowing SimpleName | UnusedVar SimpleName deriving (Show)

makeEffect ''ScopeErrorE
makeEffect ''Declare

runScopeErrors :: Eff (ScopeErrorE : es) a -> Eff es (a, ScopeErrors)
runScopeErrors = reinterpret (runState $ ScopeErrors Seq.empty Seq.empty) \_ -> \case
    Warn warning -> modify @ScopeErrors \se -> se{warnings = se.warnings Seq.|> warning}
    Error error' -> modify @ScopeErrors \se -> se{errors = se.errors Seq.|> error'}

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
    Declare (SimpleName loc "_") -> freshName loc "_"
    Declare name -> do
        scope <- get @Scope
        disambiguatedName <- freshName name.loc name.name
        case Map.lookup name.name scope.table of
            Just _ -> warn (Shadowing name)
            Nothing -> pass
        put $ Scope $ Map.insert name.name disambiguatedName scope.table
        pure disambiguatedName

type EnvEffs es = (State Scope :> es, NameGen :> es, ScopeErrorE :> es)

-- | looks up a name in the current scope
resolve :: EnvEffs es => SimpleName -> Eff es Name
resolve name = do
    scope <- get @Scope
    case scope.table & Map.lookup name.name of
        Just id' -> pure id'
        Nothing -> do
            error (UnboundVar name)
            -- this gives a unique id to every occurance of the same unbound name
            scoped $ declare name

runNameResolution
    :: NameGen :> es => HashMap Text Name -> Eff (Declare : State Scope : ScopeErrorE : es) a -> Eff es (a, ScopeErrors)
runNameResolution env = runScopeErrors . evalState (Scope env) . runDeclare

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
    D.Value _ (E.FunctionBinding _ name _ _) _ -> void $ declare name
    D.Value _ (E.ValueBinding _ pat _) _ -> void $ declarePat pat
    D.Type _ name _ _ -> void $ declare name
    D.Alias _ name _ -> void $ declare name
    D.Signature{} -> pass

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
        for_ constrsToDeclare \(textName, D.Constructor _ conName _) -> modify \(Scope table) -> Scope (Map.insert textName.name conName table)
        pure $ D.Type loc name' vars' (snd <$> constrsToDeclare)
    D.Alias loc alias body -> D.Alias loc <$> resolve alias <*> resolveType body
    D.Signature loc name ty -> D.Signature loc <$> resolve name <*> resolveType ty

{- | resolves names in a binding. Unlike the rest of the functions, it also
takes local definitions as an argument, and uses them after resolving the name / pattern
-}
resolveBinding :: EnvEffs es => [Declaration 'Parse] -> Binding 'Parse -> Eff es (Binding 'NameRes)
resolveBinding locals =
    scoped . \case
        E.FunctionBinding loc name args body -> do
            name' <- resolve name
            args' <- traverse declarePat args
            collectNames locals
            body' <- resolveExpr body
            pure $ E.FunctionBinding loc name' args' body'
        E.ValueBinding loc pat body -> do
            pat' <- resolvePat pat
            collectNames locals
            body' <- resolveExpr body
            pure $ E.ValueBinding loc pat' body'
  where
    -- this could have been a Traversable instance
    resolvePat :: EnvEffs es => Pattern 'Parse -> Eff es (Pattern 'NameRes)
    resolvePat = \case
        P.Constructor loc con pats -> P.Constructor loc <$> resolve con <*> traverse resolvePat pats
        P.Annotation loc pat ty -> P.Annotation loc <$> resolvePat pat <*> resolveType ty
        P.Record loc row -> P.Record loc <$> traverse resolvePat row
        P.Variant loc openName arg -> P.Variant loc openName <$> resolvePat arg
        P.Var name -> P.Var <$> resolve name
        P.List loc pats -> P.List loc <$> traverse resolvePat pats
        P.IntLiteral loc n -> pure $ P.IntLiteral loc n
        P.TextLiteral loc txt -> pure $ P.TextLiteral loc txt
        P.CharLiteral loc c -> pure $ P.CharLiteral loc c

-- | resolves names in a pattern. Adds all new names to the current scope
declarePat :: (EnvEffs es, Declare :> es) => Pattern 'Parse -> Eff es (Pattern 'NameRes)
declarePat = \case
    P.Constructor loc con pats -> P.Constructor loc <$> resolve con <*> traverse declarePat pats
    P.Annotation loc pat ty -> P.Annotation loc <$> declarePat pat <*> resolveType ty
    P.Record loc row -> P.Record loc <$> traverse declarePat row
    P.Variant loc openName arg -> P.Variant loc openName <$> declarePat arg
    P.Var name -> P.Var <$> declare name
    P.List loc pats -> P.List loc <$> traverse declarePat pats
    P.IntLiteral loc n -> pure $ P.IntLiteral loc n
    P.TextLiteral loc txt -> pure $ P.TextLiteral loc txt
    P.CharLiteral loc c -> pure $ P.CharLiteral loc c

{- | resolves names in an expression. Doesn't change the current scope

same story here. Most of the expressions use names, but a couple define them
-}
resolveExpr :: EnvEffs es => Expression 'Parse -> Eff es (Expression 'NameRes)
resolveExpr e = scoped case e of
    E.Lambda loc arg body -> do
        arg' <- declarePat arg
        body' <- resolveExpr body
        pure $ E.Lambda loc arg' body'
    E.Application loc f arg -> E.Application loc <$> resolveExpr f <*> resolveExpr arg
    E.Let loc binding expr -> do
        -- resolveBinding is intended for top-level bindings and where clauses,
        -- so we have to declare the new vars with `collectNames`
        --
        -- yes, this is hacky
        collectNames [D.Value loc binding []] -- should we use `loc` from `binding` here?
        binding' <- resolveBinding [] binding
        expr' <- resolveExpr expr
        pure $ E.Let loc binding' expr'
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
    E.Annotation loc body ty -> E.Annotation loc <$> resolveExpr body <*> resolveType ty
    E.If loc cond true false -> E.If loc <$> resolveExpr cond <*> resolveExpr true <*> resolveExpr false
    E.Record loc row -> E.Record loc <$> traverse resolveExpr row
    E.List loc items -> E.List loc <$> traverse resolveExpr items
    E.Infix E.Yes pairs last' ->
        E.Infix E.Yup
            <$> traverse (bitraverse resolveExpr resolve) pairs
            <*> resolveExpr last'
    E.Name name -> E.Name <$> resolve name
    E.Constructor name -> E.Constructor <$> resolve name
    E.RecordLens loc lens -> pure $ E.RecordLens loc lens
    E.Variant openName -> pure $ E.Variant openName
    E.IntLiteral loc n -> pure $ E.IntLiteral loc n
    E.TextLiteral loc txt -> pure $ E.TextLiteral loc txt
    E.CharLiteral loc c -> pure $ E.CharLiteral loc c

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
    T.Application loc lhs rhs -> T.Application loc <$> resolveType lhs <*> resolveType rhs
    T.Function loc from to -> T.Function loc <$> resolveType from <*> resolveType to
    T.Name name -> T.Name <$> resolve name
    T.Var var -> T.Var <$> resolve var
    T.Variant loc row -> T.Variant loc <$> traverse resolveType row
    T.Record loc row -> T.Record loc <$> traverse resolveType row
