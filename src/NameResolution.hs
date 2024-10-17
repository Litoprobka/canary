{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module NameResolution (runNameResolution, runScopeErrors, runDeclare, resolveNames, resolveExpr, resolveType, resolve, declare, declarePat, Scope(..), UnboundVar (..), Warning (..), ScopeErrors (..)) where

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
import Effectful.Dispatch.Dynamic (reinterpret, interpret)
import qualified Data.Sequence as Seq
import Data.List (partition)


data ScopeErrors = ScopeErrors {errors :: Seq UnboundVar, warnings :: Seq Warning}

-- | a writer-like effect for scope warnings and errors
data ScopeErrorE :: Effect where
    Warn :: Warning -> ScopeErrorE m ()
    Error :: UnboundVar -> ScopeErrorE m ()

-- | a one-off effect to differentiate functions that do and don't declare stuff
-- | on type level
data Declare :: Effect where
    Declare :: Text -> Declare m Name

-- * other types

newtype Scope = Scope {table :: HashMap Text Name}

newtype UnboundVar = UnboundVar Text deriving (Show)
data Warning = Shadowing Text | UnusedVar Text deriving (Show)

makeEffect ''ScopeErrorE
makeEffect ''Declare

runScopeErrors :: Eff (ScopeErrorE : es) a -> Eff es (a, ScopeErrors)
runScopeErrors = reinterpret (runState $ ScopeErrors Seq.empty Seq.empty) \_ -> \case
    Warn warning -> modify @ScopeErrors \se -> se{warnings = se.warnings Seq.|> warning}
    Error error' -> modify @ScopeErrors \se -> se{errors = se.errors Seq.|> error'}

-- | run a state action without changing the `Scope` part of the state
scoped :: EnvEffs es => Eff (Declare : es) a -> Eff es a
scoped action' = runDeclare action' & \action -> do
    prevScope <- get @Scope
    output <- action
    put prevScope
    pure output

-- todo: handle duplicate names (those that aren't just shadowing)
runDeclare :: EnvEffs es => Eff (Declare : es) a -> Eff es a
runDeclare = interpret \_ -> \case
    -- each wildcard gets a unique id
    Declare "_" -> freshName "_"
    Declare name -> do
        scope <- get @Scope
        disambiguatedName <- freshName name
        case Map.lookup name scope.table of
            Just _ -> warn (Shadowing name)
            Nothing -> pass
        put $ Scope $ Map.insert name disambiguatedName scope.table
        pure disambiguatedName

type EnvEffs es = (State Scope :> es, NameGen :> es, ScopeErrorE :> es)   

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

runNameResolution :: (NameGen :> es) => HashMap Text Name -> Eff (Declare : State Scope : ScopeErrorE : es) a -> Eff es (a, ScopeErrors)
runNameResolution env = runScopeErrors . evalState (Scope env) . runDeclare

resolveNames :: (EnvEffs es,  Declare :> es) => [Declaration Text] -> Eff es [Declaration Name]
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
collectNames :: (EnvEffs es, Declare :> es) => [Declaration Text] -> Eff es ()
collectNames decls = for_ decls \case
    D.Value _ (E.FunctionBinding _ name _ _) _ -> void $ declare name
    D.Value _ (E.ValueBinding _ pat _) _ -> void $ declarePat pat
    D.Type _ name _ _ -> void $ declare name
    D.Alias _ name _ -> void $ declare name
    D.Signature{} -> pass

-- | resolves names in a declaration. Adds type constructors to the current scope
resolveDec :: EnvEffs es => Declaration Text -> Eff es (Declaration Name)
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
        for_ constrsToDeclare \(textName, D.Constructor _ conName _) -> modify \(Scope table) -> Scope (Map.insert textName conName table)
        pure $ D.Type loc name' vars' (snd <$> constrsToDeclare)
    D.Alias loc alias body -> D.Alias loc <$> resolve alias <*> resolveType body
    D.Signature loc name ty -> D.Signature loc <$> resolve name <*> resolveType ty

{- | resolves names in a binding. Unlike the rest of the functions, it also
takes local definitions as an argument, and uses them after resolving the name / pattern
-}
resolveBinding :: EnvEffs es => [Declaration Text] -> Binding Text -> Eff es (Binding Name)
resolveBinding locals = scoped . \case
    E.FunctionBinding loc name args body -> do
        name' <- resolve name
        args' <- traverse declarePat args
        collectNames locals
        body' <- resolveExpr body
        pure $ E.FunctionBinding loc name' args' body'
    E.ValueBinding loc pat body -> do
        pat' <- traverse resolve pat -- `traverse` finally works
        collectNames locals
        body' <- resolveExpr body
        pure $ E.ValueBinding loc pat' body'

{- | resolves names in a pattern. Adds all new names to the current scope
-}
declarePat :: (EnvEffs es, Declare :> es) => Pattern Text -> Eff es (Pattern Name)
declarePat = \case
    P.Constructor loc con pats -> P.Constructor loc <$> resolve con <*> traverse declarePat pats
    P.Annotation loc pat ty -> P.Annotation loc <$> declarePat pat <*> resolveType ty
    P.Record loc row -> P.Record loc <$> traverse declarePat row
    P.Variant loc openName arg -> P.Variant loc openName <$> declarePat arg
    P.Var loc name -> P.Var loc <$> declare name
    P.List loc pats -> P.List loc <$> traverse declarePat pats
    P.IntLiteral loc n -> pure $ P.IntLiteral loc n
    P.TextLiteral loc txt -> pure $ P.TextLiteral loc txt
    P.CharLiteral loc c -> pure $ P.CharLiteral loc c

{- | resolves names in an expression. Doesn't change the current scope

same story here. Most of the expressions use names, but a couple define them
-}
resolveExpr :: EnvEffs es => Expression Text -> Eff es (Expression Name)
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
    E.Name loc name -> E.Name loc <$> resolve name
    E.Constructor loc name -> E.Constructor loc <$> resolve name
    E.RecordLens loc lens -> pure $ E.RecordLens loc lens
    E.Variant loc openName -> pure $ E.Variant loc openName
    E.IntLiteral loc n -> pure $ E.IntLiteral loc n
    E.TextLiteral loc txt -> pure $ E.TextLiteral loc txt
    E.CharLiteral loc c -> pure $ E.CharLiteral loc c

-- | resolves names in a type. Doesn't change the current scope
resolveType :: EnvEffs es => Type' Text -> Eff es (Type' Name)
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
    T.Name loc name -> T.Name loc <$> resolve name
    T.Var loc var -> T.Var loc <$> resolve var
    T.UniVar loc uni -> pure $ T.UniVar loc uni
    T.Skolem loc skolem -> pure $ T.Skolem loc skolem
    T.Variant loc row -> T.Variant loc <$> traverse resolveType row
    T.Record loc row -> T.Record loc <$> traverse resolveType row
