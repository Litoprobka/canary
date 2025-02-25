{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}

module NameResolution (
    run,
    runDeclare,
    resolveNames,
    resolveTerm,
    resolve,
    declare,
    declarePat,
    Scope (..),
    Declare,
    runWithEnv,
) where

import Common (Name)
import Common hiding (Name, Scope)
import Data.HashMap.Strict qualified as Map
import Data.List (partition)
import Data.List.NonEmpty qualified as NE
import Data.Traversable (for)
import Diagnostic
import Effectful.Dispatch.Dynamic (interpret)
import Effectful.State.Static.Local (State, evalState, get, put, runState)
import Error.Diagnose (Report (..))
import Error.Diagnose qualified as M
import LangPrelude hiding (error)
import NameGen
import Syntax
import Syntax.Declaration qualified as D
import Syntax.Term

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
scoped :: NameResCtx es => Eff (Declare : es) a -> Eff es a
scoped action' =
    runDeclare action' & \action -> do
        prevScope <- get @Scope
        output <- action
        put prevScope
        pure output

-- todo: handle duplicate names (those that aren't just shadowing)
runDeclare :: NameResCtx es => Eff (Declare : es) a -> Eff es a
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

type NameResCtx es = (State Scope :> es, NameGen :> es, Diagnose :> es)

{- | looks up a name in the current scope
if the name is unbound, gives it a new unique id and
emits an UnboundVar error
-}
resolve :: NameResCtx es => SimpleName -> Eff es Name
resolve name@(Located loc name_) = do
    scope <- get @Scope
    case scope.table & Map.lookup name_ of
        Just (Located _ id') -> pure $ Located loc id'
        Nothing -> do
            error (UnboundVar name)
            -- this gives a unique id to every occurance of the same unbound name
            scoped $ declare name

runWithEnv :: (NameGen :> es, Diagnose :> es) => Scope -> Eff (Declare : State Scope : es) a -> Eff es (a, Scope)
runWithEnv env = runState env . runDeclare

run :: (NameGen :> es, Diagnose :> es) => Scope -> Eff (Declare : State Scope : es) a -> Eff es a
run env = evalState env . runDeclare

resolveNames :: (NameResCtx es, Declare :> es) => [Declaration 'Parse] -> Eff es [Declaration 'NameRes]
resolveNames decls = do
    mkGlobalScope
    let (valueDecls, rest) = partition isValueDecl decls
    valueDecls' <- traverse resolveDec rest
    otherDecls <- traverse resolveDec valueDecls
    pure $ valueDecls' <> otherDecls
  where
    -- this is going to handle imports at some point
    mkGlobalScope :: (NameResCtx es, Declare :> es) => Eff es ()
    mkGlobalScope = collectNames decls

    isValueDecl D.Value{} = True
    isValueDecl _ = False

{- | adds declarations to the current scope
this function should be used very carefully, since it will
generate different IDs when called twice on the same data
-}
collectNames :: (NameResCtx es, Declare :> es) => [Declaration 'Parse] -> Eff es ()
collectNames decls = for_ decls \case
    D.Value _ (FunctionB name _ _) _ -> void $ declare name
    D.Value _ (ValueB pat _) _ -> void $ declarePat pat
    D.Type _ name _ _ -> void $ declare name
    D.GADT _ name _ _ -> void $ declare name
    D.Signature{} -> pass
    D.Fixity{} -> pass

-- | resolves names in a declaration. Adds type constructors to the current scope
resolveDec :: (NameResCtx es, Declare :> es) => Declaration 'Parse -> Eff es (Declaration 'NameRes)
resolveDec decl = case decl of
    D.Value loc binding locals -> scoped do
        binding' <- resolveBinding locals binding
        locals' <- traverse resolveDec locals
        pure $ D.Value loc binding' locals'
    D.Type loc name vars constrs -> do
        -- TODO: NAMESPACES: constrs should be declared in a corresponding type namespace
        name' <- resolve name
        for_ constrs \con -> declare con.name
        scoped do
            vars' <- traverse resolveBinder vars
            constrs' <- for constrs \(D.Constructor conLoc con args) -> do
                con' <- resolve con
                args' <- traverse resolveTerm args
                pure $ D.Constructor conLoc con' args'
            pure $ D.Type loc name' vars' constrs'
    D.GADT loc name mbKind constrs -> do
        name' <- resolve name
        mbKind' <- traverse resolveTerm mbKind
        constrs' <- for constrs \(D.GadtConstructor conLoc con sig) -> do
            con' <- declare con
            sig' <- resolveTerm sig
            pure $ D.GadtConstructor conLoc con' sig'
        pure $ D.GADT loc name' mbKind' constrs'
    D.Signature loc name ty -> D.Signature loc <$> resolve name <*> resolveTerm ty
    D.Fixity loc fixity name rels -> D.Fixity loc fixity <$> resolve name <*> traverse resolve rels

{- | resolves names in a binding. Unlike the rest of the functions, it also
takes local definitions as an argument, and uses them after resolving the name / pattern
-}
resolveBinding :: NameResCtx es => [Declaration 'Parse] -> Binding 'Parse -> Eff es (Binding 'NameRes)
resolveBinding locals =
    scoped . \case
        FunctionB name args body -> do
            name' <- resolve name
            args' <- traverse declarePat args
            collectNames locals
            body' <- resolveTerm body
            pure $ FunctionB name' args' body'
        ValueB pat body -> do
            pat' <- resolvePat pat
            collectNames locals
            body' <- resolveTerm body
            pure $ ValueB pat' body'

-- resolves / declares names in a binding. The intended use case is let bindings
declareBinding :: (NameResCtx es, Declare :> es) => Binding 'Parse -> Eff es (Binding 'NameRes)
declareBinding = \case
    FunctionB name args body -> do
        name' <- declare name
        scoped do
            args' <- traverse declarePat args
            body' <- resolveTerm body
            pure $ FunctionB name' args' body'
    ValueB pat body -> do
        pat' <- declarePat pat
        body' <- resolveTerm body
        pure $ ValueB pat' body'

-- this could have been a Traversable instance
-- resolves names in a pattern, assuming that all new bindings have already been declared
resolvePat :: NameResCtx es => Pattern 'Parse -> Eff es (Pattern 'NameRes)
resolvePat = \case
    ConstructorP con pats -> ConstructorP <$> resolve con <*> traverse resolvePat pats
    AnnotationP pat ty -> AnnotationP <$> resolvePat pat <*> resolveTerm ty
    RecordP loc row -> RecordP loc <$> traverse resolvePat row
    VariantP openName arg -> VariantP openName <$> resolvePat arg
    VarP name -> VarP <$> resolve name
    ListP loc pats -> ListP loc <$> traverse resolvePat pats
    WildcardP loc name -> pure $ WildcardP loc name
    LiteralP lit -> pure $ LiteralP lit

-- | resolves names in a pattern. Adds all new names to the current scope
declarePat :: (NameResCtx es, Declare :> es) => Pattern 'Parse -> Eff es (Pattern 'NameRes)
declarePat = \case
    ConstructorP con pats -> ConstructorP <$> resolve con <*> traverse declarePat pats
    AnnotationP pat ty -> AnnotationP <$> declarePat pat <*> resolveTerm ty
    RecordP loc row -> RecordP loc <$> traverse declarePat row
    VariantP openName arg -> VariantP openName <$> declarePat arg
    VarP name -> VarP <$> declare name
    ListP loc pats -> ListP loc <$> traverse declarePat pats
    WildcardP loc name -> pure $ WildcardP loc name
    LiteralP lit -> pure $ LiteralP lit

-- | resolves names in a term. Doesn't change the current scope
resolveTerm :: NameResCtx es => Term 'Parse -> Eff es (Term 'NameRes)
resolveTerm e = scoped case e of
    Lambda loc arg body -> do
        arg' <- declarePat arg
        body' <- resolveTerm body
        pure $ Lambda loc arg' body'
    WildcardLambda loc args body -> do
        args' <- traverse declare args
        body' <- resolveTerm body
        pure $ WildcardLambda loc args' body'
    App f arg -> App <$> resolveTerm f <*> resolveTerm arg
    TypeApp expr tyArg -> TypeApp <$> resolveTerm expr <*> resolveTerm tyArg
    Let loc binding expr -> do
        binding' <- declareBinding binding
        expr' <- resolveTerm expr
        pure $ Let loc binding' expr'
    LetRec loc bindings expr -> do
        collectNames $ map (\b -> D.Value loc b []) $ NE.toList bindings
        bindings' <- traverse (resolveBinding []) bindings
        expr' <- resolveTerm expr
        pure $ LetRec loc bindings' expr'
    Case loc arg matches ->
        Case loc <$> resolveTerm arg <*> for matches \(pat, expr) -> scoped do
            pat' <- declarePat pat
            expr' <- resolveTerm expr
            pure (pat', expr')
    Match loc matches ->
        Match loc <$> for matches \(pats, expr) -> scoped do
            pats' <- traverse declarePat pats
            expr' <- resolveTerm expr
            pure (pats', expr')
    Annotation body ty -> Annotation <$> resolveTerm body <*> resolveTerm ty
    If loc cond true false -> If loc <$> resolveTerm cond <*> resolveTerm true <*> resolveTerm false
    Record loc row -> Record loc <$> traverse resolveTerm row
    List loc items -> List loc <$> traverse resolveTerm items
    Do loc stmts lastAction -> Do loc <$> traverse resolveStmt stmts <*> resolveTerm lastAction
    InfixE pairs last' ->
        InfixE
            <$> traverse (bitraverse resolveTerm (traverse resolve)) pairs
            <*> resolveTerm last'
    Name name -> Name <$> resolve name
    RecordLens loc lens -> pure $ RecordLens loc lens
    Variant openName -> pure $ Variant openName
    Literal lit -> pure $ Literal lit
    Forall loc binder body -> do
        var' <- resolveBinder binder
        body' <- resolveTerm body
        pure $ Forall loc var' body'
    Exists loc binder body -> do
        var' <- resolveBinder binder
        body' <- resolveTerm body
        pure $ Exists loc var' body'
    Function loc from to -> Function loc <$> resolveTerm from <*> resolveTerm to
    ImplicitVar var -> internalError (getLoc var) "inference for implicit vars is not implemented yet"
    Parens expr -> resolveTerm expr -- todo: construct implicit lambdas here
    VariantT loc row -> VariantT loc <$> traverse resolveTerm row
    RecordT loc row -> RecordT loc <$> traverse resolveTerm row

resolveStmt :: (NameResCtx es, Declare :> es) => DoStatement 'Parse -> Eff es (DoStatement 'NameRes)
resolveStmt = \case
    Bind pat body -> do
        body' <- resolveTerm body
        pat' <- declarePat pat
        pure $ Bind pat' body'
    With loc pat body -> do
        body' <- resolveTerm body
        pat' <- declarePat pat
        pure $ With loc pat' body'
    DoLet loc binding -> DoLet loc <$> declareBinding binding
    Action expr -> Action <$> resolveTerm expr

{- | declares the var in a binder; resolves names in its kind annotation, if any
the kind annotation may not reference the var
-}
resolveBinder :: (NameResCtx es, Declare :> es) => VarBinder 'Parse -> Eff es (VarBinder 'NameRes)
resolveBinder (VarBinder var k) = do
    k' <- traverse resolveTerm k
    var' <- declare var
    pure $ VarBinder var' k'
