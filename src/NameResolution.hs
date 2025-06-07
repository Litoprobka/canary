{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE PatternSynonyms #-}
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
    ImplicitVars,
    runWithEnv,
) where

import Common (Name)
import Common hiding (Name, Scope)
import Data.DList (DList)
import Data.DList qualified as DList
import Data.HashMap.Strict qualified as Map
import Data.List (partition)
import Data.List qualified as List
import Data.List.NonEmpty qualified as NE
import Data.Traversable (for)
import Diagnostic
import Effectful.Dispatch.Dynamic (interpret)
import Effectful.State.Static.Local (State, evalState, get, modify, put, runState, state)
import Error.Diagnose (Report (..))
import Error.Diagnose qualified as M
import LangPrelude hiding (error)
import NameGen
import Syntax
import Syntax.AstTraversal
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
data Error = UnboundVar SimpleName | OutOfScopeWildcard SimpleName | OutOfScopeImplicit SimpleName

warn :: Diagnose :> es => Warning -> Eff es ()
warn =
    nonFatal . \case
        Shadowing name loc ->
            Warn
                Nothing
                ("The binding" <+> prettyDef name <+> "shadows an earlier binding")
                (mkNotes [(getLoc name, M.This "new binding"), (loc, M.Where "previously bound at")])
                []
        UnusedVar name ->
            Warn
                Nothing
                ("The binding" <+> prettyDef name <+> "is unused")
                (mkNotes [(getLoc name, M.This "bound at")])
                []

error :: Diagnose :> es => Error -> Eff es ()
error =
    nonFatal . \case
        UnboundVar name ->
            Err
                Nothing
                ("The variable" <+> prettyDef name <+> "is unbound")
                (mkNotes [(getLoc name, M.This "referenced here")])
                []
        OutOfScopeWildcard name ->
            Err
                Nothing
                "Wildcards must be delimited by brackets, parentheses, or braces"
                (mkNotes [(getLoc name, M.This "wildcard is out of scope")])
                []
        OutOfScopeImplicit name ->
            Err
                Nothing
                "implicit variables may only appear in a type"
                (mkNotes [(getLoc name, M.This "variable is outside of a type")])
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
    Declare w@(L Wildcard'{}) -> freshName w
    Declare name@(L name_) -> do
        scope <- get @Scope
        disambiguatedName <- freshName name
        case Map.lookup name_ scope.table of
            Just oldName -> warn (Shadowing name $ getLoc oldName)
            Nothing -> pass
        put $ Scope $ Map.insert name_ disambiguatedName scope.table
        pure disambiguatedName

type NameResCtx es = (State Scope :> es, State [DList Name] :> es, State ImplicitVars :> es, NameGen :> es, Diagnose :> es)

{- | looks up a name in the current scope
if the name is unbound, gives it a new unique id and
emits an UnboundVar error
-}
resolve :: NameResCtx es => SimpleName -> Eff es Name
resolve name@(Located loc name_) = do
    scope <- get @Scope
    case scope.table & Map.lookup name_ of
        Just (L id') -> pure $ Located loc id'
        Nothing -> do
            error (UnboundVar name)
            -- this gives a unique id to every occurence of the same unbound name
            scoped $ declare name

data ImplicitVars
    = NotInTypeScope
    | CollectingVars [(SimpleName, Name)] -- poor man's scope

inferForall :: (State ImplicitVars :> es, Diagnose :> es) => Eff es (Term 'NameRes) -> Eff es (Term 'NameRes)
inferForall mkType =
    get >>= \case
        CollectingVars{} -> mkType
        NotInTypeScope -> do
            put $ CollectingVars []
            body <- mkType
            let loc = getLoc body
            get >>= \case
                NotInTypeScope -> internalError loc "something wrong with implicit forall inference"
                CollectingVars vars -> do
                    put NotInTypeScope
                    pure $ foldr (\(_, var) acc -> Q Forall Implicit Erased VarBinder{var, kind = Nothing} acc :@ loc) body vars

runWithEnv
    :: (NameGen :> es, Diagnose :> es)
    => Scope
    -> Eff (Declare : State ImplicitVars : State [DList Name] : State Scope : es) a
    -> Eff es (a, Scope)
runWithEnv env = runState env . evalState [] . evalState NotInTypeScope . runDeclare

run
    :: (NameGen :> es, Diagnose :> es)
    => Scope
    -> Eff (Declare : State ImplicitVars : State [DList Name] : State Scope : es) a
    -> Eff es a
run env = evalState env . evalState [] . evalState NotInTypeScope . runDeclare

resolveNames :: (NameResCtx es, Declare :> es) => [Declaration 'Parse] -> Eff es [Declaration 'NameRes]
resolveNames decls = do
    mkGlobalScope
    let (valueDecls, rest) = partition isValueDecl decls
    otherDecls <- traverse resolveDec rest
    valueDecls' <- traverse resolveDec valueDecls
    pure $ otherDecls <> valueDecls'
  where
    -- this is going to handle imports at some point
    mkGlobalScope :: (NameResCtx es, Declare :> es) => Eff es ()
    mkGlobalScope = collectNames decls

    isValueDecl (L D.Value{}) = True
    isValueDecl _ = False

{- | adds declarations to the current scope
this function should be used very carefully, since it will
generate different IDs when called twice on the same data
-}
collectNames :: (NameResCtx es, Declare :> es) => [Declaration 'Parse] -> Eff es ()
collectNames decls = for_ decls $ traverse_ \case
    D.Value (FunctionB name _ _) _ -> void $ declare name
    D.Value (ValueB pat _) _ -> void $ declarePat pat
    D.Type name _ _ -> void $ declare name
    D.GADT name _ _ -> void $ declare name
    D.Signature{} -> pass
    D.Fixity{} -> pass

type Traversal es = AstTraversal 'Parse 'NameRes (Eff es)

resolveTrav :: NameResCtx es => Traversal es
resolveTrav =
    tie
        UntiedTraversal
            { term = const resolveTerm
            , pattern_ = defTravPattern
            , declaration = defTravDeclaration
            , name = const resolve
            , -- juggling Declare scopes is complicated
              binder = \_ _ -> internalError' "resolveTrav: binder"
            , binding = \_ _ -> internalError' "resolveTrav: binding"
            , statement = \_ _ -> internalError' "resolveTrav: statement"
            }

-- | resolves names in a declaration. Adds type constructors to the current scope
resolveDec :: (NameResCtx es, Declare :> es) => Declaration 'Parse -> Eff es (Declaration 'NameRes)
resolveDec = traverse \case
    D.Value binding locals -> scoped do
        binding' <- resolveBinding locals binding
        locals' <- traverse resolveDec locals
        pure $ D.Value binding' locals'
    D.Type name vars constrs -> do
        -- TODO: NAMESPACES: constrs should be declared in a corresponding type namespace
        name' <- resolve name
        for_ constrs \con -> declare con.name
        scoped do
            vars' <- traverse resolveBinder vars
            constrs' <- for constrs \(D.Constructor conLoc con args) -> do
                con' <- resolve con
                args' <- traverse resolveTerm args
                pure $ D.Constructor conLoc con' args'
            pure $ D.Type name' vars' constrs'
    D.GADT name mbKind constrs -> do
        name' <- resolve name
        mbKind' <- traverse resolveTerm mbKind
        constrs' <- for constrs \(D.GadtConstructor conLoc con sig) -> do
            con' <- declare con
            sig' <- inferForall (resolveTerm sig)
            pure $ D.GadtConstructor conLoc con' sig'
        pure $ D.GADT name' mbKind' constrs'
    D.Signature name ty -> D.Signature <$> resolve name <*> inferForall (resolveTerm ty)
    D.Fixity fixity name rels -> D.Fixity fixity <$> resolve name <*> traverse resolve rels

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
            pat' <- resolveTrav.pattern_ pat
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

-- | resolves names in a pattern. Adds all new names to the current scope
declarePat :: (NameResCtx es, Declare :> es) => Pattern 'Parse -> Eff es (Pattern 'NameRes)
declarePat (pat' :@ loc) =
    Located loc <$> case pat' of
        VarP name -> VarP <$> declare name
        AnnotationP pat ty -> AnnotationP <$> declarePat pat <*> inferForall (resolveTerm ty)
        other -> unLoc <$> defTravPattern declareTrav (other :@ loc)
  where
    -- we don't have any open recursion cases here, so we only care about
    -- what's directly reachable from Pattern, i.e. other patterns, terms and names
    declareTrav =
        AstTraversal
            { term = resolveTerm
            , pattern_ = declarePat
            , name = resolve
            , declaration = const $ internalError' "declareTrav: declaration"
            , binder = const $ internalError' "resolveTrav: binder"
            , binding = const $ internalError' "resolveTrav: binding"
            , statement = const $ internalError' "resolveTrav: statement"
            }

-- | resolves names in a term. Doesn't change the current scope
resolveTerm :: NameResCtx es => Term 'Parse -> Eff es (Term 'NameRes)
resolveTerm (Located loc e) =
    Located loc <$> scoped case e of
        Annotation term ty -> Annotation <$> resolveTerm term <*> inferForall (resolveTerm ty)
        Lambda arg body -> do
            arg' <- declarePat arg
            body' <- resolveTerm body
            pure $ Lambda arg' body'
        Let binding expr -> do
            binding' <- declareBinding binding
            expr' <- resolveTerm expr
            pure $ Let binding' expr'
        LetRec bindings expr -> do
            collectNames $ map (\b -> Located loc $ D.Value b []) $ NE.toList bindings
            bindings' <- traverse (resolveBinding []) bindings
            expr' <- resolveTerm expr
            pure $ LetRec bindings' expr'
        Case arg matches ->
            Case <$> resolveTerm arg <*> for matches \(pat, expr) -> scoped do
                pat' <- declarePat pat
                expr' <- resolveTerm expr
                pure (pat', expr')
        Match matches ->
            Match <$> for matches \(pats, expr) -> scoped do
                pats' <- traverse declarePat pats
                expr' <- resolveTerm expr
                pure (pats', expr')
        Q q vis er binder body -> do
            binder' <- resolveBinder binder
            body' <- resolveTerm body
            pure $ Q q vis er binder' body'
        Do stmts lastAction -> Do <$> traverse resolveStmt stmts <*> resolveTerm lastAction
        InfixE pairs last' -> InfixE <$> traverse (bitraverse resolveTerm (traverse resolve)) pairs <*> resolveTerm last'
        ImplicitVar var ->
            get @ImplicitVars >>= \case
                NotInTypeScope -> do
                    error $ OutOfScopeImplicit var
                    Name <$> declare var
                CollectingVars vars -> case List.lookup var vars of
                    Just name -> pure $ Name name
                    Nothing -> do
                        name <- declare var
                        put $ CollectingVars $ vars ++ [(var, name)]
                        pure $ Name name
        Name name@(Wildcard' txt :@ wloc) -> do
            stackIsEmpty <- null <$> get @[DList Name]
            if stackIsEmpty
                then do
                    name' <- declare name
                    error $ OutOfScopeWildcard name
                    pure $ Name name'
                else do
                    name' <- declare $ Name' ("$" <> txt) :@ wloc
                    modify @[DList Name] \case
                        (top : rest) -> DList.snoc top name' : rest
                        [] -> []
                    pure $ Name name'
        Parens expr -> do
            modify @[DList Name] (DList.empty :)
            body <- resolveTerm expr
            vars <- state @[DList Name] (splitAt 1)
            pure case NE.nonEmpty $ foldMap DList.toList vars of
                Nothing -> unLoc body
                Just varsNE -> WildcardLambda varsNE body
        other -> unLoc <$> partialTravTerm resolveTrav (other :@ loc)

resolveStmt :: (NameResCtx es, Declare :> es) => DoStatement 'Parse -> Eff es (DoStatement 'NameRes)
resolveStmt = traverse \case
    Bind pat body -> do
        body' <- resolveTerm body
        pat' <- declarePat pat
        pure $ Bind pat' body'
    With pat body -> do
        body' <- resolveTerm body
        pat' <- declarePat pat
        pure $ With pat' body'
    DoLet binding -> DoLet <$> declareBinding binding
    Action expr -> Action <$> resolveTerm expr

{- | declares the var in a binder; resolves names in its kind annotation, if any
the kind annotation may not reference the var
-}
resolveBinder :: (NameResCtx es, Declare :> es) => VarBinder 'Parse -> Eff es (VarBinder 'NameRes)
resolveBinder (VarBinder var k) = do
    k' <- traverse resolveTerm k
    var' <- declare var
    pure $ VarBinder var' k'
