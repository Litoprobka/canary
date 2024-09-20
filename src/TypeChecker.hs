{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE NoFieldSelectors #-}

module TypeChecker (
    run,
    runWithFinalEnv,
    infer,
    inferPattern,
    inferBinding,
    check,
    checkPattern,
    subtype,
    inferTypeVars,
    normalise,
    Builtins (..),
    InfState (..),
    TypeError (..),
    InfEffs,
    typecheck,
) where

import CheckerTypes
import Data.Foldable1 (foldr1)
import Data.HashMap.Strict qualified as HashMap
import Data.HashSet qualified as HashSet
import Data.Traversable (for)
import Effectful
import Effectful.State.Static.Local (State, get, gets, modify, runState)
import GHC.IsList qualified as IsList
import NameGen
import Prettyprinter (pretty, (<+>))
import Relude hiding (Reader, State, Type, ask, bool, get, gets, modify, put, runReader, runState)
import Syntax
import Syntax.Declaration qualified as D
import Syntax.Expression qualified as E
import Syntax.Pattern qualified as P
import Syntax.Row (ExtRow (..))
import Syntax.Row qualified as Row
import Syntax.Type qualified as T
import TypeChecker.Backend

typecheck
    :: NameGen :> es
    => HashMap Name Type -- imports
    -> Builtins Name
    -> [Declaration Name]
    -> Eff es (Either TypeError (HashMap Name Type))
typecheck env builtins decls = run (Right <$> env) builtins $ traverse normalise =<< inferDecls decls

-- finds all type parameters used in a type and creates corresponding forall clauses
-- doesn't work with type vars (univars?), because the intended use case is pre-processing user-supplied types
inferTypeVars :: Type -> Type
inferTypeVars = uncurry (foldr T.Forall) . second snd . runPureEff . runState (HashSet.empty, HashSet.empty) . go
  where
    go :: Type -> Eff '[State (HashSet Name, HashSet Name)] Type
    go = \case
        T.Var var -> do
            isNew <- not . HashSet.member var <$> gets @(HashSet Name, HashSet Name) snd
            when isNew $ modify @(HashSet Name, HashSet Name) (second $ HashSet.insert var)
            pure $ T.Var var
        T.Forall var body -> modify @(HashSet Name, HashSet Name) (first $ HashSet.insert var) >> T.Forall var <$> go body
        T.Exists var body -> modify @(HashSet Name, HashSet Name) (first $ HashSet.insert var) >> T.Exists var <$> go body
        T.Function from to -> T.Function <$> go from <*> go to
        T.Application lhs rhs -> T.Application <$> go lhs <*> go rhs
        T.Variant row -> T.Variant <$> traverse go row
        T.Record row -> T.Record <$> traverse go row
        uni@T.UniVar{} -> pure uni
        skolem@T.Skolem{} -> pure skolem
        name@T.Name{} -> pure name

-- | check / infer types of a list of declarations that may reference each other
inferDecls :: InfEffs es => [Declaration Name] -> Eff es (HashMap Name Type)
inferDecls decls = do
    traverse_ updateTopLevel decls
    let (values, sigs) = second HashMap.fromList $ foldr getValueDecls ([], []) decls
    foldr (<>) HashMap.empty <$> for values \(binding, locals) ->
        (=<<) (`HashMap.lookup` sigs) (listToMaybe $ collectNamesInBinding binding) & \case
            Just ty -> do
                checkBinding binding ty
                pure $
                    HashMap.mapMaybe (`HashMap.lookup` sigs) $
                        HashMap.fromList $
                            (\x -> (x, x)) <$> collectNamesInBinding binding
            Nothing -> scoped do
                declareAll =<< inferDecls locals
                typeMap <- inferBinding binding
                typeMap <$ declareTopLevel typeMap
  where
    updateTopLevel = \case
        D.Signature name sig ->
            modify \s -> s{topLevel = HashMap.insert name (Right $ inferTypeVars sig) s.topLevel}
        D.Value binding@(E.FunctionBinding name _ _) locals -> insertBinding name binding locals
        D.Value binding@(E.ValueBinding (P.Var name) _) locals -> insertBinding name binding locals
        D.Value E.ValueBinding{} _ -> pass -- todo
        D.Type name vars constrs ->
            for_ (mkConstrSigs name vars constrs) \(con, sig) ->
                modify \s -> s{topLevel = HashMap.insert con (Right sig) s.topLevel}
        D.Alias{} -> pass

    insertBinding name binding locals =
        let closure = UninferredType $ forallScope $ scoped do
                declareAll =<< inferDecls locals
                nameTypePairs <- inferBinding binding
                declareTopLevel nameTypePairs
                case HashMap.lookup name nameTypePairs of
                    -- this can only happen if `inferBinding` returns an incorrect map of types
                    Nothing -> typeError $ "Internal error: type closure for" <+> pretty name <+> "didn't infer its type"
                    Just ty -> pure ty
         in modify \s ->
                s{topLevel = HashMap.insertWith (\_ x -> x) name (Left closure) s.topLevel}

    getValueDecls decl (values, sigs) = case decl of
        D.Value binding locals -> ((binding, locals) : values, sigs)
        D.Signature name sig -> (values, (name, sig) : sigs)
        D.Type name vars constrs -> (values, mkConstrSigs name vars constrs ++ sigs)
        D.Alias{} -> (values, sigs)

    mkConstrSigs :: Name -> [Name] -> [(Name, [Type])] -> [(Name, Type)]
    mkConstrSigs name vars constrs =
        second (\conParams -> foldr T.Forall (foldr T.Function (T.Name name) conParams) vars)
            <$> constrs

subtype :: InfEffs es => Type -> Type -> Eff es ()
subtype lhs_ rhs_ = join $ match <$> monoLayer In lhs_ <*> monoLayer Out rhs_
  where
    match = \cases
        lhs rhs | lhs == rhs -> pass -- simple cases, i.e. two type constructors, two univars or two exvars
        lhs (MLUniVar uni) -> solveOr (mono In $ unMonoLayer lhs) (subtype (unMonoLayer lhs) . unMono) uni
        (MLUniVar uni) rhs -> solveOr (mono Out $ unMonoLayer rhs) ((`subtype` unMonoLayer rhs) . unMono) uni
        (MLName lhs) (MLName rhs) ->
            unlessM (elem (lhs, rhs) <$> builtin (.subtypeRelations)) $
                typeError ("cannot unify" <+> pretty lhs <+> "with" <+> pretty rhs)
        (MLFn inl outl) (MLFn inr outr) -> do
            subtype inr inl
            subtype outl outr
        (MLApp lhs rhs) (MLApp lhs' rhs') -> do
            -- note that we assume the same variance for all type parameters
            -- some kind of kind system is needed to track variance and prevent stuff like `Maybe a b`
            -- higher-kinded types are also problematic when it comes to variance, i.e.
            -- is `f a` a subtype of `f b` when a is `a` subtype of `b` or the other way around?
            --
            -- QuickLook just assumes that all constructors are invariant and -> is a special case
            subtype lhs lhs'
            subtype rhs rhs'
        (MLVariant lhs) (MLVariant rhs) -> rowCase Variant lhs rhs
        (MLRecord lhs) (MLRecord rhs) -> rowCase Record lhs rhs
        lhs rhs -> typeError $ pretty lhs <+> "is not a subtype of" <+> pretty rhs

    rowCase whatToMatch lhsRow rhsRow = do
        let con = conOf whatToMatch
        for_ (IsList.toList lhsRow.row) \(name, lhsTy) ->
            deepLookup whatToMatch name (con rhsRow) >>= \case
                Nothing ->
                    typeError $
                        pretty (con lhsRow)
                            <+> "is not a subtype of"
                            <+> pretty (con rhsRow)
                            <> ": right hand side does not contain"
                                <+> pretty name
                Just rhsTy -> subtype lhsTy rhsTy
        -- if the lhs has an extension, it should be compatible with rhs without the already matched fields
        for_ (Row.extension lhsRow) \ext -> subtype ext . con =<< diff whatToMatch rhsRow lhsRow.row

    -- turns out it's different enough from `withUniVar`
    solveOr :: InfEffs es => Eff es Monotype -> (Monotype -> Eff es ()) -> UniVar -> Eff es ()
    solveOr solveWith whenSolved uni = lookupUniVar uni >>= either (const $ solveUniVar uni =<< solveWith) whenSolved

check :: InfEffs es => Expr -> Type -> Eff es ()
check e type_ = scoped $ match e type_
  where
    match = \cases
        -- the cases for E.Name and E.Constructor are redundant, since
        -- `infer` just looks up their types anyway
        (E.Lambda arg body) (T.Function from to) -> scoped do
            -- `checkPattern` updates signatures of all mentioned variables
            checkPattern arg from
            check body to
        (E.Annotation expr annTy) ty -> do
            check expr annTy
            subtype annTy ty
        (E.If cond true false) ty -> do
            check cond $ T.Name BoolName
            check true ty
            check false ty
        (E.Case arg matches) ty -> do
            argTy <- infer arg
            for_ matches \(pat, body) -> do
                checkPattern pat argTy
                check body ty
        (E.List items) (T.Application (T.Name ListName) itemTy) -> for_ items (`check` itemTy)
        (E.Record row) ty -> do
            for_ (IsList.toList row) \(name, expr) ->
                deepLookup Record name ty >>= \case
                    Nothing -> typeError $ pretty ty <+> "does not contain field" <+> pretty name
                    Just fieldTy -> check expr fieldTy
        expr (T.UniVar uni) ->
            lookupUniVar uni >>= \case
                Right ty -> check expr $ unMono ty
                Left _ -> do
                    newTy <- mono In =<< infer expr
                    lookupUniVar uni >>= \case
                        Left _ -> solveUniVar uni newTy
                        Right _ -> pass
        expr (T.Forall var body) -> check expr =<< substitute Out var body
        expr (T.Exists var body) -> check expr =<< substitute In var body
        expr ty -> do
            inferredTy <- infer expr
            subtype inferredTy ty

checkBinding :: InfEffs es => Binding Name -> Type -> Eff es ()
checkBinding binding ty = case binding of
    E.FunctionBinding _ args body -> check (foldr E.Lambda body args) ty
    E.ValueBinding pat body -> checkPattern pat ty >> check body ty

checkPattern :: InfEffs es => Pattern' -> Type -> Eff es ()
checkPattern = \cases
    -- we need this case, since inferPattern only infers monotypes for var patterns
    (P.Var name) ty -> updateSig name ty
    -- we probably do need a case for P.Constructor for the same reason
    (P.Variant name arg) ty ->
        deepLookup Variant name ty >>= \case
            Nothing -> typeError $ pretty ty <+> "does not contain variant" <+> pretty name
            Just argTy -> checkPattern arg argTy
    (P.Record patRow) ty -> do
        for_ (IsList.toList patRow) \(name, pat) ->
            deepLookup Record name ty >>= \case
                Nothing -> typeError $ pretty ty <+> "does not contain field" <+> pretty name
                Just fieldTy -> checkPattern pat fieldTy
    pat ty -> do
        inferredTy <- inferPattern pat
        subtype inferredTy ty

infer :: InfEffs es => Expr -> Eff es Type
infer =
    scoped . \case
        E.Name name -> lookupSig name
        E.Constructor name -> lookupSig name
        E.Variant name -> {-forallScope-} do
            var <- freshUniVar
            rowVar <- freshUniVar
            -- #a -> [Name #a | #r]
            pure $ T.Function var (T.Variant $ ExtRow (fromList [(name, var)]) rowVar)
        E.Application f x -> do
            fTy <- infer f
            inferApp fTy x
        E.Lambda arg body -> {-forallScope-} do
            argTy <- inferPattern arg
            T.Function argTy <$> infer body
        E.Let binding body -> do
            declareAll =<< inferBinding binding
            infer body
        E.Annotation expr ty -> ty <$ check expr ty
        E.If cond true false -> do
            check cond $ T.Name BoolName
            result <- unMono <$> (mono In =<< infer true)
            check false result
            pure result
        E.Case arg matches -> do
            argTy <- infer arg
            result <- freshUniVar
            for_ matches \(pat, body) -> do
                checkPattern pat argTy
                check body result
            pure result
        E.Match [] -> typeError "empty match expression"
        E.Match ((firstPats, firstBody) : ms) -> {-forallScope-} do
            bodyType <- infer firstBody
            patTypes <- traverse inferPattern firstPats
            for_ ms \(pats, body) -> do
                traverse_ (`checkPattern` bodyType) pats
                check body bodyType
            unless (all ((== length patTypes) . length . fst) ms) $
                typeError "different amount of arguments in a match statement"
            pure $ foldr T.Function bodyType patTypes
        E.List items -> do
            itemTy <- freshUniVar
            traverse_ (`check` itemTy) items
            pure $ T.Application (T.Name ListName) itemTy
        E.Record row -> T.Record . NoExtRow <$> traverse infer row
        E.RecordLens fields -> do
            recordParts <- for fields \field -> do
                rowVar <- freshUniVar
                pure \nested -> T.Record $ ExtRow (one (field, nested)) rowVar
            let mkNestedRecord = foldr1 (.) recordParts
            a <- freshUniVar
            b <- freshUniVar
            pure $
                T.Name LensName
                    `T.Application` mkNestedRecord a
                    `T.Application` mkNestedRecord b
                    `T.Application` a
                    `T.Application` b
        E.IntLiteral num
            | num >= 0 -> pure $ T.Name NatName
            | otherwise -> pure $ T.Name IntName
        E.TextLiteral _ -> pure $ T.Name TextName
        E.CharLiteral _ -> pure $ T.Name TextName

-- infers the type of a function / variables in a pattern
-- does not implicitly declare anything
inferBinding :: InfEffs es => Binding Name -> Eff es (HashMap Name Type)
inferBinding = \case
    E.ValueBinding pat body -> scoped do
        bodyTy <- infer body
        checkPattern pat bodyTy
        traverse lookupSig (HashMap.fromList $ (\x -> (x, x)) <$> collectNames pat)
    E.FunctionBinding name args body -> do
        argTypes <- traverse inferPattern args
        bodyTy <- infer body
        let ty = foldr T.Function bodyTy argTypes
        pure $ HashMap.singleton name ty

-- \| collects all to-be-declared names in a pattern
collectNames :: Pattern a -> [a]
collectNames = \case
    P.Var name -> [name]
    P.Annotation pat _ -> collectNames pat
    P.Variant _ pat -> collectNames pat
    P.Constructor _ pats -> foldMap collectNames pats
    P.List pats -> foldMap collectNames pats
    P.Record row -> foldMap collectNames $ toList row
    -- once again, exhaustiveness checking is worth writing some boilerplate
    P.IntLiteral{} -> []
    P.TextLiteral{} -> []
    P.CharLiteral{} -> []

collectNamesInBinding :: Binding a -> [a]
collectNamesInBinding = \case
    E.FunctionBinding name _ _ -> [name]
    E.ValueBinding pat _ -> collectNames pat

inferPattern :: InfEffs es => Pattern' -> Eff es Type
inferPattern = \case
    P.Var name -> do
        uni <- freshUniVar
        updateSig name uni
        pure uni
    P.Annotation pat ty -> ty <$ checkPattern pat ty
    p@(P.Constructor name args) -> do
        (resultType, argTypes) <- conArgTypes name
        unless (length argTypes == length args) $ typeError $ "incorrect arg count in pattern" <+> pretty p
        zipWithM_ checkPattern args argTypes
        pure resultType
    P.List pats -> do
        result <- freshUniVar
        traverse_ (`checkPattern` result) pats
        pure $ T.Application (T.Name ListName) result
    P.Variant name arg -> {-forallScope-} do
        argTy <- inferPattern arg
        T.Variant . ExtRow (fromList [(name, argTy)]) <$> freshUniVar
    P.Record row -> do
        typeRow <- traverse inferPattern row
        T.Record . ExtRow typeRow <$> freshUniVar
    P.IntLiteral num
        | num >= 0 -> pure $ T.Name NatName
        | otherwise -> pure $ T.Name IntName
    P.TextLiteral _ -> pure $ T.Name TextName
    P.CharLiteral _ -> pure $ T.Name TextName
  where
    -- conArgTypes and the zipM may be unified into a single function
    conArgTypes = lookupSig >=> go
    go =
        monoLayer In >=> \case
            MLFn arg rest -> second (arg :) <$> go rest
            -- univars should never appear as the rightmost argument of a value constructor type
            -- i.e. types of value constructors have the shape `a -> b -> c -> d -> ConcreteType a b c d`
            --
            -- solved univars cannot appear here either, since `lookupSig` on a pattern returns a type with no univars
            MLUniVar uni -> typeError $ "unexpected univar" <+> pretty uni <+> "in a constructor type"
            -- this kind of repetition is necessary to retain missing pattern warnings
            MLName name -> pure (T.Name name, [])
            MLApp lhs rhs -> pure (T.Application lhs rhs, [])
            MLVariant row -> pure (T.Variant row, [])
            MLRecord row -> pure (T.Record row, [])
            MLSkolem skolem -> pure (T.Skolem skolem, [])
            MLVar var -> pure (T.Var var, [])

inferApp :: InfEffs es => Type -> Expr -> Eff es Type
inferApp fTy arg =
    monoLayer In fTy >>= \case
        MLUniVar uni -> do
            from <- infer arg
            to <- freshUniVar
            to <$ subtype (T.UniVar uni) (T.Function from to)
        MLFn from to -> to <$ check arg from
        _ -> typeError $ pretty fTy <+> "is not a function type"

-- gets rid of all univars
normalise :: InfEffs es => Type -> Eff es Type
normalise = uniVarsToForall {->=> skolemsToExists-} >=> go
  where
    go = \case
        T.UniVar uni ->
            lookupUniVar uni >>= \case
                Left _ -> typeError $ "dangling univar " <> pretty uni
                Right body -> go (unMono body)
        T.Forall var body -> T.Forall var <$> go body
        T.Exists var body -> T.Exists var <$> go body
        T.Function from to -> T.Function <$> go from <*> go to
        T.Application lhs rhs -> T.Application <$> go lhs <*> go rhs
        T.Variant row -> T.Variant <$> traverse go row
        T.Record row -> T.Record <$> traverse go row
        v@T.Var{} -> pure v
        name@T.Name{} -> pure name
        skolem@T.Skolem{} -> pure skolem -- typeError $ "skolem " <> pretty skolem <> " remains in code"

    -- this is an alternative to forallScope that's only suitable at the top level
    -- it also compresses any records found along the way, because I don't feel like
    -- making that a different pass, and `compress` uses `mono` under the hood, which
    -- means that it has to be run early
    uniVarsToForall ty = uncurry (foldr T.Forall) <$> runState HashMap.empty (uniGo ty)
    uniGo :: InfEffs es => Type -> Eff (State (HashMap UniVar Name) : es) Type
    uniGo = \case
        T.UniVar uni -> do
            gets @(HashMap UniVar Name) (HashMap.lookup uni) >>= \case
                Just var -> pure $ T.Var var
                Nothing ->
                    lookupUniVar uni >>= \case
                        Left _ -> do
                            tyVar <- freshTypeVar
                            modify $ HashMap.insert uni tyVar
                            pure $ T.Var tyVar
                        Right body -> uniGo $ unMono body
        T.Forall var body -> T.Forall var <$> uniGo body
        T.Exists var body -> T.Exists var <$> uniGo body
        T.Function from to -> T.Function <$> uniGo from <*> uniGo to
        T.Application lhs rhs -> T.Application <$> uniGo lhs <*> uniGo rhs
        T.Variant row -> T.Variant <$> (traverse uniGo =<< compress Variant row)
        T.Record row -> T.Record <$> (traverse uniGo =<< compress Record row)
        v@T.Var{} -> pure v
        name@T.Name{} -> pure name
        skolem@T.Skolem{} -> pure skolem

-- these two functions have the same problem as the old `forallScope` - they capture skolems from an outer scope
-- it's not clear whether anything should be done about them
-- the only problem I can see is a univar unifying with a type var from an inner scope, but I'm not sure how would that happen
--
-- it is still safe to use these at the top-level, however
skolemsToExists, skolemsToForall :: forall es. InfEffs es => Type -> Eff es Type
-- ∃a. a -> a <: b
-- ?a -> ?a <: b
-- b ~ ∃a. a -> a
skolemsToExists = replaceSkolems T.Exists
-- b <: ∀a. a -> a
-- b <: ?a -> ?a
-- b ~ ∀a. a -> a
skolemsToForall = replaceSkolems T.Forall

replaceSkolems :: InfEffs es => (Name -> Type -> Type) -> Type -> Eff es Type
replaceSkolems con ty = uncurry (foldr con) <$> runState HashMap.empty (go ty)
  where
    go :: InfEffs es => Type -> Eff (State (HashMap Skolem Name) : es) Type
    go = \case
        T.Skolem skolem ->
            get @(HashMap Skolem Name) >>= \acc -> case HashMap.lookup skolem acc of
                Just tyVar -> pure $ T.Var tyVar
                Nothing -> do
                    tyVar <- freshTypeVar
                    modify $ HashMap.insert skolem tyVar
                    pure $ T.Var tyVar
        T.UniVar uni ->
            lookupUniVar uni >>= \case
                Left _ -> pure $ T.UniVar uni
                Right body -> do
                    body' <- go $ undefined body
                    overrideUniVar uni $ undefined body'
                    pure body'
        T.Forall var body -> T.Forall var <$> go body
        T.Exists var body -> T.Exists var <$> go body
        T.Function from to -> T.Function <$> go from <*> go to
        T.Application lhs rhs -> T.Application <$> go lhs <*> go rhs
        T.Record row -> T.Record <$> traverse go row
        T.Variant row -> T.Variant <$> traverse go row
        v@T.Var{} -> pure v
        name@T.Name{} -> pure name
