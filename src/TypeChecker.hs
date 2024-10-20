{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE NoFieldSelectors #-}
{-# LANGUAGE GADTs #-}

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
    Declare,
    typecheck,
) where

import Common
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
    => HashMap Name (Type' 'Fixity) -- imports; note that the types may not be incomplete
    -> Builtins Name
    -> [Declaration 'Fixity]
    -> Eff es (Either TypeError (HashMap Name (Type' 'Fixity))) -- type checking doesn't add anything new to the AST, so we reuse 'Fixity for simplicity
typecheck env builtins decls = run (Right <$> env) builtins $ traverse normalise =<< inferDecls decls

-- finds all type parameters used in a type and creates corresponding forall clauses
-- ignores univars, because the intended use case is pre-processing user-supplied types
inferTypeVars :: Type' 'Fixity -> Type' 'Fixity
inferTypeVars ty = uncurry (foldr (T.Forall $ getLoc ty)) . second snd . runPureEff . runState (HashSet.empty, HashSet.empty) . go $ ty
  where
    go :: Type' 'Fixity -> Eff '[State (HashSet Name, HashSet Name)] (Type' 'Fixity)
    go = \case
        T.Var var -> do
            isNew <- not . HashSet.member var <$> gets @(HashSet Name, HashSet Name) snd
            when isNew $ modify @(HashSet Name, HashSet Name) (second $ HashSet.insert var)
            pure $ T.Var var
        T.Forall loc var body -> modify @(HashSet Name, HashSet Name) (first $ HashSet.insert var) >> T.Forall loc var <$> go body
        T.Exists loc var body -> modify @(HashSet Name, HashSet Name) (first $ HashSet.insert var) >> T.Exists loc var <$> go body
        T.Function loc from to -> T.Function loc <$> go from <*> go to
        T.Application loc lhs rhs -> T.Application loc <$> go lhs <*> go rhs
        T.Variant loc row -> T.Variant loc <$> traverse go row
        T.Record loc row -> T.Record loc <$> traverse go row
        T.Name name -> pure $ T.Name name

-- | check / infer types of a list of declarations that may reference each other
inferDecls :: InfEffs es => [Declaration 'Fixity] -> Eff es (HashMap Name Type)
inferDecls decls = do
    traverse_ updateTopLevel decls
    let (values, sigs) = second (fmap (T.cast id) . HashMap.fromList) $ foldr getValueDecls ([], []) decls
    fold <$> for values \(binding, locals) ->
        binding & collectNamesInBinding & listToMaybe >>= (`HashMap.lookup` sigs) & \case
            Just ty -> do
                checkBinding binding ty
                pure $
                    HashMap.mapMaybe (`HashMap.lookup` sigs) $
                        HashMap.fromList $
                            (\x -> (x, x)) <$> collectNamesInBinding binding
            Nothing -> scoped do
                declareAll =<< inferDecls locals
                typeMap <- traverse normalise =<< inferBinding binding -- todo: true top level should be separated from the parent scopes
                fmap (T.cast id) typeMap <$ declareTopLevel typeMap
  where
    updateTopLevel = \case
        D.Signature _ name sig ->
            modify \s -> s{topLevel = HashMap.insert name (Right $ inferTypeVars sig) s.topLevel}
        D.Value _ binding@(E.FunctionBinding _ name _ _) locals -> insertBinding name binding locals
        D.Value _ binding@(E.ValueBinding _ (P.Var name) _) locals -> insertBinding name binding locals
        D.Value _ E.ValueBinding{} _ -> pass -- todo
        D.Type loc name vars constrs ->
            for_ (mkConstrSigs loc name vars constrs) \(con, sig) ->
                modify \s -> s{topLevel = HashMap.insert con (Right sig) s.topLevel}
        D.Alias{} -> pass

    insertBinding name binding locals =
        let closure = UninferredType $ scoped do
                declareAll =<< inferDecls locals
                nameTypePairs <- traverse normalise =<< inferBinding binding
                declareTopLevel nameTypePairs
                case HashMap.lookup name nameTypePairs of
                    -- this can only happen if `inferBinding` returns an incorrect map of types
                    Nothing -> typeError $ "Internal error: type closure for" <+> pretty name <+> "didn't infer its type"
                    Just ty -> pure ty
         in modify \s ->
                s{topLevel = HashMap.insertWith (\_ x -> x) name (Left closure) s.topLevel}

    getValueDecls decl (values, sigs) = case decl of
        D.Value _ binding locals -> ((binding, locals) : values, sigs)
        D.Signature _ name sig -> (values, (name, sig) : sigs)
        D.Type loc name vars constrs -> (values, mkConstrSigs loc name vars constrs ++ sigs)
        D.Alias{} -> (values, sigs)

    mkConstrSigs :: Loc -> Name -> [Name] -> [Constructor 'Fixity] -> [(Name, Type' 'Fixity)]
    mkConstrSigs tyLoc name vars constrs =
        constrs <&> \(D.Constructor loc con params) ->
            ( con
            , foldr (T.Forall loc) (foldr (T.Function loc) fullType params) vars
            )
      where
        fullType = foldl' (T.Application tyLoc) (T.Name name) (T.Var <$> vars)

subtype :: InfEffs es => Type -> Type -> Eff es ()
subtype lhs_ rhs_ = join $ match <$> monoLayer In lhs_ <*> monoLayer Out rhs_
  where
    match = \cases
        lhs rhs | lhs == rhs -> pass -- simple cases, i.e. two type constructors, two univars or two exvars
        lhs (MLUniVar _ uni) -> solveOr (mono In $ unMonoLayer lhs) (subtype (unMonoLayer lhs) . unMono) uni
        (MLUniVar _ uni) rhs -> solveOr (mono Out $ unMonoLayer rhs) ((`subtype` unMonoLayer rhs) . unMono) uni
        (MLName lhs) (MLName rhs) ->
            unlessM (elem (lhs, rhs) <$> builtin (.subtypeRelations)) $
                typeError ("cannot unify" <+> pretty lhs <+> "with" <+> pretty rhs)
        (MLFn _ inl outl) (MLFn _ inr outr) -> do
            subtype inr inl
            subtype outl outr
        (MLApp _ lhs rhs) (MLApp _ lhs' rhs') -> do
            -- note that we assume the same variance for all type parameters
            -- some kind of kind system is needed to track variance and prevent stuff like `Maybe a b`
            -- higher-kinded types are also problematic when it comes to variance, i.e.
            -- is `f a` a subtype of `f b` when a is `a` subtype of `b` or the other way around?
            --
            -- QuickLook just assumes that all constructors are invariant and -> is a special case
            subtype lhs lhs'
            subtype rhs rhs'
        (MLVariant locL lhs) (MLVariant locR rhs) -> rowCase Variant (locL, lhs) (locR, rhs)
        (MLRecord locL lhs) (MLRecord locR rhs) -> rowCase Record (locL, lhs) (locR, rhs)
        (MLVar var) _ -> typeError $ "dangling type variable" <+> pretty var
        _ (MLVar var) -> typeError $ "dangling type variable" <+> pretty var
        lhs rhs -> typeError $ pretty lhs <+> "is not a subtype of" <+> pretty rhs

    rowCase :: InfEffs es => RecordOrVariant -> (Loc, ExtRow Type) -> (Loc, ExtRow Type) -> Eff es ()
    rowCase whatToMatch (locL, lhsRow) (locR, rhsRow) = do
        let con = conOf whatToMatch
        for_ (IsList.toList lhsRow.row) \(name, lhsTy) ->
            deepLookup whatToMatch name (con locR rhsRow) >>= \case
                Nothing ->
                    typeError $
                        pretty (con locL lhsRow)
                            <+> "is not a subtype of"
                            <+> pretty (con locR rhsRow)
                            <> ": right hand side does not contain"
                                <+> pretty name
                Just rhsTy -> subtype lhsTy rhsTy
        -- if the lhs has an extension, it should be compatible with rhs without the already matched fields
        for_ (Row.extension lhsRow) \ext -> subtype ext . con locL =<< diff whatToMatch rhsRow lhsRow.row

    -- turns out it's different enough from `withUniVar`
    solveOr :: InfEffs es => Eff es Monotype -> (Monotype -> Eff es ()) -> UniVar -> Eff es ()
    solveOr solveWith whenSolved uni = lookupUniVar uni >>= either (const $ solveUniVar uni =<< solveWith) whenSolved

check :: (InfEffs es) => Expr -> Type -> Eff es ()
check e type_ = scoped $ match e type_
  where
    match = \cases
        -- the cases for E.Name and E.Constructor are redundant, since
        -- `infer` just looks up their types anyway
        (E.Lambda _ arg body) (T.Function _ from to) -> scoped do
            -- `checkPattern` updates signatures of all mentioned variables
            checkPattern arg from
            check body to
        (E.Annotation _ expr annTy) ty -> do
            check expr $ T.cast id annTy
            subtype (T.cast id annTy) ty
        (E.If _ cond true false) ty -> do
            check cond $ T.Name $ BoolName $ getLoc cond
            check true ty
            check false ty
        (E.Case _ arg matches) ty -> do
            argTy <- infer arg
            for_ matches \(pat, body) -> do
                checkPattern pat argTy
                check body ty
        (E.List _ items) (T.Application _ (T.Name (ListName _)) itemTy) -> for_ items (`check` itemTy)
        (E.Record _ row) ty -> do
            for_ (IsList.toList row) \(name, expr) ->
                deepLookup Record name ty >>= \case
                    Nothing -> typeError $ pretty ty <+> "does not contain field" <+> pretty name
                    Just fieldTy -> check expr fieldTy
        expr (T.UniVar _ uni) ->
            lookupUniVar uni >>= \case
                Right ty -> check expr $ unMono ty
                Left _ -> do
                    newTy <- mono In =<< infer expr
                    lookupUniVar uni >>= \case
                        Left _ -> solveUniVar uni newTy
                        Right _ -> pass
        expr (T.Forall _ var body) -> check expr =<< substitute Out var body
        expr (T.Exists _ var body) -> check expr =<< substitute In var body
        expr ty -> do
            inferredTy <- infer expr
            subtype inferredTy ty

checkBinding :: InfEffs es => Binding 'Fixity -> Type -> Eff es ()
checkBinding binding ty = case binding of
    E.FunctionBinding loc _ args body -> check (foldr (E.Lambda loc) body args) ty
    E.ValueBinding _ pat body -> scoped $ checkPattern pat ty >> check body ty

checkPattern :: (InfEffs es, Declare :> es) => Pat -> Type -> Eff es ()
checkPattern = \cases
    -- we need this case, since inferPattern only infers monotypes for var patterns
    (P.Var name) ty -> updateSig name ty
    -- we probably do need a case for P.Constructor for the same reason
    (P.Variant _ name arg) ty ->
        deepLookup Variant name ty >>= \case
            Nothing -> typeError $ pretty ty <+> "does not contain variant" <+> pretty name
            Just argTy -> checkPattern arg argTy
    (P.Record _ patRow) ty -> do
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
            let loc = getLoc name
            var <- freshUniVar loc
            rowVar <- freshUniVar loc
            -- #a -> [Name #a | #r]
            pure $ T.Function loc var (T.Variant loc $ ExtRow (fromList [(name, var)]) rowVar)
        E.Application _ f x -> do
            fTy <- infer f
            inferApp fTy x
        E.Lambda loc arg body -> {-forallScope-} do
            argTy <- inferPattern arg
            T.Function loc argTy <$> infer body
        E.Let _ binding body -> do
            declareAll =<< inferBinding binding
            infer body
        E.Annotation _ expr ty -> T.cast id ty <$ check expr (T.cast id ty)
        E.If loc cond true false -> do
            check cond $ T.Name $ BoolName loc
            result <- unMono <$> (mono In =<< infer true)
            check false result
            pure result
        E.Case loc arg matches -> do
            argTy <- infer arg
            result <- freshUniVar loc
            for_ matches \(pat, body) -> do
                checkPattern pat argTy
                check body result
            pure result
        E.Match _ [] -> typeError "empty match expression"
        E.Match loc ((firstPats, firstBody) : ms) -> {-forallScope-} do
            bodyType <- infer firstBody
            patTypes <- traverse inferPattern firstPats
            for_ ms \(pats, body) -> do
                traverse_ (`checkPattern` bodyType) pats
                check body bodyType
            unless (all ((== length patTypes) . length . fst) ms) $
                typeError "different amount of arguments in a match statement"
            pure $ foldr (T.Function loc) bodyType patTypes
        E.List loc items -> do
            itemTy <- freshUniVar loc
            traverse_ (`check` itemTy) items
            pure $ T.Application loc (T.Name $ ListName loc) itemTy
        E.Record loc row -> T.Record loc . NoExtRow <$> traverse infer row
        E.RecordLens loc fields -> do
            recordParts <- for fields \field -> do
                rowVar <- freshUniVar loc
                pure \nested -> T.Record loc $ ExtRow (one (field, nested)) rowVar
            let mkNestedRecord = foldr1 (.) recordParts
            let tAppLoc = T.Application loc
            a <- freshUniVar loc
            b <- freshUniVar loc
            pure $
                T.Name (LensName loc)
                    `tAppLoc` mkNestedRecord a
                    `tAppLoc` mkNestedRecord b
                    `tAppLoc` a
                    `tAppLoc` b
        E.IntLiteral loc num
            | num >= 0 -> pure $ T.Name $ NatName loc
            | otherwise -> pure $ T.Name $ IntName loc
        E.TextLiteral loc _ -> pure $ T.Name $ TextName loc
        E.CharLiteral loc _ -> pure $ T.Name $ TextName loc
        E.Infix witness _ _ -> E.noInfix witness

inferApp :: InfEffs es => Type -> Expr -> Eff es Type
inferApp fTy arg = do
    monoLayer In fTy >>= \case
        MLUniVar loc uni -> do
            from <- infer arg
            to <- freshUniVar loc
            to <$ subtype (T.UniVar loc uni) (T.Function loc from to)
        MLFn _ from to -> do
            to <$ check arg from
        _ -> typeError $ pretty fTy <+> "is not a function type"

-- infers the type of a function / variables in a pattern
-- does not implicitly declare anything
inferBinding :: InfEffs es => Binding 'Fixity -> Eff es (HashMap Name Type)
inferBinding =
    scoped . forallScope . \case
        E.ValueBinding _ pat body -> do
            (patTy, bodyTy) <- do
                patTy <- inferPattern pat
                bodyTy <- infer body
                pure (patTy, bodyTy)
            subtype patTy bodyTy
            checkPattern pat bodyTy
            traverse lookupSig (HashMap.fromList $ (\x -> (x, x)) <$> collectNames pat)
        E.FunctionBinding loc name args body -> do
            -- note: we can only infer monotypes for recursive functions
            -- while checking the body, the function itself is assigned a univar
            -- in the end, we check that the inferred type is compatible with the one in the univar (inferred from recursive calls)
            uni <- freshUniVar'
            updateSig name $ T.UniVar loc uni
            argTypes <- traverse inferPattern args
            bodyTy <- infer body
            let ty = foldr (T.Function loc) bodyTy argTypes
            -- since we can still infer higher-rank types for non-recursive functions,
            -- we only need the subtype check when the univar is solved, i.e. when the
            -- functions contains any recursive calls at all
            withUniVar uni (subtype ty . unMono)
            pure $ HashMap.singleton name ty

-- \| collects all to-be-declared names in a pattern
collectNames :: Pattern p -> [NameAt p]
collectNames = \case
    P.Var name -> [name]
    P.Annotation _ pat _ -> collectNames pat
    P.Variant _ _ pat -> collectNames pat
    P.Constructor _ _ pats -> foldMap collectNames pats
    P.List _ pats -> foldMap collectNames pats
    P.Record _ row -> foldMap collectNames $ toList row
    -- once again, exhaustiveness checking is worth writing some boilerplate
    P.IntLiteral{} -> []
    P.TextLiteral{} -> []
    P.CharLiteral{} -> []

collectNamesInBinding :: Binding p -> [NameAt p]
collectNamesInBinding = \case
    E.FunctionBinding _ name _ _ -> [name]
    E.ValueBinding _ pat _ -> collectNames pat

inferPattern :: (InfEffs es, Declare :> es) => Pat -> Eff es Type
inferPattern = \case
    P.Var name -> do
        uni <- freshUniVar $ getLoc name
        updateSig name uni
        pure uni
    P.Annotation _ pat ty -> T.cast id ty <$ checkPattern pat (T.cast id ty)
    p@(P.Constructor _loc name args) -> do
        (resultType, argTypes) <- conArgTypes name
        unless (length argTypes == length args) $
            typeError $
                "incorrect arg count ("
                    <> pretty (length args)
                    <> ") in pattern" <+> pretty p <+> "(expected" <+> pretty (length argTypes)
                    <> ")"
        zipWithM_ checkPattern args argTypes
        pure resultType
    P.List loc pats -> do
        result <- freshUniVar loc
        traverse_ (`checkPattern` result) pats
        pure $ T.Application loc (T.Name $ ListName loc) result
    P.Variant loc name arg -> {-forallScope-} do
        argTy <- inferPattern arg
        T.Variant loc . ExtRow (fromList [(name, argTy)]) <$> freshUniVar loc
    P.Record loc row -> do
        typeRow <- traverse inferPattern row
        T.Record loc . ExtRow typeRow <$> freshUniVar loc
    P.IntLiteral loc num
        | num >= 0 -> pure $ T.Name $ NatName loc
        | otherwise -> pure $ T.Name $ IntName loc
    P.TextLiteral loc _ -> pure $ T.Name $ TextName loc
    P.CharLiteral loc _ -> pure $ T.Name $ TextName loc
  where
    -- conArgTypes and the zipM may be unified into a single function
    conArgTypes name = lookupSig name >>= go
    go =
        monoLayer In >=> \case
            MLFn _ arg rest -> second (arg :) <$> go rest
            -- univars should never appear as the rightmost argument of a value constructor type
            -- i.e. types of value constructors have the shape `a -> b -> c -> d -> ConcreteType a b c d`
            --
            -- solved univars cannot appear here either, since `lookupSig` on a pattern returns a type with no univars
            MLUniVar _ uni -> typeError $ "unexpected univar" <+> pretty uni <+> "in a constructor type"
            -- this kind of repetition is necwithUniVaressary to retain missing pattern warnings
            MLName name -> pure (T.Name name, [])
            MLApp loc lhs rhs -> pure (T.Application loc lhs rhs, [])
            MLVariant loc row -> pure (T.Variant loc row, [])
            MLRecord loc row -> pure (T.Record loc row, [])
            MLSkolem loc skolem -> pure (T.Skolem loc skolem, [])
            MLVar var -> pure (T.Var var, [])

-- gets rid of all univars
normalise :: InfEffs es => Type -> Eff es (Type' 'Fixity)
normalise = uniVarsToForall {->=> skolemsToExists-} >=> go
  where
    go = \case
        T.UniVar _ uni ->
            lookupUniVar uni >>= \case
                Left _ -> typeError $ "dangling univar " <> pretty uni
                Right body -> go (unMono body)
        T.Forall loc var body -> T.Forall loc var <$> go body
        T.Exists loc var body -> T.Exists loc var <$> go body
        T.Function loc from to -> T.Function loc <$> go from <*> go to
        T.Application loc lhs rhs -> T.Application loc <$> go lhs <*> go rhs
        T.Variant loc row -> T.Variant loc <$> traverse go row
        T.Record loc row -> T.Record loc <$> traverse go row
        T.Var v -> pure $ T.Var v
        T.Name name -> pure $ T.Name name
        skolem@T.Skolem{} -> typeError $ "skolem " <> pretty skolem <> " remains in code"

    -- this is an alternative to forallScope that's only suitable at the top level
    -- it also compresses any records found along the way, because I don't feel like
    -- making that a different pass, and `compress` uses `mono` under the hood, which
    -- means that it has to be run early
    uniVarsToForall ty = uncurry (foldr (T.Forall (getLoc ty))) <$> runState HashMap.empty (uniGo ty)
    uniGo :: InfEffs es => Type -> Eff (State (HashMap UniVar Name) : es) Type
    uniGo = \case
        T.UniVar loc uni -> do
            gets @(HashMap UniVar Name) (HashMap.lookup uni) >>= \case
                Just var -> pure $ T.Var var -- I'm not sure where should typevars originate from
                Nothing ->
                    lookupUniVar uni >>= \case
                        Left _ -> do
                            tyVar <- freshTypeVar loc
                            modify $ HashMap.insert uni tyVar
                            pure $ T.Var tyVar
                        Right body -> uniGo $ unMono body
        T.Forall loc var body -> T.Forall loc var <$> uniGo body
        T.Exists loc var body -> T.Exists loc var <$> uniGo body
        T.Function loc from to -> T.Function loc <$> uniGo from <*> uniGo to
        T.Application loc lhs rhs -> T.Application loc <$> uniGo lhs <*> uniGo rhs
        T.Variant loc row -> T.Variant loc <$> (traverse uniGo =<< compress Variant row)
        T.Record loc row -> T.Record loc <$> (traverse uniGo =<< compress Record row)
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

replaceSkolems :: InfEffs es => (Loc -> Name -> Type -> Type) -> Type -> Eff es Type
replaceSkolems con ty = uncurry (foldr (con $ getLoc ty)) <$> runState HashMap.empty (go ty)
  where
    go :: InfEffs es => Type -> Eff (State (HashMap Skolem Name) : es) Type
    go = \case
        T.Skolem loc skolem ->
            get @(HashMap Skolem Name) >>= \acc -> case HashMap.lookup skolem acc of
                Just tyVar -> pure $ T.Var tyVar
                Nothing -> do
                    tyVar <- freshTypeVar loc
                    modify $ HashMap.insert skolem tyVar
                    pure $ T.Var tyVar
        T.UniVar loc uni ->
            lookupUniVar uni >>= \case
                Left _ -> pure $ T.UniVar loc uni
                Right body -> do
                    body' <- go $ undefined body
                    overrideUniVar uni $ undefined body'
                    pure body'
        T.Forall loc var body -> T.Forall loc var <$> go body
        T.Exists loc var body -> T.Exists loc var <$> go body
        T.Function loc from to -> T.Function loc <$> go from <*> go to
        T.Application loc lhs rhs -> T.Application loc <$> go lhs <*> go rhs
        T.Record loc row -> T.Record loc <$> traverse go row
        T.Variant loc row -> T.Variant loc <$> traverse go row
        v@T.Var{} -> pure v
        name@T.Name{} -> pure name
