{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE GADTs #-}
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
    InfEffs,
    Declare,
    typecheck,
) where

import Common (Name)
import Common hiding (Name)
import Data.Foldable1 (foldr1)
import Data.HashMap.Strict qualified as HashMap
import Data.HashSet qualified as HashSet
import Data.List.NonEmpty qualified as NE
import Data.Traversable (for)
import Diagnostic (Diagnose, internalError)
import Effectful
import Effectful.State.Static.Local (State, gets, modify, runState)
import GHC.IsList qualified as IsList
import LangPrelude hiding (bool)
import LensyUniplate hiding (cast)
import NameGen
import Syntax
import Syntax.Declaration qualified as D
import Syntax.Row (ExtRow (..))
import Syntax.Row qualified as Row
import Syntax.Term hiding (Record, Variant)
import Syntax.Term qualified as E (Term (Record, Variant))
import Syntax.Term qualified as T (Term (Skolem, UniVar), uniplate)
import TypeChecker.Backend

typecheck
    :: (NameGen :> es, Diagnose :> es)
    => HashMap Name (Type 'Fixity) -- imports; note that the types may not be incomplete
    -> Builtins Name
    -> [Declaration 'Fixity]
    -> Eff es (HashMap Name (Type 'Fixity)) -- type checking doesn't add anything new to the AST, so we reuse 'Fixity for simplicity
typecheck env builtins decls = run (Right <$> env) builtins $ normaliseAll $ inferDecls decls

-- finds all type parameters used in a type and creates corresponding forall clauses
inferTypeVars :: Type 'Fixity -> Type 'Fixity
inferTypeVars ty =
    uncurry (foldr (Forall (getLoc ty) . plainBinder)) . second snd . runPureEff . runState (HashSet.empty, HashSet.empty) . go $
        ty
  where
    go :: Type 'Fixity -> Eff '[State (HashSet Name, HashSet Name)] (Type 'Fixity)
    go = transformM T.uniplate \case
        Var var -> do
            isNew <- not . HashSet.member var <$> gets @(HashSet Name, HashSet Name) snd
            when isNew $ modify @(HashSet Name, HashSet Name) (second $ HashSet.insert var)
            pure $ Var var
        forall_@(Forall _ binder _) -> forall_ <$ modify @(HashSet Name, HashSet Name) (first $ HashSet.insert binder.var)
        exists_@(Exists _ binder _) -> exists_ <$ modify @(HashSet Name, HashSet Name) (first $ HashSet.insert binder.var)
        other -> pure other

-- | check / infer types of a list of declarations that may reference each other
inferDecls :: InfEffs es => [Declaration 'Fixity] -> Eff es (HashMap Name TypeDT)
inferDecls decls = do
    -- ideally, all of this shuffling around should be moved to the dependency resolution pass
    traverse_ updateTopLevel decls
    let (values, sigs') = second HashMap.fromList $ foldr getValueDecls ([], []) decls
    -- kind-checking all signatures
    traverse_ (`check` type_ Blank) sigs'
    let sigs = fmap cast sigs'
    (<> sigs) . fold <$> for values \(binding, locals) ->
        binding & collectNamesInBinding & listToMaybe >>= (`HashMap.lookup` sigs) & \case
            Just ty -> do
                checkBinding binding ty
                pure $
                    HashMap.compose sigs $
                        HashMap.fromList $
                            (\x -> (x, x)) <$> collectNamesInBinding binding
            Nothing -> scoped do
                declareAll =<< inferDecls locals
                typeMap <- normaliseAll $ inferBinding binding -- todo: true top level should be separated from the parent scopes
                fmap cast typeMap <$ declareTopLevel typeMap
  where
    updateTopLevel = \case
        D.Signature _ name sig ->
            modify \s -> s{topLevel = HashMap.insert name (Right $ inferTypeVars sig) s.topLevel}
        D.Value _ binding@(FunctionB name _ _) locals -> insertBinding name binding locals
        D.Value _ binding@(ValueB (VarP name) _) locals -> insertBinding name binding locals
        D.Value loc ValueB{} _ -> internalError loc "destructuring bindings are not supported yet"
        D.Type loc name binders constrs ->
            for_ (mkConstrSigs name binders constrs) \(con, sig) ->
                modify \s -> s{topLevel = HashMap.insert name (Right $ typeKind loc binders) $ HashMap.insert con (Right sig) s.topLevel}
        D.GADT loc name mbKind constrs ->
            for_ constrs \con ->
                modify \s -> s{topLevel = HashMap.insert name (Right $ getKind loc mbKind) $ HashMap.insert con.name (Right con.sig) s.topLevel}
    typeKind loc = go
      where
        go [] = type_ loc
        go (binder : rest) = Function loc (getKind (getLoc binder) binder.kind) (go rest)
    getKind loc = fromMaybe (type_ loc)
    type_ :: NameAt p ~ Name => Loc -> Type p
    type_ loc = Name $ Located loc TypeName

    insertBinding name binding locals =
        let closure = UninferredType $ scoped do
                declareAll =<< inferDecls locals
                nameTypePairs <- topLevelScope $ normaliseAll $ inferBinding binding
                declareTopLevel nameTypePairs
                case HashMap.lookup name nameTypePairs of
                    -- this can only happen if `inferBinding` returns an incorrect map of types
                    Nothing -> internalError (getLoc name) $ "type closure for" <+> pretty name <+> "didn't infer its type"
                    Just ty -> pure ty
         in modify \s ->
                s{topLevel = HashMap.insertWith (\_ x -> x) name (Left closure) s.topLevel}

    getValueDecls decl (values, sigs) = case decl of
        D.Value _ binding locals -> ((binding, locals) : values, sigs)
        D.Signature _ name sig -> (values, (name, sig) : sigs)
        D.Type _ name vars constrs -> (values, mkConstrSigs name vars constrs ++ sigs)
        D.GADT _ _ _ constrs -> (values, (constrs <&> \con -> (con.name, con.sig)) ++ sigs)

    mkConstrSigs :: Name -> [VarBinder 'Fixity] -> [Constructor 'Fixity] -> [(Name, Type 'Fixity)]
    mkConstrSigs name binders constrs =
        constrs <&> \(D.Constructor loc con params) ->
            ( con
            , foldr (Forall loc) (foldr (Function loc) fullType params) binders
            )
      where
        fullType = foldl' Application (Name name) (Var . (.var) <$> binders)

subtype :: InfEffs es => TypeDT -> TypeDT -> Eff es ()
subtype lhs_ rhs_ = join $ match <$> monoLayer In lhs_ <*> monoLayer Out rhs_
  where
    match = \cases
        lhs rhs | lhs == rhs -> pass -- simple cases, i.e. two type constructors, two univars or two exvars
        lhs (MLUniVar _ uni) -> solveOr (mono In $ unMonoLayer lhs) (subtype (unMonoLayer lhs) . unMono) uni
        (MLUniVar _ uni) rhs -> solveOr (mono Out $ unMonoLayer rhs) ((`subtype` unMonoLayer rhs) . unMono) uni
        (MLName lhs) (MLName rhs) ->
            unlessM (elem (lhs, rhs) <$> builtin (.subtypeRelations)) do
                typeError $ CannotUnify lhs rhs
        (MLFn _ inl outl) (MLFn _ inr outr) -> do
            subtype inr inl
            subtype outl outr
        (MLApp lhs rhs) (MLApp lhs' rhs') -> do
            -- note that we assume the same variance for all type parameters
            -- seems like we need to track variance in kinds for this to work properly
            -- higher-kinded types are also problematic when it comes to variance, i.e.
            -- is `f a` a subtype of `f b` when a is `a` subtype of `b` or the other way around?
            --
            -- QuickLook just assumes that all constructors are invariant and -> is a special case
            subtype lhs lhs'
            subtype rhs rhs'
        (MLVariant locL lhs) (MLVariant locR rhs) -> rowCase Variant (locL, lhs) (locR, rhs)
        (MLRecord locL lhs) (MLRecord locR rhs) -> rowCase Record (locL, lhs) (locR, rhs)
        (MLVar var) _ -> internalError (getLoc var) $ "dangling type variable" <+> pretty var
        _ (MLVar var) -> internalError (getLoc var) $ "dangling type variable" <+> pretty var
        lhs rhs -> typeError $ NotASubtype (unMonoLayer lhs) (unMonoLayer rhs) Nothing

    rowCase :: InfEffs es => RecordOrVariant -> (Loc, ExtRow TypeDT) -> (Loc, ExtRow TypeDT) -> Eff es ()
    rowCase whatToMatch (locL, lhsRow) (locR, rhsRow) = do
        let con = conOf whatToMatch
        for_ (IsList.toList lhsRow.row) \(name, lhsTy) ->
            deepLookup whatToMatch name (con locR rhsRow) >>= \case
                Nothing -> typeError $ NotASubtype (con locL lhsRow) (con locR rhsRow) (Just name)
                Just rhsTy -> subtype lhsTy rhsTy
        -- if the lhs has an extension, it should be compatible with rhs without the already matched fields
        for_ (Row.extension lhsRow) \ext -> subtype ext . con locL =<< diff whatToMatch rhsRow lhsRow.row

    -- turns out it's different enough from `withUniVar`
    solveOr :: InfEffs es => Eff es Monotype -> (Monotype -> Eff es ()) -> UniVar -> Eff es ()
    solveOr solveWith whenSolved uni = lookupUniVar uni >>= either (const $ solveUniVar uni =<< solveWith) whenSolved

check :: InfEffs es => Expr 'Fixity -> TypeDT -> Eff es ()
check e type_ = scoped $ match e type_
  where
    match = \cases
        -- the case for E.Name is redundant, since
        -- `infer` just looks up its type anyway
        (Lambda _ arg body) (Function _ from to) -> scoped do
            -- `checkPattern` updates signatures of all mentioned variables
            checkPattern arg from
            check body to
        (Annotation expr annTy) ty -> do
            check expr $ cast annTy
            subtype (cast annTy) ty
        (If _ cond true false) ty -> do
            check cond $ Name $ Located (getLoc cond) BoolName
            check true ty
            check false ty
        (Case _ arg matches) ty -> do
            argTy <- infer arg
            for_ matches \(pat, body) -> do
                checkPattern pat argTy
                check body ty
        (Match loc matches) ty -> do
            n <- whenNothing (getArgCount matches) $ typeError $ ArgCountMismatch loc
            (patTypes, bodyTy) <- unwrapFn n ty
            for_ matches \(pats, body) -> do
                zipWithM_ checkPattern pats patTypes
                check body bodyTy
          where
            unwrapFn 0 = pure . ([],)
            unwrapFn n =
                monoLayer Out >=> \case
                    MLFn _ from to -> first (from :) <$> unwrapFn (pred n) to
                    MLUniVar loc' uni ->
                        lookupUniVar uni >>= \case
                            Right ty' -> unwrapFn n $ unMono ty'
                            Left _ -> do
                                argVars <- replicateM n freshUniVar'
                                bodyVar <- freshUniVar'
                                solveUniVar uni $ foldr (MFn loc' . MUniVar loc') (MUniVar loc' bodyVar) argVars
                                pure (T.UniVar loc' <$> argVars, T.UniVar loc' bodyVar)
                    other -> typeError $ ArgCountMismatch $ getLoc other
        (List _ items) (Application (Name (Located _ ListName)) itemTy) -> for_ items (`check` itemTy)
        (E.Record _ row) ty -> do
            for_ (IsList.toList row) \(name, expr) ->
                deepLookup Record name ty >>= \case
                    Nothing -> typeError $ MissingField ty name
                    Just fieldTy -> check expr fieldTy
        expr (T.UniVar _ uni) ->
            lookupUniVar uni >>= \case
                Right ty -> check expr $ unMono ty
                Left _ -> do
                    newTy <- mono In =<< infer expr
                    lookupUniVar uni >>= \case
                        Left _ -> solveUniVar uni newTy
                        Right _ -> pass
        expr (Forall _ binder body) -> check expr =<< substitute Out binder.var body
        expr (Exists _ binder body) -> check expr =<< substitute In binder.var body
        -- todo: a case for do-notation
        expr ty -> do
            inferredTy <- infer expr
            subtype inferredTy ty

-- a helper function for matches
getArgCount :: [([Pat], Expr 'Fixity)] -> Maybe Int
getArgCount [] = Just 0
getArgCount ((firstPats, _) : matches) = argCount <$ guard (all ((== argCount) . length . fst) matches)
  where
    argCount = length firstPats

checkBinding :: InfEffs es => Binding 'Fixity -> TypeDT -> Eff es ()
checkBinding binding ty = case binding of
    FunctionB _ args body -> check (foldr (Lambda (getLoc binding)) body args) ty
    ValueB pat body -> scoped $ checkPattern pat ty >> check body ty

checkPattern :: (InfEffs es, Declare :> es) => Pat -> TypeDT -> Eff es ()
checkPattern = \cases
    -- we need this case, since inferPattern only infers monotypes for var patterns
    (VarP name) ty -> updateSig name ty
    -- we probably do need a case for ConstructorP for the same reason
    (VariantP name arg) ty ->
        deepLookup Variant name ty >>= \case
            Nothing -> typeError $ MissingVariant ty name
            Just argTy -> checkPattern arg argTy
    (RecordP _ patRow) ty -> do
        for_ (IsList.toList patRow) \(name, pat) ->
            deepLookup Record name ty >>= \case
                Nothing -> typeError $ MissingField ty name
                Just fieldTy -> checkPattern pat fieldTy
    pat ty -> do
        inferredTy <- inferPattern pat
        subtype inferredTy ty

infer :: InfEffs es => Expr 'Fixity -> Eff es TypeDT
infer =
    scoped . \case
        Name name -> lookupSig name
        E.Variant name -> do
            let loc = getLoc name
            var <- freshUniVar loc
            rowVar <- freshUniVar loc
            -- #a -> [Name #a | #r]
            pure $ Function loc var (VariantT loc $ ExtRow (fromList [(name, var)]) rowVar)
        app@(Application f x) -> do
            fTy <- infer f
            inferApp (getLoc app) fTy x
        TypeApplication expr tyArg -> do
            infer expr >>= \case
                Forall _ binder body -> do
                    Subst{var, result} <- substitute' In binder.var body
                    subtype var $ cast tyArg
                    pure result
                ty -> typeError $ NoVisibleTypeArgument expr tyArg ty
        Lambda loc arg body -> do
            argTy <- inferPattern arg
            Function loc argTy <$> infer body
        -- chances are, I'd want to add some specific error messages or context for wildcard lambdas
        -- for now, they are just desugared to normal lambdas before inference
        WildcardLambda loc args body -> infer $ foldr (Lambda loc . VarP) body args
        Let _ binding body -> do
            declareAll =<< inferBinding binding
            infer body
        LetRec loc bindings body -> do
            declareAll =<< (inferDecls . map (\b -> D.Value loc b []) . NE.toList) bindings
            infer body
        Annotation expr ty -> cast ty <$ check expr (cast ty)
        If loc cond true false -> do
            check cond $ Name $ Located loc BoolName
            result <- fmap unMono . mono In =<< infer true
            check false result
            pure result
        Case loc arg matches -> do
            argTy <- infer arg
            result <- freshUniVar loc
            for_ matches \(pat, body) -> do
                checkPattern pat argTy
                check body result
            pure result
        Match loc [] -> typeError $ EmptyMatch loc
        Match loc matches@(_ : _) -> do
            argCount <- case getArgCount matches of
                Just argCount -> pure argCount
                Nothing -> typeError $ ArgCountMismatch loc
            result <- freshUniVar loc
            patTypes <- replicateM argCount (freshUniVar loc)
            for_ matches \(pats, body) -> do
                zipWithM_ checkPattern pats patTypes
                check body result
            pure $ foldr (Function loc) result patTypes
        List loc items -> do
            itemTy <- freshUniVar loc
            traverse_ (`check` itemTy) items
            pure $ Application (Name $ Located loc ListName) itemTy
        E.Record loc row -> RecordT loc . NoExtRow <$> traverse infer row
        RecordLens loc fields -> do
            recordParts <- for fields \field -> do
                rowVar <- freshUniVar loc
                pure \nested -> RecordT loc $ ExtRow (one (field, nested)) rowVar
            let mkNestedRecord = foldr1 (.) recordParts
            a <- freshUniVar loc
            b <- freshUniVar loc
            pure $
                Name (Located loc LensName)
                    `Application` mkNestedRecord a
                    `Application` mkNestedRecord b
                    `Application` a
                    `Application` b
        Do loc _ _ -> internalError loc "do-notation is not supported yet"
        Literal (Located loc lit) -> pure $ Name . Located loc $ case lit of
            IntLiteral num
                | num >= 0 -> NatName
                | otherwise -> IntName
            TextLiteral _ -> TextName
            CharLiteral _ -> TextName -- huh?
        v@Var{} -> pure . Name $ Located (getLoc v) TypeName
        f@Function{} -> pure . Name $ Located (getLoc f) TypeName
        f@Forall{} -> pure . Name $ Located (getLoc f) TypeName
        e@Exists{} -> pure . Name $ Located (getLoc e) TypeName
        v@VariantT{} -> pure . Name $ Located (getLoc v) TypeName
        r@RecordT{} -> pure . Name $ Located (getLoc r) TypeName

inferApp :: InfEffs es => Loc -> TypeDT -> Expr 'Fixity -> Eff es TypeDT
inferApp appLoc fTy arg = do
    monoLayer In fTy >>= \case
        MLUniVar loc uni -> do
            from <- infer arg
            to <- freshUniVar loc
            to <$ subtype (T.UniVar loc uni) (Function loc from to)
        MLFn _ from to -> do
            to <$ check arg from
        _ -> typeError $ NotAFunction appLoc fTy

-- infers the type of a function / variables in a pattern
-- does not implicitly declare anything
inferBinding :: InfEffs es => Binding 'Fixity -> Eff es (HashMap Name TypeDT)
inferBinding =
    scoped . generaliseAll . \case
        ValueB pat body -> do
            (patTy, bodyTy) <- do
                patTy <- inferPattern pat
                bodyTy <- infer body
                pure (patTy, bodyTy)
            subtype patTy bodyTy
            checkPattern pat bodyTy
            traverse lookupSig (HashMap.fromList $ (\x -> (x, x)) <$> collectNamesInPat pat)
        binding@(FunctionB name args body) -> do
            -- note: we can only infer monotypes for recursive functions
            -- while checking the body, the function itself is assigned a univar
            -- in the end, we check that the inferred type is compatible with the one in the univar (inferred from recursive calls)
            uni <- freshUniVar'
            updateSig name $ T.UniVar (getLoc binding) uni
            argTypes <- traverse inferPattern args
            bodyTy <- infer body
            let ty = foldr (Function $ getLoc binding) bodyTy argTypes
            -- since we can still infer higher-rank types for non-recursive functions,
            -- we only need the subtype check when the univar is solved, i.e. when the
            -- function contains any recursive calls at all
            withUniVar uni (subtype ty . unMono)
            pure $ HashMap.singleton name ty

inferPattern :: (InfEffs es, Declare :> es) => Pat -> Eff es TypeDT
inferPattern = \case
    VarP name -> do
        uni <- freshUniVar $ getLoc name
        updateSig name uni
        pure uni
    WildcardP loc _ -> freshUniVar loc
    AnnotationP pat ty -> cast ty <$ checkPattern pat (cast ty)
    p@(ConstructorP name args) -> do
        (resultType, argTypes) <- conArgTypes name
        unless (length argTypes == length args) $
            typeError $
                ArgCountMismatchPattern p (length argTypes) (length args)
        zipWithM_ checkPattern args argTypes
        pure resultType
    ListP loc pats -> do
        result <- freshUniVar loc
        traverse_ (`checkPattern` result) pats
        pure $ Application (Name $ Located loc ListName) result
    v@(VariantP name arg) -> do
        argTy <- inferPattern arg
        VariantT (getLoc v) . ExtRow (fromList [(name, argTy)]) <$> freshUniVar (getLoc v)
    RecordP loc row -> do
        typeRow <- traverse inferPattern row
        RecordT loc . ExtRow typeRow <$> freshUniVar loc
    LiteralP (Located loc lit) -> pure $ Name . Located loc $ case lit of
        IntLiteral num
            | num >= 0 -> NatName
            | otherwise -> IntName
        TextLiteral _ -> TextName
        CharLiteral _ -> TextName -- huh?
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
            MLUniVar loc uni -> internalError loc $ "unexpected univar" <+> pretty uni <+> "in a constructor type"
            -- this kind of repetition is necwithUniVaressary to retain missing pattern warnings
            MLName name -> pure (Name name, [])
            MLApp lhs rhs -> pure (Application lhs rhs, [])
            MLVariant loc row -> pure (VariantT loc row, [])
            MLRecord loc row -> pure (RecordT loc row, [])
            MLSkolem skolem -> pure (T.Skolem skolem, [])
            MLVar var -> pure (Var var, [])

normalise :: InfEffs es => Eff es TypeDT -> Eff es (Type 'Fixity)
normalise = fmap runIdentity . normaliseAll . fmap Identity

-- gets rid of all univars
normaliseAll :: (Traversable t, InfEffs es) => Eff es (t TypeDT) -> Eff es (t (Type 'Fixity))
normaliseAll = generaliseAll {->=> skolemsToExists-} >=> traverse go
  where
    go :: InfEffs es => TypeDT -> Eff es (Type 'Fixity)
    go = \case
        T.UniVar loc uni ->
            lookupUniVar uni >>= \case
                Left _ -> internalError loc $ "dangling univar " <> pretty uni
                Right body -> go (unMono body)
        T.Skolem skolem -> internalError (getLoc skolem) $ "skolem " <> pretty (T.Skolem skolem) <> " remains in code"
        -- other cases could be eliminated by a type changing uniplate
        Application lhs rhs -> Application <$> go lhs <*> go rhs
        Function loc lhs rhs -> Function loc <$> go lhs <*> go rhs
        Forall loc var body -> Forall loc <$> goBinder var <*> go body
        Exists loc var body -> Exists loc <$> goBinder var <*> go body
        VariantT loc row -> VariantT loc <$> traverse go row
        RecordT loc row -> RecordT loc <$> traverse go row
        -- expression-only constructors are unsupported for now
        t@TypeApplication{} -> internalError (getLoc t) "type-level type applications are not supported yet"
        l@Lambda{} -> internalError (getLoc l) "type-level lambdas are not supported yet"
        w@WildcardLambda{} -> internalError (getLoc w) "type-level wildcard lambdas are not supported yet"
        l@Let{} -> internalError (getLoc l) "type-level let bindings are not supported yet"
        l@LetRec{} -> internalError (getLoc l) "type-level let rec bindings are not supported yet"
        c@Case{} -> internalError (getLoc c) "type-level case is not supported yet"
        m@Match{} -> internalError (getLoc m) "type-level match is not supported yet"
        i@If{} -> internalError (getLoc i) "type-level lambdas if not supported yet"
        a@Annotation{} -> internalError (getLoc a) "type-level annotations are not supported yet"
        r@E.Record{} -> internalError (getLoc r) "type-level records are not supported yet"
        l@List{} -> internalError (getLoc l) "type-level lists are not supported yet"
        d@Do{} -> internalError (getLoc d) "type-level do blocks are not supported yet"
        -- and these are just boilerplate
        Name name -> pure $ Name name
        RecordLens loc name -> pure $ RecordLens loc name
        E.Variant name -> pure $ E.Variant name
        Literal lit -> pure $ Literal lit
        Var var -> pure $ Var var
    goBinder binder = VarBinder binder.var <$> traverse go binder.kind
