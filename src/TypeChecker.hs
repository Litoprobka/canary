{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
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

import Common
import Data.Foldable1 (foldr1)
import Data.HashMap.Strict qualified as HashMap
import Data.HashSet qualified as HashSet
import Data.List.NonEmpty qualified as NE
import Data.Traversable (for)
import Diagnostic (Diagnose)
import Effectful
import Effectful.State.Static.Local (State, gets, modify, runState)
import GHC.IsList qualified as IsList
import LensyUniplate
import NameGen
import LangPrelude hiding (Type, bool)
import Syntax
import Syntax.Declaration qualified as D
import Syntax.Expression qualified as E
import Syntax.Pattern qualified as P
import Syntax.Row (ExtRow (..))
import Syntax.Row qualified as Row
import Syntax.Type qualified as T
import TypeChecker.Backend

typecheck
    :: (NameGen :> es, Diagnose :> es)
    => HashMap Name (Type' 'Fixity) -- imports; note that the types may not be incomplete
    -> Builtins Name
    -> [Declaration 'Fixity]
    -> Eff es (HashMap Name (Type' 'Fixity)) -- type checking doesn't add anything new to the AST, so we reuse 'Fixity for simplicity
typecheck env builtins decls = run (Right <$> env) builtins $ normaliseAll $ inferDecls decls

-- finds all type parameters used in a type and creates corresponding forall clauses
inferTypeVars :: Type' 'Fixity -> Type' 'Fixity
inferTypeVars ty = uncurry (foldr (T.Forall $ getLoc ty)) . second snd . runPureEff . runState (HashSet.empty, HashSet.empty) . go $ ty
  where
    go :: Type' 'Fixity -> Eff '[State (HashSet Name, HashSet Name)] (Type' 'Fixity)
    go = transformM T.uniplate \case
        T.Var var -> do
            isNew <- not . HashSet.member var <$> gets @(HashSet Name, HashSet Name) snd
            when isNew $ modify @(HashSet Name, HashSet Name) (second $ HashSet.insert var)
            pure $ T.Var var
        forall_@(T.Forall _ var _) -> forall_ <$ modify @(HashSet Name, HashSet Name) (first $ HashSet.insert var)
        exists_@(T.Exists _ var _) -> exists_ <$ modify @(HashSet Name, HashSet Name) (first $ HashSet.insert var)
        other -> pure other

-- | check / infer types of a list of declarations that may reference each other
inferDecls :: InfEffs es => [Declaration 'Fixity] -> Eff es (HashMap Name Type)
inferDecls decls = do
    traverse_ updateTopLevel decls
    let (values, sigs) = second (fmap (cast uniplateCast) . HashMap.fromList) $ foldr getValueDecls ([], []) decls
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
                typeMap <- normaliseAll $ inferBinding binding -- todo: true top level should be separated from the parent scopes
                fmap (cast uniplateCast) typeMap <$ declareTopLevel typeMap
  where
    updateTopLevel = \case
        D.Signature _ name sig ->
            modify \s -> s{topLevel = HashMap.insert name (Right $ inferTypeVars sig) s.topLevel}
        D.Value _ binding@(E.FunctionBinding name _ _) locals -> insertBinding name binding locals
        D.Value _ binding@(E.ValueBinding (P.Var name) _) locals -> insertBinding name binding locals
        D.Value _ E.ValueBinding{} _ -> pass -- todo
        D.Type _ name vars constrs ->
            for_ (mkConstrSigs name vars constrs) \(con, sig) ->
                modify \s -> s{topLevel = HashMap.insert con (Right sig) s.topLevel}
        D.Alias{} -> pass
        D.Fixity{} -> pass

    insertBinding name binding locals =
        let closure = UninferredType $ scoped do
                declareAll =<< inferDecls locals
                nameTypePairs <- topLevelScope $ normaliseAll $ inferBinding binding
                declareTopLevel nameTypePairs
                case HashMap.lookup name nameTypePairs of
                    -- this can only happen if `inferBinding` returns an incorrect map of types
                    Nothing -> typeError $ Internal (getLoc name) $ "type closure for" <+> pretty name <+> "didn't infer its type"
                    Just ty -> pure ty
         in modify \s ->
                s{topLevel = HashMap.insertWith (\_ x -> x) name (Left closure) s.topLevel}

    getValueDecls decl (values, sigs) = case decl of
        D.Value _ binding locals -> ((binding, locals) : values, sigs)
        D.Signature _ name sig -> (values, (name, sig) : sigs)
        D.Type _ name vars constrs -> (values, mkConstrSigs name vars constrs ++ sigs)
        D.Alias{} -> (values, sigs)
        D.Fixity{} -> (values, sigs)

    mkConstrSigs :: Name -> [Name] -> [Constructor 'Fixity] -> [(Name, Type' 'Fixity)]
    mkConstrSigs name vars constrs =
        constrs <&> \(D.Constructor loc con params) ->
            ( con
            , foldr (T.Forall loc) (foldr (T.Function loc) fullType params) vars
            )
      where
        fullType = foldl' T.Application (T.Name name) (T.Var <$> vars)

subtype :: InfEffs es => Type -> Type -> Eff es ()
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
            -- some kind of kind system is needed to track variance and prevent stuff like `Maybe a b`
            -- higher-kinded types are also problematic when it comes to variance, i.e.
            -- is `f a` a subtype of `f b` when a is `a` subtype of `b` or the other way around?
            --
            -- QuickLook just assumes that all constructors are invariant and -> is a special case
            subtype lhs lhs'
            subtype rhs rhs'
        (MLVariant locL lhs) (MLVariant locR rhs) -> rowCase Variant (locL, lhs) (locR, rhs)
        (MLRecord locL lhs) (MLRecord locR rhs) -> rowCase Record (locL, lhs) (locR, rhs)
        (MLVar var) _ -> typeError $ Internal (getLoc var) $ "dangling type variable" <+> pretty var
        _ (MLVar var) -> typeError $ Internal (getLoc var) $ "dangling type variable" <+> pretty var
        lhs rhs -> typeError $ NotASubtype (unMonoLayer lhs) (unMonoLayer rhs) Nothing

    rowCase :: InfEffs es => RecordOrVariant -> (Loc, ExtRow Type) -> (Loc, ExtRow Type) -> Eff es ()
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

check :: InfEffs es => Expr -> Type -> Eff es ()
check e type_ = scoped $ match e type_
  where
    match = \cases
        -- the cases for E.Name and E.Constructor are redundant, since
        -- `infer` just looks up their types anyway
        (E.Lambda _ arg body) (T.Function _ from to) -> scoped do
            -- `checkPattern` updates signatures of all mentioned variables
            checkPattern arg from
            check body to
        (E.Annotation expr annTy) ty -> do
            check expr $ cast uniplateCast annTy
            subtype (cast uniplateCast annTy) ty
        (E.If _ cond true false) ty -> do
            check cond $ T.Name $ Located (getLoc cond) BoolName
            check true ty
            check false ty
        (E.Case _ arg matches) ty -> do
            argTy <- infer arg
            for_ matches \(pat, body) -> do
                checkPattern pat argTy
                check body ty
        (E.Match loc matches) ty -> do
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
        (E.List _ items) (T.Application (T.Name (Located _ ListName)) itemTy) -> for_ items (`check` itemTy)
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
        expr (T.Forall _ var body) -> check expr =<< substitute Out var body
        expr (T.Exists _ var body) -> check expr =<< substitute In var body
        expr ty -> do
            inferredTy <- infer expr
            subtype inferredTy ty

-- a helper function for matches
getArgCount :: [([Pat], Expr)] -> Maybe Int
getArgCount [] = Just 0
getArgCount ((firstPats, _) : matches) = argCount <$ guard (all ((== argCount) . length . fst) matches)
  where
    argCount = length firstPats

checkBinding :: InfEffs es => Binding 'Fixity -> Type -> Eff es ()
checkBinding binding ty = case binding of
    E.FunctionBinding _ args body -> check (foldr (E.Lambda (getLoc binding)) body args) ty
    E.ValueBinding pat body -> scoped $ checkPattern pat ty >> check body ty

checkPattern :: (InfEffs es, Declare :> es) => Pat -> Type -> Eff es ()
checkPattern = \cases
    -- we need this case, since inferPattern only infers monotypes for var patterns
    (P.Var name) ty -> updateSig name ty
    -- we probably do need a case for P.Constructor for the same reason
    (P.Variant name arg) ty ->
        deepLookup Variant name ty >>= \case
            Nothing -> typeError $ MissingVariant ty name
            Just argTy -> checkPattern arg argTy
    (P.Record _ patRow) ty -> do
        for_ (IsList.toList patRow) \(name, pat) ->
            deepLookup Record name ty >>= \case
                Nothing -> typeError $ MissingField ty name
                Just fieldTy -> checkPattern pat fieldTy
    -- todo: a case for do-notation
    pat ty -> do
        inferredTy <- inferPattern pat
        subtype inferredTy ty

infer :: InfEffs es => Expr -> Eff es Type
infer =
    scoped . \case
        E.Name name -> lookupSig name
        E.Constructor name -> lookupSig name
        E.Variant name -> do
            let loc = getLoc name
            var <- freshUniVar loc
            rowVar <- freshUniVar loc
            -- #a -> [Name #a | #r]
            pure $ T.Function loc var (T.Variant loc $ ExtRow (fromList [(name, var)]) rowVar)
        app@(E.Application f x) -> do
            fTy <- infer f
            inferApp (getLoc app) fTy x
        E.Lambda loc arg body -> do
            argTy <- inferPattern arg
            T.Function loc argTy <$> infer body
        -- chances are, I'd want to add some specific error messages or context for wildcard lambdas
        -- for now, they are just desugared to normal lambdas before inference
        E.WildcardLambda loc args body -> infer $ foldr (E.Lambda loc . P.Var) body args
        E.Let _ binding body -> do
            declareAll =<< inferBinding binding
            infer body
        E.LetRec loc bindings body -> do
            declareAll =<< (inferDecls . map (\b -> D.Value loc b []) . NE.toList) bindings
            infer body
        E.Annotation expr ty -> cast uniplateCast ty <$ check expr (cast uniplateCast ty)
        E.If loc cond true false -> do
            check cond $ T.Name $ Located loc BoolName
            result <- fmap unMono . mono In =<< infer true
            check false result
            pure result
        E.Case loc arg matches -> do
            argTy <- infer arg
            result <- freshUniVar loc
            for_ matches \(pat, body) -> do
                checkPattern pat argTy
                check body result
            pure result
        E.Match loc [] -> typeError $ EmptyMatch loc
        E.Match loc matches@((firstPats, firstBody) : rest) -> do
            -- NOTE: this implementation is biased towards the first match
            bodyType <- fmap unMono . mono In =<< infer firstBody
            patTypes <- traverse inferPattern firstPats
            whenNothing_ (getArgCount matches) $ typeError $ ArgCountMismatch loc
            for_ rest \(pats, body) -> do
                zipWithM_ checkPattern pats patTypes
                check body bodyType
            pure $ foldr (T.Function loc) bodyType patTypes
        E.List loc items -> do
            itemTy <- freshUniVar loc
            traverse_ (`check` itemTy) items
            pure $ T.Application (T.Name $ Located loc ListName) itemTy
        E.Record loc row -> T.Record loc . NoExtRow <$> traverse infer row
        E.RecordLens loc fields -> do
            recordParts <- for fields \field -> do
                rowVar <- freshUniVar loc
                pure \nested -> T.Record loc $ ExtRow (one (field, nested)) rowVar
            let mkNestedRecord = foldr1 (.) recordParts
            a <- freshUniVar loc
            b <- freshUniVar loc
            pure $
                T.Name (Located loc LensName)
                    `T.Application` mkNestedRecord a
                    `T.Application` mkNestedRecord b
                    `T.Application` a
                    `T.Application` b
        E.Do loc _ _ -> typeError $ Internal loc "do-notation is not supported yet"
        E.Literal (Located loc lit) -> pure $ T.Name . Located loc $ case lit of
            IntLiteral num
                | num >= 0 -> NatName
                | otherwise -> IntName
            TextLiteral _ -> TextName
            CharLiteral _ -> TextName -- huh?

inferApp :: InfEffs es => Loc -> Type -> Expr -> Eff es Type
inferApp appLoc fTy arg = do
    monoLayer In fTy >>= \case
        MLUniVar loc uni -> do
            from <- infer arg
            to <- freshUniVar loc
            to <$ subtype (T.UniVar loc uni) (T.Function loc from to)
        MLFn _ from to -> do
            to <$ check arg from
        _ -> typeError $ NotAFunction appLoc fTy

-- infers the type of a function / variables in a pattern
-- does not implicitly declare anything
inferBinding :: InfEffs es => Binding 'Fixity -> Eff es (HashMap Name Type)
inferBinding =
    scoped . generaliseAll . \case
        E.ValueBinding pat body -> do
            (patTy, bodyTy) <- do
                patTy <- inferPattern pat
                bodyTy <- infer body
                pure (patTy, bodyTy)
            subtype patTy bodyTy
            checkPattern pat bodyTy
            traverse lookupSig (HashMap.fromList $ (\x -> (x, x)) <$> collectNames pat)
        binding@(E.FunctionBinding name args body) -> do
            -- note: we can only infer monotypes for recursive functions
            -- while checking the body, the function itself is assigned a univar
            -- in the end, we check that the inferred type is compatible with the one in the univar (inferred from recursive calls)
            uni <- freshUniVar'
            updateSig name $ T.UniVar (getLoc binding) uni
            argTypes <- traverse inferPattern args
            bodyTy <- infer body
            let ty = foldr (T.Function $ getLoc binding) bodyTy argTypes
            -- since we can still infer higher-rank types for non-recursive functions,
            -- we only need the subtype check when the univar is solved, i.e. when the
            -- function contains any recursive calls at all
            withUniVar uni (subtype ty . unMono)
            pure $ HashMap.singleton name ty

-- \| collects all to-be-declared names in a pattern
collectNames :: Pattern p -> [NameAt p]
collectNames = \case
    P.Var name -> [name]
    P.Wildcard{} -> []
    P.Annotation pat _ -> collectNames pat
    P.Variant _ pat -> collectNames pat
    P.Constructor _ pats -> foldMap collectNames pats
    P.List _ pats -> foldMap collectNames pats
    P.Record _ row -> foldMap collectNames $ toList row
    P.Literal _ -> []

collectNamesInBinding :: Binding p -> [NameAt p]
collectNamesInBinding = \case
    E.FunctionBinding name _ _ -> [name]
    E.ValueBinding pat _ -> collectNames pat

inferPattern :: (InfEffs es, Declare :> es) => Pat -> Eff es Type
inferPattern = \case
    P.Var name -> do
        uni <- freshUniVar $ getLoc name
        updateSig name uni
        pure uni
    P.Wildcard loc _ -> freshUniVar loc
    P.Annotation pat ty -> cast uniplateCast ty <$ checkPattern pat (cast uniplateCast ty)
    p@(P.Constructor name args) -> do
        (resultType, argTypes) <- conArgTypes name
        unless (length argTypes == length args) $
            typeError $
                ArgCountMismatchPattern p (length argTypes) (length args)
        zipWithM_ checkPattern args argTypes
        pure resultType
    P.List loc pats -> do
        result <- freshUniVar loc
        traverse_ (`checkPattern` result) pats
        pure $ T.Application (T.Name $ Located loc ListName) result
    v@(P.Variant name arg) -> do
        argTy <- inferPattern arg
        T.Variant (getLoc v) . ExtRow (fromList [(name, argTy)]) <$> freshUniVar (getLoc v)
    P.Record loc row -> do
        typeRow <- traverse inferPattern row
        T.Record loc . ExtRow typeRow <$> freshUniVar loc
    P.Literal (Located loc lit) -> pure $ T.Name . Located loc $ case lit of
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
            MLUniVar loc uni -> typeError $ Internal loc $ "unexpected univar" <+> pretty uni <+> "in a constructor type"
            -- this kind of repetition is necwithUniVaressary to retain missing pattern warnings
            MLName name -> pure (T.Name name, [])
            MLApp lhs rhs -> pure (T.Application lhs rhs, [])
            MLVariant loc row -> pure (T.Variant loc row, [])
            MLRecord loc row -> pure (T.Record loc row, [])
            MLSkolem skolem -> pure (T.Skolem skolem, [])
            MLVar var -> pure (T.Var var, [])

normalise :: InfEffs es => Eff es Type -> Eff es (Type' 'Fixity)
normalise = fmap runIdentity . normaliseAll . fmap Identity

-- gets rid of all univars
normaliseAll :: (Traversable t, InfEffs es) => Eff es (t Type) -> Eff es (t (Type' 'Fixity))
normaliseAll = generaliseAll {->=> skolemsToExists-} >=> traverse go
  where
    go = transformM' (T.uniplate' coerce (error "univar in uniplate") (error "skolem in uniplate")) \case
        T.UniVar loc uni ->
            lookupUniVar uni >>= \case
                Left _ -> typeError $ Internal loc $ "dangling univar " <> pretty uni
                Right body -> Left <$> go (unMono body)
        T.Skolem skolem -> typeError $ Internal (getLoc skolem) $ "skolem " <> pretty (T.Skolem skolem) <> " remains in code"
        other -> pure $ Right other
