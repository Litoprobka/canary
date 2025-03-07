{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE NoFieldSelectors #-}

module TypeChecker (
    run,
    infer,
    inferPattern,
    inferBinding,
    check,
    checkPattern,
    subtype,
    normalise,
    InfState (..),
    InfEffs,
    inferDeclaration,
) where

import Common (Name)
import Common hiding (Name)
import Data.EnumMap.Lazy qualified as LMap
import Data.EnumMap.Strict qualified as Map
import Data.Foldable1 (foldr1)
import Data.Traversable (for)
import Diagnostic (internalError)
import Effectful
import Effectful.State.Static.Local (State, get, modify, runState)
import Eval (ValueEnv)
import Eval qualified as V
import GHC.IsList qualified as IsList
import LangPrelude hiding (bool, unzip)
import NameGen
import Syntax
import Syntax.Core qualified as C
import Syntax.Declaration qualified as D
import Syntax.Row (ExtRow (..))
import Syntax.Row qualified as Row
import Syntax.Term hiding (Record, Variant)
import Syntax.Term qualified as E (Term_ (Record, Variant))
import TypeChecker.Backend

-- todo: properly handle where clauses
-- data Locality = Local | NonLocal

inferDeclaration :: InfEffs es => InfState -> Declaration 'Fixity -> Eff es (ValueEnv -> ValueEnv)
inferDeclaration env (Located loc decl) = case decl of
    D.Signature name sig -> do
        sigV <- typeFromTerm env sig
        modify $ Map.insert name sigV
        pure id
    D.Type name binders constrs -> do
        let envWithTy = define name (V.TyCon name) env
        typeKind <- mkTypeKind envWithTy binders
        modify $ Map.insert name typeKind
        for_ (mkConstrSigs name binders constrs) \(con, sig) -> do
            sigV <- typeFromTerm envWithTy sig
            modify $ Map.insert con sigV
        pure $ insertVal name (V.TyCon name)
    D.GADT name mbKind constrs -> do
        let envWithTy = define name (V.TyCon name) env
        do
            kind <- maybe (pure type_) (typeFromTerm envWithTy) mbKind
            modify $ Map.insert name kind
            for_ constrs \con -> do
                conSig <- typeFromTerm envWithTy con.sig
                modify $ Map.insert con.name conSig
        pure $ insertVal name (V.TyCon name)
    D.Value binding (_ : _) -> internalError (getLoc binding) "todo: proper support for where clauses"
    D.Value binding [] -> do
        sigs <- get
        let relevantSigs = collectNamesInBinding binding & mapMaybe (\k -> (k,) <$> Map.lookup k sigs) & Map.fromList
        typeMap <- generaliseAll env (\e -> checkBinding e binding relevantSigs)
        modify (typeMap <>)
        pure id
  where
    insertVal name val venv = venv{V.values = LMap.insert name val venv.values}

    mkTypeKind env' = \case
        [] -> pure type_
        (binder : rest) -> V.Function loc <$> typeFromTerm env' (binderKind binder) <*> mkTypeKind env' rest
    type_ = V.TyCon (Located loc TypeName)

    mkConstrSigs :: Name -> [VarBinder 'Fixity] -> [Constructor 'Fixity] -> [(Name, Type 'Fixity)]
    mkConstrSigs name binders constrs =
        constrs <&> \(D.Constructor loc' con params) ->
            ( con
            , foldr
                (\var -> Located loc' . Q Forall Implicit Erased var)
                (foldr (\lhs -> Located loc' . Function lhs) (fullType loc') params)
                binders
            )
      where
        fullType loc' = foldl' (\lhs -> Located loc' . App lhs) (Located (getLoc name) $ Name name) (Located loc' . Name . (.var) <$> binders)

typeFromTerm :: InfEffs es => InfState -> Type 'Fixity -> Eff es Type'
typeFromTerm env term = do
    check env term $ V.TyCon (Located (getLoc term) TypeName)
    V.eval env.values term

subtype :: InfEffs es => InfState -> TypeDT -> TypeDT -> Eff es ()
subtype env lhs_ rhs_ = join $ match <$> monoLayer env In lhs_ <*> monoLayer env Out rhs_
  where
    match = \cases
        (MLTyCon lhs) (MLTyCon rhs) | lhs == rhs -> pass
        (MLUniVar _ lhs) (MLUniVar _ rhs) | lhs == rhs -> pass
        (MLSkolem lhs) (MLSkolem rhs) | lhs == rhs -> pass
        lhs (MLUniVar _ uni) -> solveOr (mono env In $ unMonoLayer lhs) (subtype env (unMonoLayer lhs) . unMono) uni
        (MLUniVar _ uni) rhs -> solveOr (mono env Out $ unMonoLayer rhs) ((\l -> subtype env l (unMonoLayer rhs)) . unMono) uni
        lhs rhs@(MLSkolem skolem) -> do
            case LMap.lookup skolem env.values.skolems of
                Nothing -> typeError $ NotASubtype (unMonoLayer lhs) (unMonoLayer rhs) Nothing
                Just skolemTy -> subtype env (unMonoLayer lhs) skolemTy
        lhs@(MLSkolem skolem) rhs -> do
            case LMap.lookup skolem env.values.skolems of
                Nothing -> typeError $ NotASubtype (unMonoLayer lhs) (unMonoLayer rhs) Nothing
                Just skolemTy -> subtype env skolemTy (unMonoLayer rhs)
        (MLTyCon (L NatName)) (MLTyCon (L IntName)) -> pass
        lhs@(MLCon lhsCon lhsArgs) rhs@(MLCon rhsCon rhsArgs) -> do
            unless (lhsCon == rhsCon) $ typeError $ CannotUnify (unMonoLayer lhs) (unMonoLayer rhs)
            -- we assume that the arg count is correct
            zipWithM_ (subtype env) lhsArgs rhsArgs
        (MLFn _ inl outl) (MLFn _ inr outr) -> do
            subtype env inr inl
            subtype env outl outr
        -- I'm not sure whether the subtyping between erased and non-erased arguments is right, since
        -- those types would have different runtime representations
        (MLQ _ Forall erasedl closurel) (MLQ _ Forall erasedr closurer) | subErased erasedr erasedl -> do
            subtype env closurer.ty closurel.ty
            skolem <- freshSkolem env $ toSimpleName closurel.var
            subtype env (V.app closurel skolem) (V.app closurer skolem)
        (MLQ _ Exists erasedl closurel) (MLQ _ Exists erasedr closurer) | subErased erasedl erasedr -> do
            subtype env closurel.ty closurer.ty
            skolem <- freshSkolem env $ toSimpleName closurel.var
            subtype env (V.app closurel skolem) (V.app closurer skolem)
        (MLFn _ inl outl) (MLQ _ Forall Retained closure) -> do
            subtype env closure.ty inl
            skolem <- freshSkolem env $ toSimpleName closure.var
            subtype env outl (V.app closure skolem)
        (MLQ _ Forall Retained closure) (MLFn _ inr outr) -> do
            subtype env inr closure.ty
            skolem <- freshSkolem env $ toSimpleName closure.var
            subtype env (V.app closure skolem) outr
        (MLApp lhs rhs) (MLApp lhs' rhs') -> do
            -- note that we assume the same variance for all type parameters
            -- seems like we need to track variance in kinds for this to work properly
            -- higher-kinded types are also problematic when it comes to variance, i.e.
            -- is `f a` a subtype of `f b` when a is `a` subtype of `b` or the other way around?
            --
            -- QuickLook just assumes that all constructors are invariant and -> is a special case
            subtype env lhs lhs'
            subtype env rhs rhs'
        (MLVariantT locL lhs) (MLVariantT locR rhs) -> rowCase Variant (locL, lhs) (locR, rhs)
        (MLRecordT locL lhs) (MLRecordT locR rhs) -> rowCase Record (locL, lhs) (locR, rhs)
        lhs rhs -> typeError $ NotASubtype (unMonoLayer lhs) (unMonoLayer rhs) Nothing

    -- (forall a -> ty) <: (foreach a -> ty)
    -- (some a ** ty) <: (exists a ** ty)
    subErased :: Erased -> Erased -> Bool
    subErased _ Erased = True
    subErased Retained Retained = True
    subErased Erased Retained = False

    -- todo: this is absolute jank. We don't want {a, b} <: {a}
    rowCase :: InfEffs es => RecordOrVariant -> (Loc, ExtRow TypeDT) -> (Loc, ExtRow TypeDT) -> Eff es ()
    rowCase whatToMatch (locL, lhsRow) (locR, rhsRow) = do
        let con = conOf whatToMatch
        for_ (IsList.toList lhsRow.row) \(name, lhsTy) ->
            deepLookup env whatToMatch name (con locR rhsRow) >>= \case
                Nothing -> typeError $ NotASubtype (con locL lhsRow) (con locR rhsRow) (Just name)
                Just rhsTy -> subtype env lhsTy rhsTy
        -- if the lhs has an extension, it should be compatible with rhs without the already matched fields
        for_ (Row.extension lhsRow) \ext -> subtype env ext . con locL =<< diff env whatToMatch rhsRow lhsRow.row

    -- turns out it's different enough from `withUniVar`
    solveOr :: InfEffs es => Eff es Monotype -> (Monotype -> Eff es ()) -> UniVar -> Eff es ()
    solveOr solveWith whenSolved uni = lookupUniVar uni >>= either (const $ solveUniVar env uni =<< solveWith) whenSolved

check :: InfEffs es => InfState -> Expr 'Fixity -> TypeDT -> Eff es ()
check env (Located loc e) = match e
  where
    match = \cases
        -- the case for E.Name is redundant, since
        -- `infer` just looks up its type anyway
        (Lambda (L (VarP arg)) body) (V.Q _ Forall Visible Retained closure) -> do
            -- checkPattern arg closure.ty
            var <- freshSkolem env (toSimpleName arg)
            check (define arg var $ declare arg closure.ty env) body (closure `V.app` var)
        (Lambda arg body) (V.Function _ from to) -> do
            newTypes <- checkPattern env arg from
            check (env{locals = newTypes <> env.locals}) body to
        (Annotation expr annTy) ty -> do
            annTyV <- typeFromTerm env annTy
            check env expr annTyV
            subtype env annTyV ty
        (If cond true false) ty -> do
            check env cond $ V.TyCon (Located (getLoc cond) BoolName)
            check env true ty
            check env false ty
        (Case arg matches) ty -> do
            argTy <- infer env arg
            for_ matches \(pat, body) -> do
                typeMap <- checkPattern env pat argTy
                newValues <- case mbArgV of
                    Just argV -> localEquality (declareMany typeMap env) argV pat
                    Nothing -> pure env.values
                check (declareMany typeMap env{values = newValues}) body ty
          where
            -- a special case for matching on a var seems janky, but apparently that's how Idris does this
            mbArgV = case arg of
                L (Name name) -> Map.lookup name env.values.values
                _ -> Nothing
        (Match matches) ty -> do
            n <- whenNothing (getArgCount matches) $ typeError $ ArgCountMismatch loc
            (patTypes, bodyTy) <- unwrapFn n ty
            for_ matches \(pats, body) -> do
                typeMap <- fold <$> zipWithM (checkPattern env) pats patTypes
                check (declareMany typeMap env) body bodyTy
          where
            unwrapFn 0 = pure . ([],)
            unwrapFn n =
                monoLayer env Out >=> \case
                    -- todo: this should support Pi and dependent pattern matching
                    -- MLQ{} -> uhhh
                    MLFn _ from to -> first (from :) <$> unwrapFn (pred n) to
                    MLUniVar loc' uni ->
                        lookupUniVar uni >>= \case
                            Right ty' -> unwrapFn n $ unMono ty'
                            Left _ -> do
                                argVars <- replicateM n (freshUniVar' env)
                                bodyVar <- freshUniVar' env
                                solveUniVar env uni $ foldr (MFn loc' . MUniVar loc') (MUniVar loc' bodyVar) argVars
                                pure (V.UniVar loc' <$> argVars, V.UniVar loc' bodyVar)
                    other -> typeError $ ArgCountMismatch $ getLoc other
        (List items) (V.TyCon (L ListName) `V.App` itemTy) -> for_ items \item -> check env item itemTy
        (E.Record row) ty -> do
            for_ (IsList.toList row) \(name, expr) ->
                deepLookup env Record name ty >>= \case
                    Nothing -> typeError $ MissingField ty name
                    Just fieldTy -> check env expr fieldTy
        expr (V.UniVar _ uni) ->
            lookupUniVar uni >>= \case
                Right ty -> check env (Located loc expr) $ unMono ty
                Left _ -> do
                    newTy <- mono env In =<< infer env (Located loc expr)
                    lookupUniVar uni >>= \case
                        Left _ -> solveUniVar env uni newTy
                        Right _ -> pass
        _expr (V.Q _ Exists Visible _e _closure) -> internalError loc "dependent pairs are not supported yet"
        expr (V.Q _ Forall _vis _e closure) -> check env (Located loc expr) =<< substitute env Out closure
        expr (V.Q _ Exists _vis _e closure) -> check env (Located loc expr) =<< substitute env In closure
        -- todo: a case for do-notation
        expr ty -> do
            inferredTy <- infer env (Located loc expr)
            subtype env inferredTy ty

-- a helper function for matches
getArgCount :: [([Pat], Expr 'Fixity)] -> Maybe Int
getArgCount [] = Just 0
getArgCount ((firstPats, _) : matches) = argCount <$ guard (all ((== argCount) . length . fst) matches)
  where
    argCount = length firstPats

-- an implementation of depedendent pattern matching, pretty much
localEquality :: InfEffs es => InfState -> V.Value -> Pat -> Eff es ValueEnv
localEquality env val pat = do
    case val of
        V.Skolem skolem
            -- for now, we don't do anything if the skolem is already locally solved
            | LMap.member skolem env.values.skolems -> pure env.values
            | otherwise -> do
                (solvedTo, venv) <- runState env.values $ patToVal pat
                pure venv{V.skolems = LMap.insert skolem solvedTo $ V.skolems venv}
        _ -> pure env.values
  where
    patToVal :: InfEffs es => Pat -> Eff (State ValueEnv : es) V.Value
    patToVal (Located loc pat') = case pat' of
        VarP name -> do
            valToDefine <- freshSkolem env $ toSimpleName name
            modify \venv -> venv{V.values = LMap.insert name valToDefine env.values.values}
            pure valToDefine
        WildcardP name -> freshSkolem env $ Located loc $ Name' name -- todo: use SimpleName in WildcardP
        AnnotationP innerPat _ -> patToVal innerPat
        ConstructorP con args -> V.Con con <$> traverse patToVal args
        ListP args -> do
            argVs <- traverse patToVal args
            -- this is not the first time I write out the List desugaring, is it?
            pure $ foldr (\h t -> V.Con (Located loc ConsName) [h, t]) (V.Con (Located loc NilName) []) argVs
        VariantP con arg -> V.Variant con <$> patToVal arg
        RecordP row -> V.Record <$> traverse patToVal row
        LiteralP lit -> pure $ V.PrimValue lit

-- | given a map of related signatures, check or infer a declaration
checkBinding :: InfEffs es => InfState -> Binding 'Fixity -> EnumMap Name TypeDT -> Eff es (EnumMap Name TypeDT)
checkBinding env binding types = case binding of
    _ | Map.null types -> inferBinding env binding
    FunctionB name args body -> case Map.lookup name types of
        Just ty -> Map.singleton name ty <$ check env (foldr (\var -> Located (getLoc binding) . Lambda var) body args) ty
        Nothing -> inferBinding env binding
    ValueB (L (VarP name)) body -> case Map.lookup name types of
        Just ty -> Map.singleton name ty <$ check env body ty
        Nothing -> inferBinding env binding
    ValueB pat _body -> do
        internalError (getLoc pat) "todo: type check destructuring bindings with partial signatures"

-- check a pattern, returning all of the newly bound vars
checkPattern :: InfEffs es => InfState -> Pat -> TypeDT -> Eff es (EnumMap Name TypeDT)
checkPattern env (Located ploc outerPat) ty = case outerPat of
    -- we need this case, since inferPattern only infers monotypes for var patterns
    VarP name -> pure $ Map.singleton name ty
    -- we probably do need a case for ConstructorP for the same reason
    VariantP name arg ->
        deepLookup env Variant name ty >>= \case
            Nothing -> typeError $ MissingVariant ty name
            Just argTy -> checkPattern env arg argTy
    RecordP patRow -> do
        fold <$> for (IsList.toList patRow) \(name, pat) ->
            deepLookup env Record name ty >>= \case
                Nothing -> typeError $ MissingField ty name
                Just fieldTy -> checkPattern env pat fieldTy
    _ -> do
        (typeMap, inferredTy) <- inferPattern env $ Located ploc outerPat
        subtype env inferredTy ty
        pure typeMap

infer :: InfEffs es => InfState -> Expr 'Fixity -> Eff es TypeDT
infer env (Located loc e) = case e of
    Name name -> lookupSig env name
    E.Variant name -> do
        var <- freshUniVar env loc
        rowVar <- freshUniVar env loc
        -- #a -> [Name #a | #r]
        pure $ V.Function loc var (V.VariantT loc $ ExtRow (fromList [(name, var)]) rowVar)
    App f x -> do
        fTy <- infer env f
        inferApp env loc fTy x
    TypeApp expr tyArg -> do
        ty <- infer env expr
        inferTyApp env expr ty tyArg
    Lambda arg body -> do
        (typeMap, argTy) <- inferPattern env arg
        V.Function loc argTy <$> infer (declareMany typeMap env) body
    -- chances are, I'd want to add some specific error messages or context for wildcard lambdas
    -- for now, they are just desugared to normal lambdas before inference
    WildcardLambda args body -> infer env $ foldr (\var -> Located loc . Lambda (Located (getLoc var) $ VarP var)) body args
    Let binding body -> do
        typeMap <- inferBinding env binding
        infer (declareMany typeMap env) body
    LetRec _bindings _body -> internalError loc "todo: typecheck of recursive bindings is not supported yet"
    {- do
    declareAll =<< (inferDecls . map (\b -> Located loc $ D.Value b []) . NE.toList) bindings
    infer body -}
    Annotation expr ty -> do
        tyV <- typeFromTerm env ty
        tyV <$ check env expr tyV
    If cond true false -> do
        check env cond $ V.TyCon (Located loc BoolName)
        result <- fmap unMono . mono env In =<< infer env true
        check env false result
        pure result
    Case arg matches -> do
        argTy <- infer env arg
        result <- freshUniVar env loc
        for_ matches \(pat, body) -> do
            typeMap <- checkPattern env pat argTy
            -- inferring dependent pattern matching is probably unnecessary, but we do it anyway
            newValues <- case mbArgV of
                Just argV -> localEquality (declareMany typeMap env) argV pat
                Nothing -> pure env.values
            check (declareMany typeMap env{values = newValues}) body result
        pure result
      where
        mbArgV = case arg of
            L (Name name) -> Map.lookup name env.values.values
            _ -> Nothing
    Match [] -> typeError $ EmptyMatch loc
    Match matches@(_ : _) -> do
        argCount <- case getArgCount matches of
            Just argCount -> pure argCount
            Nothing -> typeError $ ArgCountMismatch loc
        result <- freshUniVar env loc
        patTypes <- replicateM argCount (freshUniVar env loc)
        for_ matches \(pats, body) -> do
            typeMap <- fold <$> zipWithM (checkPattern env) pats patTypes
            check (declareMany typeMap env) body result
        pure $ foldr (V.Function loc) result patTypes
    List items -> do
        itemTy <- freshUniVar env loc
        traverse_ (\item -> check env item itemTy) items
        pure $ V.TyCon (Located loc ListName) `V.App` itemTy
    E.Record row -> V.RecordT loc . NoExtRow <$> traverse (infer env) row
    RecordLens fields -> do
        recordParts <- for fields \field -> do
            rowVar <- freshUniVar env loc
            pure \nested -> V.RecordT loc $ ExtRow (one (field, nested)) rowVar
        let mkNestedRecord = foldr1 (.) recordParts
        a <- freshUniVar env loc
        b <- freshUniVar env loc
        pure $
            V.TyCon
                (Located loc LensName)
                `V.App` mkNestedRecord a
                `V.App` mkNestedRecord b
                `V.App` a
                `V.App` b
    Do _ _ -> internalError loc "do-notation is not supported yet"
    Literal (Located loc' lit) -> pure $ V.TyCon . Located loc' $ case lit of
        IntLiteral num
            | num >= 0 -> NatName
            | otherwise -> IntName
        TextLiteral _ -> TextName
        CharLiteral _ -> CharName
    Function lhs rhs -> do
        check env lhs type_
        check env rhs type_
        pure type_ -- alpha-conversion?
    Q _ _ _ binder body -> do
        tyV <- maybe (freshUniVar env loc) (typeFromTerm env) binder.kind
        check (define binder.var tyV env) body type_

        pure type_
    VariantT row -> do
        traverse_ (\v -> check env v type_) row
        pure type_
    RecordT row -> do
        traverse_ (\field -> check env field type_) row
        pure type_
  where
    type_ = V.TyCon (Located loc TypeName)

inferApp :: InfEffs es => InfState -> Loc -> TypeDT -> Expr 'Fixity -> Eff es TypeDT
inferApp env appLoc fTy arg = do
    monoLayer env In fTy >>= \case
        -- todo: this case is not ideal if the univar is already solved with a concrete function type
        MLUniVar loc uni -> do
            from <- infer env arg
            to <- freshUniVar env loc
            var <- freshName $ Located loc $ Name' "x"
            let closure = V.Closure{var, env = env.values, ty = from, body = V.quote to}
            to <$ subtype env (V.UniVar loc uni) (V.Q loc Forall Visible Retained closure)
        MLFn _ from to -> do
            to <$ check env arg from
        -- todo: special case for erased args
        MLQ _ Forall _e closure -> do
            argV <- V.eval env.values arg
            V.app closure argV <$ check env arg closure.ty
        _ -> typeError $ NotAFunction appLoc fTy

inferTyApp :: InfEffs es => InfState -> Expr 'Fixity -> TypeDT -> Type 'Fixity -> Eff es TypeDT
inferTyApp env expr ty tyArg = case ty of
    V.Q _ Forall Implicit _e closure -> do
        Subst{var, result} <- substitute' env In closure
        tyArgV <- V.eval env.values tyArg
        subtype env var tyArgV
        pure result
    V.Q _ q Hidden _e closure -> do
        Subst{result} <- substitute' env (qVariance q) closure
        inferTyApp env expr result tyArg
    _ -> typeError $ NoVisibleTypeArgument expr tyArg ty
  where
    qVariance = \case
        Forall -> In
        Exists -> Out

-- infers the type of a function / variables in a pattern
inferBinding :: InfEffs es => InfState -> Binding 'Fixity -> Eff es (EnumMap Name TypeDT)
inferBinding env = \case
    ValueB pat body -> do
        (typeMap, patTy) <- inferPattern env pat
        -- we need the pattern itself to be in scope in case the binding is recursive
        bodyTy <- infer (declareMany typeMap env) body
        subtype env patTy bodyTy
        pure typeMap
    binding@(FunctionB name args body) -> do
        -- note: we can only infer monotypes for recursive functions
        -- while checking the body, the function itself is assigned a univar
        -- in the end, we check that the inferred type is compatible with the one in the univar (inferred from recursive calls)
        uni <- freshUniVar' env
        let envWithName = declare name (V.UniVar (getLoc binding) uni) env

        (typeMap, argTypes) <- traverseFold (inferPattern envWithName) args
        bodyTy <- infer (declareMany typeMap envWithName) body

        -- todo: infer dependent functions
        let ty = foldr (V.Function $ getLoc binding) bodyTy argTypes
        -- since we can still infer higher-rank types for non-recursive functions,
        -- we only need the subtype check when the univar is solved, i.e. when the
        -- function contains any recursive calls at all
        withUniVar uni (subtype envWithName ty . unMono)
        pure $ Map.singleton name ty

inferPattern :: InfEffs es => InfState -> Pat -> Eff es (EnumMap Name TypeDT, TypeDT)
inferPattern env (Located loc p) = case p of
    VarP name -> do
        uni <- freshUniVar env $ getLoc name
        pure (Map.singleton name uni, uni)
    WildcardP _ -> (Map.empty,) <$> freshUniVar env loc
    (AnnotationP pat ty) -> do
        tyV <- typeFromTerm env ty
        (,tyV) <$> checkPattern env pat tyV
    ConstructorP name args -> do
        (resultType, argTypes) <- conArgTypes name
        unless (length argTypes == length args) do
            typeError $ ArgCountMismatchPattern (Located loc p) (length argTypes) (length args)
        typeMap <- fold <$> zipWithM (checkPattern env) args argTypes
        pure (typeMap, resultType)
    ListP pats -> do
        result <- freshUniVar env loc
        typeMap <- foldMapM (\item -> checkPattern env item result) pats
        let listTy = V.TyCon (Located loc ListName) `V.App` result
        pure (typeMap, listTy)
    VariantP name arg -> do
        (typeMap, argTy) <- inferPattern env arg
        ty <- V.VariantT loc . ExtRow (fromList [(name, argTy)]) <$> freshUniVar env loc
        pure (typeMap, ty)
    RecordP row -> do
        (typeMap, typeRow) <- traverseFold (inferPattern env) row
        ty <- V.RecordT loc . ExtRow typeRow <$> freshUniVar env loc
        pure (typeMap, ty)
    LiteralP (L lit) ->
        pure
            ( Map.empty
            , V.TyCon . Located loc $ case lit of
                IntLiteral num
                    | num >= 0 -> NatName
                    | otherwise -> IntName
                TextLiteral _ -> TextName
                CharLiteral _ -> CharName
            )
  where
    -- conArgTypes and the zipM may be unified into a single function
    conArgTypes name = lookupSig env name >>= go
      where
        go =
            monoLayer env In >=> \case
                MLFn _ arg rest -> second (arg :) <$> go rest
                MLQ loc' _ _ _ -> internalError loc' "dependent constructor types are not supported yet"
                -- MLQ _loc Forall _e closure -> second (closure.ty :) <$> go (V.closureBody closure) -- alpha-conversion?
                -- univars should never appear as the rightmost argument of a value constructor type
                -- i.e. types of value constructors have the shape `a -> b -> c -> d -> ConcreteType a b c d`
                --
                -- solved univars cannot appear here either, since `lookupSig` on a pattern returns a type with no univars
                MLUniVar loc' uni -> internalError loc' $ "unexpected univar" <+> pretty uni <+> "in a constructor type"
                -- this kind of repetition is necessary to retain missing pattern warnings
                MLCon cname args -> pure (V.Con cname args, [])
                MLTyCon cname -> pure (V.TyCon cname, [])
                MLApp lhs rhs -> pure (V.App lhs rhs, [])
                MLVariantT loc' _ -> internalError loc' $ "unexpected variant type" <+> "in a constructor type"
                MLRecordT loc' _ -> internalError loc' $ "unexpected record type" <+> "in a constructor type"
                MLVariant{} -> internalError (getLoc name) $ "unexpected variant constructor" <+> "in a constructor type"
                MLRecord{} -> internalError (getLoc name) $ "unexpected record value" <+> "in a constructor type"
                MLLambda{} -> internalError (getLoc name) $ "unexpected lambda" <+> "in a constructor type"
                MLPrim{} -> internalError (getLoc name) $ "unexpected value" <+> "in a constructor type"
                MLPrimFunc{} -> internalError (getLoc name) $ "unexpected primitive function" <+> "in a constructor type"
                MLCase{} -> internalError (getLoc name) $ "unexpected case" <+> "in a constructor type"
                MLSkolem skolem -> pure (V.Skolem skolem, [])

normalise :: InfEffs es => InfState -> (InfState -> Eff es TypeDT) -> Eff es Type'
normalise env = fmap runIdentity . normaliseAll env . (fmap . fmap) Identity

-- gets rid of all univars
normaliseAll :: (Traversable t, InfEffs es) => InfState -> (InfState -> Eff es (t TypeDT)) -> Eff es (t Type')
normaliseAll env = generaliseAll env >=> traverse (pure . V.evalCore env.values <=< go . V.quote)
  where
    go :: InfEffs es => CoreTerm -> Eff es CoreTerm
    go = \case
        C.UniVar loc uni ->
            lookupUniVar uni >>= \case
                Left _ -> internalError loc $ "dangling univar" <+> pretty uni
                Right body -> go $ V.quote (unMono body)
        C.Skolem skolem -> internalError (getLoc skolem) $ "skolem" <+> pretty (V.Skolem skolem) <+> "remains in code"
        -- other cases could be eliminated by a type changing uniplate
        C.App lhs rhs -> C.App <$> go lhs <*> go rhs
        C.Function loc lhs rhs -> C.Function loc <$> go lhs <*> go rhs
        -- this might produce incorrect results if we ever share a single forall in multiple places
        -- todo: convert a pi type to a lambda if its arg doesn't occur in its body
        -- I'm not sure whether there's a better way than traversing the entire body
        C.Q loc q v e var ty body -> C.Q loc q v e var <$> go ty <*> go body
        C.VariantT loc row -> C.VariantT loc <$> traverse go row
        C.RecordT loc row -> C.RecordT loc <$> traverse go row
        C.Lambda name body -> C.Lambda name <$> go body
        C.Case arg matches -> C.Case <$> go arg <*> traverse (traverse go) matches
        C.Record row -> C.Record <$> traverse go row
        -- and these are just boilerplate
        C.Name name -> pure $ C.Name name
        C.TyCon name -> pure $ C.TyCon name
        C.Con name args -> pure $ C.Con name args
        C.Variant name -> pure $ C.Variant name
        C.Literal lit -> pure $ C.Literal lit
        C.Let name _ _ -> internalError (getLoc name) "unexpected let in a quoted value"
