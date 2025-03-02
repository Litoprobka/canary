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
    normalise,
    InfState (..),
    InfEffs,
    Declare,
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
import Effectful.State.Static.Local (get, modify, modifyM)
import GHC.IsList qualified as IsList
import Eval qualified as V
import LangPrelude hiding (bool)
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

inferDeclaration :: InfEffs es => Declaration 'Fixity -> Eff es ()
inferDeclaration (Located loc decl) = case decl of
    D.Signature name sig -> do
        sigV <- typeFromTerm sig
        declareTopLevel' name sigV
    D.Type name binders constrs -> do
        withValues $ modify $ LMap.insert name (V.TyCon name)
        typeKind <- mkTypeKind binders
        declareTopLevel' name typeKind
        for_ (mkConstrSigs name binders constrs) \(con, sig) -> do
            sigV <- typeFromTerm sig
            declareTopLevel' con sigV
    D.GADT name mbKind constrs -> do
        withValues $ modify $ LMap.insert name (V.TyCon name)
        kind <- maybe (pure type_) typeFromTerm mbKind
        declareTopLevel' name kind
        for_ constrs \con -> do
            conSig <- typeFromTerm con.sig
            declareTopLevel' con.name conSig
    D.Value binding locals -> scoped do
        for_ locals \local -> do
            -- todo: what to do about type signatures
            inferDeclaration local
            withValues $ modifyM $ flip V.modifyEnv [local]
        relevantSigs <- Map.filterWithKey (\k _ -> k `elem` collectNamesInBinding binding) <$> withTypes get
        declareTopLevel =<< generaliseAll (checkBinding binding relevantSigs)
  where
    mkTypeKind = \case
        [] -> pure type_
        (binder : rest) -> V.Function loc <$> typeFromTerm (binderKind binder) <*> mkTypeKind rest
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

typeFromTerm :: InfEffs es => Type 'Fixity -> Eff es Type'
typeFromTerm term = do
    check term $ V.TyCon (Located (getLoc term) TypeName)
    env <- withValues get
    V.eval env term

subtype :: InfEffs es => TypeDT -> TypeDT -> Eff es ()
subtype lhs_ rhs_ = join $ match <$> monoLayer In lhs_ <*> monoLayer Out rhs_
  where
    match = \cases
        (MLTyCon lhs) (MLTyCon rhs) | lhs == rhs -> pass
        (MLUniVar _ lhs) (MLUniVar _ rhs) | lhs == rhs -> pass
        (MLSkolem lhs) (MLSkolem rhs) | lhs == rhs -> pass
        lhs (MLUniVar _ uni) -> solveOr (mono In $ unMonoLayer lhs) (subtype (unMonoLayer lhs) . unMono) uni
        (MLUniVar _ uni) rhs -> solveOr (mono Out $ unMonoLayer rhs) ((`subtype` unMonoLayer rhs) . unMono) uni
        (MLTyCon (L NatName)) (MLTyCon (L IntName)) -> pass
        lhs@(MLCon lhsCon lhsArgs) rhs@(MLCon rhsCon rhsArgs) -> do
            unless (lhsCon == rhsCon) $ typeError $ CannotUnify (unMonoLayer lhs) (unMonoLayer rhs)
            -- we assume that the arg count is correct
            zipWithM_ subtype lhsArgs rhsArgs
        (MLFn _ inl outl) (MLFn _ inr outr) -> do
            subtype inr inl
            subtype outl outr
        -- I'm not sure whether the subtyping between erased and non-erased arguments is right, since
        -- those types would have different runtime representations
        (MLQ _ Forall erasedl closurel) (MLQ _ Forall erasedr closurer) | subErased erasedr erasedl -> do
            subtype closurer.ty closurel.ty
            skolem <- freshSkolem $ toSimpleName closurel.var
            subtype (V.app closurel skolem) (V.app closurer skolem)
        (MLQ _ Exists erasedl closurel) (MLQ _ Exists erasedr closurer) | subErased erasedl erasedr -> do
            subtype closurel.ty closurer.ty
            skolem <- freshSkolem $ toSimpleName closurel.var
            subtype (V.app closurel skolem) (V.app closurer skolem)
        (MLFn _ inl outl) (MLQ _ Forall Retained closure) -> do
            subtype closure.ty inl
            skolem <- freshSkolem $ toSimpleName closure.var
            subtype outl (V.app closure skolem)
        (MLQ _ Forall Retained closure) (MLFn _ inr outr) -> do
            subtype inr closure.ty
            skolem <- freshSkolem $ toSimpleName closure.var
            subtype (V.app closure skolem) outr
        (MLApp lhs rhs) (MLApp lhs' rhs') -> do
            -- note that we assume the same variance for all type parameters
            -- seems like we need to track variance in kinds for this to work properly
            -- higher-kinded types are also problematic when it comes to variance, i.e.
            -- is `f a` a subtype of `f b` when a is `a` subtype of `b` or the other way around?
            --
            -- QuickLook just assumes that all constructors are invariant and -> is a special case
            subtype lhs lhs'
            subtype rhs rhs'
        (MLVariantT locL lhs) (MLVariantT locR rhs) -> rowCase Variant (locL, lhs) (locR, rhs)
        (MLRecordT locL lhs) (MLRecordT locR rhs) -> rowCase Record (locL, lhs) (locR, rhs)
        lhs rhs -> typeError $ NotASubtype (unMonoLayer lhs) (unMonoLayer rhs) Nothing

    -- (forall a -> ty) <: (foreach a -> ty)
    -- (some a ** ty) <: (exists a ** ty)
    subErased :: Erased -> Erased -> Bool
    subErased _ Erased = True
    subErased Retained Retained = True
    subErased Erased Retained = False

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
check (Located loc e) type_ = scoped $ match e type_
  where
    match = \cases
        -- the case for E.Name is redundant, since
        -- `infer` just looks up its type anyway
        (Lambda (L (VarP arg)) body) (V.Q _ Forall Visible Retained closure) -> scoped do
            updateSig arg closure.ty -- checkPattern arg closure.ty
            var <- freshSkolem (toSimpleName arg)
            withValues $ modify $ LMap.insert arg var
            check body (closure `V.app` var)
        (Lambda arg body) (V.Function _ from to) -> scoped do
            -- `checkPattern` updates signatures of all mentioned variables
            checkPattern arg from
            check body to
        (Annotation expr annTy) ty -> do
            annTyV <- typeFromTerm annTy
            check expr annTyV
            subtype annTyV ty
        (If cond true false) ty -> do
            check cond $ V.TyCon (Located (getLoc cond) BoolName)
            check true ty
            check false ty
        (Case arg matches) ty -> do
            argTy <- infer arg
            for_ matches \(pat, body) -> do
                checkPattern pat argTy
                check body ty
        (Match matches) ty -> do
            n <- whenNothing (getArgCount matches) $ typeError $ ArgCountMismatch loc
            (patTypes, bodyTy) <- unwrapFn n ty
            for_ matches \(pats, body) -> do
                zipWithM_ checkPattern pats patTypes
                check body bodyTy
          where
            unwrapFn 0 = pure . ([],)
            unwrapFn n =
                monoLayer Out >=> \case
                    -- todo: this should support Pi and dependent pattern matching
                    -- MLQ{} -> uhhh
                    MLFn _ from to -> first (from :) <$> unwrapFn (pred n) to
                    MLUniVar loc' uni ->
                        lookupUniVar uni >>= \case
                            Right ty' -> unwrapFn n $ unMono ty'
                            Left _ -> do
                                argVars <- replicateM n freshUniVar'
                                bodyVar <- freshUniVar'
                                solveUniVar uni $ foldr (MFn loc' . MUniVar loc') (MUniVar loc' bodyVar) argVars
                                pure (V.UniVar loc' <$> argVars, V.UniVar loc' bodyVar)
                    other -> typeError $ ArgCountMismatch $ getLoc other
        (List items) (V.TyCon (L ListName) `V.App` itemTy) -> for_ items (`check` itemTy)
        (E.Record row) ty -> do
            for_ (IsList.toList row) \(name, expr) ->
                deepLookup Record name ty >>= \case
                    Nothing -> typeError $ MissingField ty name
                    Just fieldTy -> check expr fieldTy
        expr (V.UniVar _ uni) ->
            lookupUniVar uni >>= \case
                Right ty -> check (Located loc expr) $ unMono ty
                Left _ -> do
                    newTy <- mono In =<< infer (Located loc expr)
                    lookupUniVar uni >>= \case
                        Left _ -> solveUniVar uni newTy
                        Right _ -> pass
        expr (V.Q _ Forall _vis _e closure) -> check (Located loc expr) =<< substitute Out closure
        expr (V.Q _ Exists _vis _e closure) -> check (Located loc expr) =<< substitute In closure
        -- todo: a case for do-notation
        expr ty -> do
            inferredTy <- infer (Located loc expr)
            subtype inferredTy ty

-- a helper function for matches
getArgCount :: [([Pat], Expr 'Fixity)] -> Maybe Int
getArgCount [] = Just 0
getArgCount ((firstPats, _) : matches) = argCount <$ guard (all ((== argCount) . length . fst) matches)
  where
    argCount = length firstPats

-- | given a map of related signatures, check or infer a declaration
checkBinding :: InfEffs es => Binding 'Fixity -> EnumMap Name TypeDT -> Eff es (EnumMap Name TypeDT)
checkBinding binding types = case binding of
    _ | Map.null types -> inferBinding binding
    FunctionB name args body -> case Map.lookup name types of
        Just ty -> Map.singleton name ty <$ check (foldr (\var -> Located (getLoc binding) . Lambda var) body args) ty
        Nothing -> inferBinding binding
    ValueB (L (VarP name)) body -> case Map.lookup name types of
        Just ty -> Map.singleton name ty <$ check body ty
        Nothing -> inferBinding binding
    ValueB pat _body -> do
        internalError (getLoc pat) "todo: type check destructuring bindings with partial signatures"

-- scoped $ checkPattern pat ty >> check body ty

checkPattern :: (InfEffs es, Declare :> es) => Pat -> TypeDT -> Eff es ()
checkPattern (Located ploc outerPat) ty = case outerPat of
    -- we need this case, since inferPattern only infers monotypes for var patterns
    VarP name -> updateSig name ty
    -- we probably do need a case for ConstructorP for the same reason
    VariantP name arg ->
        deepLookup Variant name ty >>= \case
            Nothing -> typeError $ MissingVariant ty name
            Just argTy -> checkPattern arg argTy
    RecordP patRow -> do
        for_ (IsList.toList patRow) \(name, pat) ->
            deepLookup Record name ty >>= \case
                Nothing -> typeError $ MissingField ty name
                Just fieldTy -> checkPattern pat fieldTy
    _ -> do
        inferredTy <- inferPattern $ Located ploc outerPat
        subtype inferredTy ty

infer :: InfEffs es => Expr 'Fixity -> Eff es TypeDT
infer (Located loc e) = scoped case e of
    Name name -> lookupSig name
    E.Variant name -> do
        var <- freshUniVar loc
        rowVar <- freshUniVar loc
        -- #a -> [Name #a | #r]
        pure $ V.Function loc var (V.VariantT loc $ ExtRow (fromList [(name, var)]) rowVar)
    App f x -> do
        fTy <- infer f
        inferApp loc fTy x
    TypeApp expr tyArg -> do
        ty <- infer expr
        inferTyApp expr ty tyArg
    Lambda arg body -> do
        argTy <- inferPattern arg
        V.Function loc argTy <$> infer body
    -- chances are, I'd want to add some specific error messages or context for wildcard lambdas
    -- for now, they are just desugared to normal lambdas before inference
    WildcardLambda args body -> infer $ foldr (\var -> Located loc . Lambda (Located (getLoc var) $ VarP var)) body args
    Let binding body -> do
        declareAll =<< inferBinding binding
        infer body
    LetRec _bindings _body -> internalError loc "todo: typecheck of recursive bindings is not supported yet"
         {- do
        declareAll =<< (inferDecls . map (\b -> Located loc $ D.Value b []) . NE.toList) bindings
        infer body -}
    Annotation expr ty -> do
        tyV <- typeFromTerm ty
        tyV <$ check expr tyV
    If cond true false -> do
        check cond $ V.TyCon (Located loc BoolName)
        result <- fmap unMono . mono In =<< infer true
        check false result
        pure result
    Case arg matches -> do
        argTy <- infer arg
        result <- freshUniVar loc
        for_ matches \(pat, body) -> do
            checkPattern pat argTy
            check body result
        pure result
    Match [] -> typeError $ EmptyMatch loc
    Match matches@(_ : _) -> do
        argCount <- case getArgCount matches of
            Just argCount -> pure argCount
            Nothing -> typeError $ ArgCountMismatch loc
        result <- freshUniVar loc -- alpha-conversion?
        patTypes <- replicateM argCount (freshUniVar loc)
        for_ matches \(pats, body) -> do
            zipWithM_ checkPattern pats patTypes
            check body result
        pure $ foldr (V.Function loc) result patTypes
    List items -> do
        itemTy <- freshUniVar loc
        traverse_ (`check` itemTy) items
        pure $ V.TyCon (Located loc ListName) `V.App` itemTy
    E.Record row -> V.RecordT loc . NoExtRow <$> traverse infer row
    RecordLens fields -> do
        recordParts <- for fields \field -> do
            rowVar <- freshUniVar loc
            pure \nested -> V.RecordT loc $ ExtRow (one (field, nested)) rowVar
        let mkNestedRecord = foldr1 (.) recordParts
        a <- freshUniVar loc
        b <- freshUniVar loc
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
        check lhs type_
        check rhs type_
        pure type_ -- alpha-conversion?
    Q _ _ _ binder body -> do
        tyV <- maybe (freshUniVar loc) typeFromTerm binder.kind
        updateSig binder.var tyV
        check body type_
        pure type_
    VariantT row -> do
        traverse_ (`check` type_) row
        pure type_
    RecordT row -> do
        traverse_ (`check` type_) row
        pure type_
  where
    type_ = V.TyCon (Located loc TypeName)

inferApp :: InfEffs es => Loc -> TypeDT -> Expr 'Fixity -> Eff es TypeDT
inferApp appLoc fTy arg = do
    monoLayer In fTy >>= \case
        -- todo: this case is not ideal if the univar is already solved with a concrete function type
        MLUniVar loc uni -> do
            from <- infer arg
            to <- freshUniVar loc
            env <- withValues get
            var <- freshName $ Located loc $ Name' "x"
            let closure = V.Closure{var, env, ty = from, body = V.quote to}
            to <$ subtype (V.UniVar loc uni) (V.Q loc Forall Visible Retained closure)
        MLFn _ from to -> do
            to <$ check arg from
        -- todo: special case for erased args
        MLQ _ Forall _e closure -> do
            env <- withValues get
            argV <- V.eval env arg
            V.app closure argV <$ check arg closure.ty
        _ -> typeError $ NotAFunction appLoc fTy

inferTyApp :: InfEffs es => Expr 'Fixity -> TypeDT -> Type 'Fixity -> Eff es TypeDT
inferTyApp expr ty tyArg = case ty of
    V.Q _ Forall Implicit _e closure -> do
        Subst{var, result} <- substitute' In closure
        env <- withValues get
        tyArgV <- V.eval env tyArg
        subtype var tyArgV
        pure result
    V.Q _ q Hidden _e closure -> do
        Subst{result} <- substitute' (qVariance q) closure
        inferTyApp expr result tyArg
    _ -> typeError $ NoVisibleTypeArgument expr tyArg ty
  where
    qVariance = \case
        Forall -> In
        Exists -> Out

-- infers the type of a function / variables in a pattern
-- does not implicitly declare anything
inferBinding :: InfEffs es => Binding 'Fixity -> Eff es (EnumMap Name TypeDT)
inferBinding =
    scoped . \case
        ValueB pat body -> do
            (patTy, bodyTy) <- do
                patTy <- inferPattern pat
                bodyTy <- infer body
                pure (patTy, bodyTy)
            subtype patTy bodyTy
            checkPattern pat bodyTy
            traverse lookupSig (Map.fromList $ (\x -> (x, x)) <$> collectNamesInPat pat)
        binding@(FunctionB name args body) -> do
            -- note: we can only infer monotypes for recursive functions
            -- while checking the body, the function itself is assigned a univar
            -- in the end, we check that the inferred type is compatible with the one in the univar (inferred from recursive calls)
            uni <- freshUniVar'
            updateSig name $ V.UniVar (getLoc binding) uni
            argTypes <- traverse inferPattern args
            bodyTy <- infer body
            let ty = foldr (V.Function $ getLoc binding) bodyTy argTypes
            -- since we can still infer higher-rank types for non-recursive functions,
            -- we only need the subtype check when the univar is solved, i.e. when the
            -- function contains any recursive calls at all
            withUniVar uni (subtype ty . unMono)
            pure $ Map.singleton name ty

inferPattern :: (InfEffs es, Declare :> es) => Pat -> Eff es TypeDT
inferPattern (Located loc p) = case p of
    VarP name -> do
        uni <- freshUniVar $ getLoc name
        updateSig name uni
        pure uni
    WildcardP _ -> freshUniVar loc
    (AnnotationP pat ty) -> do
        tyV <- typeFromTerm ty
        tyV <$ checkPattern pat tyV
    ConstructorP name args -> do
        (resultType, argTypes) <- conArgTypes name
        unless (length argTypes == length args) do
            typeError $ ArgCountMismatchPattern (Located loc p) (length argTypes) (length args)
        zipWithM_ checkPattern args argTypes
        pure resultType
    ListP pats -> do
        result <- freshUniVar loc
        traverse_ (`checkPattern` result) pats
        pure $ V.TyCon (Located loc ListName) `V.App` result
    VariantP name arg -> do
        argTy <- inferPattern arg
        V.VariantT loc . ExtRow (fromList [(name, argTy)]) <$> freshUniVar loc
    RecordP row -> do
        typeRow <- traverse inferPattern row
        V.RecordT loc . ExtRow typeRow <$> freshUniVar loc
    LiteralP (L lit) -> pure $ V.TyCon . Located loc $ case lit of
        IntLiteral num
            | num >= 0 -> NatName
            | otherwise -> IntName
        TextLiteral _ -> TextName
        CharLiteral _ -> CharName
  where
    -- conArgTypes and the zipM may be unified into a single function
    conArgTypes name = lookupSig name >>= go
      where
        go =
            monoLayer In >=> \case
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

normalise :: InfEffs es => Eff es TypeDT -> Eff es Type'
normalise = fmap runIdentity . normaliseAll . fmap Identity

-- gets rid of all univars
normaliseAll :: (Traversable t, InfEffs es) => Eff es (t TypeDT) -> Eff es (t Type')
normaliseAll = generaliseAll >=> traverse (eval' <=< go . V.quote)
  where
    eval' :: InfEffs es => CoreTerm -> Eff es Type'
    eval' ty = do
        env <- withValues get
        pure $ V.evalCore env ty

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
