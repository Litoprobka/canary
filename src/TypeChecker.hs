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
    typecheck,
) where

import Common (Name)
import Common hiding (Name)
import Data.DList qualified as DList
import Data.Foldable1 (foldr1)
import Data.HashMap.Strict qualified as HashMap
import Data.List.NonEmpty qualified as NE
import Data.Traversable (for)
import Diagnostic (Diagnose, internalError)
import Effectful
import Effectful.State.Static.Local (State, get, gets, modify)
import GHC.IsList qualified as IsList
import Interpreter (ValueEnv)
import Interpreter qualified as V
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

typecheck
    :: (NameGen :> es, Diagnose :> es, State ValueEnv :> es)
    => HashMap Name Type' -- imports
    -> [Declaration 'Fixity]
    -> Eff es (HashMap Name Type') -- type checking doesn't add anything new to the AST
typecheck env decls = run env $ normaliseAll $ inferDecls decls

-- | check / infer types of a list of declarations that may reference each other
inferDecls :: InfEffs es => [Declaration 'Fixity] -> Eff es (HashMap Name TypeDT)
inferDecls decls = do
    -- ideally, all of this shuffling around should be moved to the dependency resolution pass
    typeNames <- DList.toList . fold <$> traverse updateTopLevel decls
    let (values, sigs') = second HashMap.fromList $ foldr getValueDecls ([], []) decls
    -- kind-checking all signatures
    sigs <- traverse typeFromTerm sigs'
    topLevel <- gets @InfState (.topLevel)
    let types = HashMap.compose topLevel $ HashMap.fromList $ (\x -> (x, x)) <$> typeNames
    (types <>) . (<> sigs) . fold <$> for values \(binding, locals) ->
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
                declareTopLevel typeMap
                pure typeMap
  where
    updateTopLevel (Located loc decl) = case decl of
        D.Signature name sig -> do
            sigV <- typeFromTerm sig
            modify \s -> s{topLevel = HashMap.insert name sigV s.topLevel}
            pure DList.empty
        D.Value{} -> pure DList.empty
        D.Type name binders constrs -> do
            modify @ValueEnv $ HashMap.insert name (V.TyCon name)
            typeKind <- mkTypeKind loc binders
            modify \s -> s{topLevel = HashMap.insert name typeKind s.topLevel}
            for_ (mkConstrSigs name binders constrs) \(con, sig) -> do
                sigV <- typeFromTerm sig
                modify \s -> s{topLevel = HashMap.insert con sigV s.topLevel}
            pure $ DList.singleton name
        D.GADT name mbKind constrs -> do
            modify @ValueEnv $ HashMap.insert name (V.TyCon name)
            kind <- maybe (pure $ type_ loc) typeFromTerm mbKind
            modify \s -> s{topLevel = HashMap.insert name kind s.topLevel}
            for_ constrs \con -> do
                conSig <- typeFromTerm con.sig
                modify \s ->
                    s{topLevel = HashMap.insert con.name conSig s.topLevel}
            pure $ DList.singleton name
    mkTypeKind loc = go
      where
        go [] = pure $ type_ loc
        go (binder : rest) = V.Function loc <$> typeFromTerm (binderKind binder) <*> go rest
    type_ :: Loc -> Type'
    type_ loc = V.TyCon (Located loc TypeName)

    getValueDecls (L decl) (values, sigs) = case decl of
        D.Value binding locals -> ((binding, locals) : values, sigs)
        D.Signature name sig -> (values, (name, sig) : sigs)
        D.Type name vars constrs -> (values, mkConstrSigs name vars constrs ++ sigs)
        D.GADT _ _ constrs -> (values, (constrs <&> \con -> (con.name, con.sig)) ++ sigs)

    mkConstrSigs :: Name -> [VarBinder 'Fixity] -> [Constructor 'Fixity] -> [(Name, Type 'Fixity)]
    mkConstrSigs name binders constrs =
        constrs <&> \(D.Constructor loc con params) ->
            ( con
            , foldr (\var -> Located loc . Forall var) (foldr (\lhs -> Located loc . Function lhs) (fullType loc) params) binders
            )
      where
        fullType loc = foldl' (\lhs -> Located loc . App lhs) (Located (getLoc name) $ Name name) (Located loc . Name . (.var) <$> binders)

typeFromTerm :: InfEffs es => Type 'Fixity -> Eff es Type'
typeFromTerm term = do
    check term $ V.TyCon (Located (getLoc term) TypeName)
    env <- get @ValueEnv
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
        (MLTyCon (Located _ NatName)) (MLTyCon (Located _ IntName)) -> pass
        (MLCon lhs lhsArgs) (MLCon rhs rhsArgs) -> do
            unless (lhs == rhs) $ typeError $ CannotUnify lhs rhs
            -- we assume that the arg count is correct
            zipWithM_ subtype lhsArgs rhsArgs
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
        (MLVariantT locL lhs) (MLVariantT locR rhs) -> rowCase Variant (locL, lhs) (locR, rhs)
        (MLRecordT locL lhs) (MLRecordT locR rhs) -> rowCase Record (locL, lhs) (locR, rhs)
        -- (MLVar var) _ -> internalError (getLoc var) $ "dangling type variable" <+> pretty var
        -- _ (MLVar var) -> internalError (getLoc var) $ "dangling type variable" <+> pretty var
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
check (Located loc e) type_ = scoped $ match e type_
  where
    match = \cases
        -- the case for E.Name is redundant, since
        -- `infer` just looks up its type anyway
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
        (List items) (V.TyCon (Located _ ListName) `V.App` itemTy) -> for_ items (`check` itemTy)
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
        expr (V.Forall _ _ closure) -> check (Located loc expr) =<< substitute Out closure
        expr (V.Exists _ _ closure) -> check (Located loc expr) =<< substitute In closure
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

checkBinding :: InfEffs es => Binding 'Fixity -> TypeDT -> Eff es ()
checkBinding binding ty = case binding of
    FunctionB _ args body -> check (foldr (\var -> Located (getLoc binding) . Lambda var) body args) ty
    ValueB pat body -> scoped $ checkPattern pat ty >> check body ty

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
        infer expr >>= \case
            V.Forall _ _ closure -> do
                Subst{var, result} <- substitute' In closure
                env <- get @ValueEnv
                tyArgV <- V.eval env tyArg
                subtype var tyArgV
                pure result
            ty -> typeError $ NoVisibleTypeArgument expr tyArg ty
    Lambda arg body -> do
        argTy <- inferPattern arg
        V.Function loc argTy <$> infer body
    -- chances are, I'd want to add some specific error messages or context for wildcard lambdas
    -- for now, they are just desugared to normal lambdas before inference
    WildcardLambda args body -> infer $ foldr (\var -> Located loc . Lambda (Located (getLoc var) $ VarP var)) body args
    Let binding body -> do
        declareAll =<< inferBinding binding
        infer body
    LetRec bindings body -> do
        declareAll =<< (inferDecls . map (\b -> Located loc $ D.Value b []) . NE.toList) bindings
        infer body
    (Annotation expr ty) -> do
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
        result <- freshUniVar loc
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
        pure type_
    Pi arg ty body -> do
        tyV <- typeFromTerm ty
        updateSig arg tyV
        check body type_
        pure type_
    VariantT row -> do
        traverse_ (`check` type_) row
        pure type_
    RecordT row -> do
        traverse_ (`check` type_) row
        pure type_
    Forall binder body -> scoped do
        kind <- maybe (freshUniVar loc) typeFromTerm binder.kind
        updateSig binder.var kind
        check body type_
        pure type_
    Exists binder body -> scoped do
        kind <- maybe (freshUniVar loc) typeFromTerm binder.kind
        updateSig binder.var kind
        check body type_
        pure type_
  where
    type_ = V.TyCon (Located loc TypeName)

inferApp :: InfEffs es => Loc -> TypeDT -> Expr 'Fixity -> Eff es TypeDT
inferApp appLoc fTy arg = do
    monoLayer In fTy >>= \case
        MLUniVar loc uni -> do
            from <- infer arg
            to <- freshUniVar loc
            to <$ subtype (V.UniVar loc uni) (V.Function loc from to)
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
            updateSig name $ V.UniVar (getLoc binding) uni
            argTypes <- traverse inferPattern args
            bodyTy <- infer body
            let ty = foldr (V.Function $ getLoc binding) bodyTy argTypes
            -- since we can still infer higher-rank types for non-recursive functions,
            -- we only need the subtype check when the univar is solved, i.e. when the
            -- function contains any recursive calls at all
            withUniVar uni (subtype ty . unMono)
            pure $ HashMap.singleton name ty

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
    LiteralP (Located _ lit) -> pure $ V.TyCon . Located loc $ case lit of
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
                -- univars should never appear as the rightmost argument of a value constructor type
                -- i.e. types of value constructors have the shape `a -> b -> c -> d -> ConcreteType a b c d`
                --
                -- solved univars cannot appear here either, since `lookupSig` on a pattern returns a type with no univars
                MLUniVar loc uni -> internalError loc $ "unexpected univar" <+> pretty uni <+> "in a constructor type"
                -- this kind of repetition is necessary to retain missing pattern warnings
                MLCon cname args -> pure (V.Con cname args, [])
                MLTyCon cname -> pure (V.TyCon cname, [])
                MLApp lhs rhs -> pure (V.App lhs rhs, [])
                MLVariantT loc _ -> internalError loc $ "unexpected variant type" <+> "in a constructor type"
                MLRecordT loc _ -> internalError loc $ "unexpected record type" <+> "in a constructor type"
                MLVariant{} -> internalError (getLoc name) $ "unexpected variant constructor" <+> "in a constructor type"
                MLRecord{} -> internalError (getLoc name) $ "unexpected record value" <+> "in a constructor type"
                MLLambda{} -> internalError (getLoc name) $ "unexpected lambda" <+> "in a constructor type"
                MLPrim{} -> internalError (getLoc name) $ "unexpected value" <+> "in a constructor type"
                MLPrimFunc{} -> internalError (getLoc name) $ "unexpected primitive function" <+> "in a constructor type"
                MLCase{} -> internalError (getLoc name) $ "unexpected case" <+> "in a constructor type"
                MLSkolem skolem -> pure (V.Skolem skolem, [])

-- MLVar var -> pure (Var var, [])

normalise :: InfEffs es => Eff es TypeDT -> Eff es Type'
normalise = fmap runIdentity . normaliseAll . fmap Identity

-- gets rid of all univars
normaliseAll :: (Traversable t, InfEffs es) => Eff es (t TypeDT) -> Eff es (t Type')
normaliseAll = generaliseAll >=> traverse (eval' <=< go . V.quote)
  where
    eval' :: InfEffs es => CoreTerm -> Eff es Type'
    eval' ty = do
        env <- get @ValueEnv
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
        C.Pi loc var ty body -> C.Pi loc var <$> go ty <*> go body
        -- this might produce incorrect results if we ever share a single forall in multiple places
        C.Forall loc var ty body -> C.Forall loc var <$> go ty <*> go body
        C.Exists loc var ty body -> C.Exists loc var <$> go ty <*> go body
        C.VariantT loc row -> C.VariantT loc <$> traverse go row
        C.RecordT loc row -> C.RecordT loc <$> traverse go row
        -- expression-only constructors are unsupported for now
        C.Lambda{} -> internalError Blank "type-level lambdas are not supported yet"
        C.Case{} -> internalError Blank "type-level case is not supported yet"
        C.Record{} -> internalError Blank "type-level records are not supported yet"
        -- and these are just boilerplate
        C.Name name -> pure $ C.Name name
        C.TyCon name -> pure $ C.TyCon name
        C.Con name args -> pure $ C.Con name args
        C.Variant name -> pure $ C.Variant name
        C.Literal lit -> pure $ C.Literal lit
        C.Let name _ _ -> internalError (getLoc name) "unexpected let in a quoted value"
