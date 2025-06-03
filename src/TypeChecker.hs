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
    Env (..),
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
import Effectful.Reader.Static (ask, asks)
import Effectful.State.Static.Local (State, execState, get, modify, put, runState)
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
import TypeChecker.TypeError

-- todo: properly handle where clauses
-- data Locality = Local | NonLocal

inferDeclaration :: InfEffs es => Declaration 'Fixity -> Eff es (ValueEnv -> ValueEnv)
inferDeclaration (Located loc decl) = case decl of
    D.Signature name sig -> do
        sigV <- typeFromTerm sig
        modify $ Map.insert name sigV
        pure id
    D.Type name binders constrs -> do
        local' (define name (V.TyCon name)) do
            typeKind <- mkTypeKind binders
            modify $ Map.insert name typeKind
            for_ (mkConstrSigs name binders constrs) \(con, sig) -> do
                sigV <- typeFromTerm sig
                modify $ Map.insert con sigV
            pure $ insertVal name (V.TyCon name)
    D.GADT name mbKind constrs -> do
        local' (define name (V.TyCon name)) do
            kind <- maybe (pure type_) typeFromTerm mbKind
            modify $ Map.insert name kind
            for_ constrs \con -> do
                checkGadtConstructor name con
                conSig <- typeFromTerm con.sig
                modify $ Map.insert con.name conSig
        pure $ insertVal name (V.TyCon name)
    D.Value binding (_ : _) -> internalError (getLoc binding) "todo: proper support for where clauses"
    D.Value binding [] -> do
        sigs <- get
        let relevantSigs = collectNamesInBinding binding & mapMaybe (\k -> (k,) <$> Map.lookup k sigs) & Map.fromList
        typeMap <- generaliseAll (checkBinding binding relevantSigs)
        modify (typeMap <>)
        pure id
  where
    insertVal name val venv = venv{V.values = LMap.insert name val venv.values}

    mkTypeKind = \case
        [] -> pure type_
        (binder : rest) -> fmap (Located loc) $ V.Function <$> (unLoc <$> typeFromTerm (binderKind binder)) <*> (unLoc <$> mkTypeKind rest) -- ewww
    type_ = V.TyCon (TypeName :@ loc) :@ loc

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

    checkGadtConstructor tyName con = case unwrapApp (fnResult con.sig) of
        (L (Name name), _)
            | name /= tyName -> typeError $ ConstructorReturnType{con = con.name, expected = tyName, returned = name}
            | otherwise -> pass
        (other, _) -> internalError (getLoc other) "something weird in a GADT consturctor type"
      where
        fnResult = \case
            L (Function _ rhs) -> fnResult rhs
            L (Q _ _ _ _ rhs) -> fnResult rhs
            other -> other
        unwrapApp = go []
          where
            go acc = \case
                L (App lhs rhs) -> go (rhs : acc) lhs
                other -> (other, acc)

typeFromTerm :: InfEffs es => Type 'Fixity -> Eff es Type'
typeFromTerm term = do
    values <- asks @Env (.values)
    check term $ V.TyCon (TypeName :@ getLoc term) :@ getLoc term
    Located (getLoc term) <$> V.eval values term

subtype :: InfEffs es => TypeDT -> TypeDT -> Eff es ()
subtype (lhs_ :@ locL) (rhs_ :@ locR) = join $ match <$> monoLayer' In lhs_ <*> monoLayer' Out rhs_
  where
    match = \cases
        (V.TyCon lhs) (V.TyCon rhs) | lhs == rhs -> pass
        (V.UniVar lhs) (V.UniVar rhs) | lhs == rhs -> pass
        (V.Skolem lhs) (V.Skolem rhs) | lhs == rhs -> pass
        lhs (V.UniVar uni) -> solveOr (Located locL <$> mono' In lhs) (subtype (lhs :@ locL) . unMono) uni
        (V.UniVar uni) rhs -> solveOr (Located locR <$> mono' Out rhs) ((`subtype` (rhs :@ locR)) . unMono) uni
        lhs rhs@(V.Skolem skolem) -> do
            skolems <- asks @Env ((.skolems) . (.values))
            case LMap.lookup skolem skolems of
                Nothing -> typeError $ NotASubtype (lhs :@ locL) (rhs :@ locR) Nothing
                Just skolemTy -> subtype (lhs :@ locL) (skolemTy :@ locR)
        lhs@(V.Skolem skolem) rhs -> do
            skolems <- asks @Env ((.skolems) . (.values))
            case LMap.lookup skolem skolems of
                Nothing -> typeError $ NotASubtype (lhs :@ locL) (rhs :@ locR) Nothing
                Just skolemTy -> subtype (skolemTy :@ locL) (rhs :@ locR)
        (V.TyCon (L NatName)) (V.TyCon (L IntName)) -> pass
        lhs@(V.Con lhsCon lhsArgs) rhs@(V.Con rhsCon rhsArgs) -> do
            unless (lhsCon == rhsCon) $ typeError $ CannotUnify (lhs :@ locL) (rhs :@ locR)
            -- we assume that the arg count is correct
            zipWithM_ subtypeLoc lhsArgs rhsArgs
        (V.Function inl outl) (V.Function inr outr) -> do
            subtypeFlipped inr inl
            subtypeLoc outl outr
        -- I'm not sure whether the subtyping between erased and non-erased arguments is right, since
        -- those types would have different runtime representations
        (V.Q Forall Visible erasedl closurel) (V.Q Forall Visible erasedr closurer) | subErased erasedr erasedl -> do
            subtypeFlipped closurer.ty closurel.ty
            skolem <- freshSkolem $ toSimpleName closurel.var
            subtypeLoc (V.app closurel skolem) (V.app closurer skolem)
        (V.Q Exists Visible erasedl closurel) (V.Q Exists Visible erasedr closurer) | subErased erasedl erasedr -> do
            subtypeLoc closurel.ty closurer.ty
            skolem <- freshSkolem $ toSimpleName closurel.var
            subtypeLoc (V.app closurel skolem) (V.app closurer skolem)
        (V.Function inl outl) (V.Q Forall Visible Retained closure) -> do
            subtypeFlipped closure.ty inl
            skolem <- freshSkolem $ toSimpleName closure.var
            subtypeLoc outl (V.app closure skolem)
        (V.Q Forall Visible Retained closure) (V.Function inr outr) -> do
            subtypeFlipped inr closure.ty
            skolem <- freshSkolem $ toSimpleName closure.var
            subtypeLoc (V.app closure skolem) outr
        (V.App lhs rhs) (V.App lhs' rhs') -> do
            -- note that we assume the same variance for all type parameters
            -- seems like we need to track variance in kinds for this to work properly
            -- higher-kinded types are also problematic when it comes to variance, i.e.
            -- is `f a` a subtype of `f b` when a is `a` subtype of `b` or the other way around?
            --
            -- QuickLook just assumes that all constructors are invariant and -> is a special case
            subtypeLoc lhs lhs'
            subtypeLoc rhs rhs'
        (V.VariantT lhs) (V.VariantT rhs) -> subtypeRows Variant lhs rhs
        (V.RecordT lhs) (V.RecordT rhs) -> subtypeRows Record lhs rhs
        lhs rhs -> typeError $ NotASubtype (lhs :@ locL) (rhs :@ locR) Nothing
      where
        subtypeLoc :: InfEffs es => TypeDT_ -> TypeDT_ -> Eff es ()
        subtypeLoc l r = subtype (l :@ locL) (r :@ locR)
        subtypeFlipped r l = subtype (r :@ locR) (l :@ locL)

        subtypeRows :: InfEffs es => RecordOrVariant -> ExtRow TypeDT_ -> ExtRow TypeDT_ -> Eff es ()
        subtypeRows whatToMatch lhs rhs = do
            lhsRow <- compress whatToMatch In lhs
            rhsRow <- compress whatToMatch Out rhs
            let (intersection, onlyL, onlyR) = Row.zipRows lhsRow.row rhsRow.row
            traverse_ (uncurry subtypeLoc) intersection
            -- we delegate the handling of univar row extensions to `subtype`
            -- by this point, any other extension would be factored out by `compress`
            newExt <- freshUniVar
            subtypeLoc (con onlyL newExt) (extensionOrEmpty rhsRow)
            subtypeLoc (extensionOrEmpty lhsRow) (con onlyR newExt)
          where
            con row ext
                | Row.isEmpty row = ext
                | otherwise = conOf whatToMatch $ ExtRow row ext
            extensionOrEmpty = fromMaybe (conOf whatToMatch $ NoExtRow Row.empty) . Row.extension

    -- (forall a -> ty) <: (foreach a -> ty)
    -- (some a ** ty) <: (exists a ** ty)
    subErased :: Erased -> Erased -> Bool
    subErased _ Erased = True
    subErased Retained Retained = True
    subErased Erased Retained = False

    -- turns out it's different enough from `withUniVar`
    solveOr :: InfEffs es => Eff es Monotype -> (Monotype -> Eff es ()) -> UniVar -> Eff es ()
    solveOr solveWith whenSolved uni = lookupUniVar uni >>= either (const $ solveUniVar uni =<< solveWith) whenSolved

check :: InfEffs es => Expr 'Fixity -> TypeDT -> Eff es ()
check (e :@ loc) (typeToCheck :@ tyLoc) = match e typeToCheck
  where
    check_ expr ty = check expr (ty :@ tyLoc)
    match = \cases
        -- the case for E.Name is redundant, since
        -- `infer` just looks up its type anyway
        (Lambda arg body) (V.Q Forall Visible Retained closure) -> do
            argVars <- checkPattern arg $ closure.ty :@ tyLoc
            (argVal, valDiff) <- skolemizePattern' arg
            local' (defineMany valDiff . declareMany argVars) do
                check body $ (closure `V.app` argVal) :@ tyLoc
        (Lambda arg body) (V.Function from to) -> do
            newTypes <- checkPattern arg $ from :@ tyLoc
            (_, valDiff) <- skolemizePattern' arg
            local' (defineMany valDiff . declareMany newTypes) do
                check_ body to
        (Annotation expr annTy) ty -> do
            annTyV <- typeFromTerm annTy
            check expr annTyV
            subtype annTyV (ty :@ tyLoc)
        (If cond true false) ty -> do
            check cond $ V.TyCon (BoolName :@ loc) :@ loc
            check_ true ty
            check_ false ty
        (Case arg matches) ty -> do
            argTy <- infer arg
            for_ matches \(pat, body) -> do
                typeMap <- checkPatternRelaxed pat argTy
                local' (declareMany typeMap) do
                    env <- ask @Env
                    newValues <- execState env.values do
                        patValue <- skolemizePattern pat
                        truePatTy <- snd <$> inferPattern pat
                        localEquality (unLoc argTy) (unLoc truePatTy)
                        traverse_ (`localEquality` patValue) (mbArgV env)
                    local' (\tcenv -> tcenv{values = newValues}) do
                        check_ body ty
          where
            -- a special case for matching on a var seems janky, but apparently that's how Idris does this
            -- we can do better: eval the arg with the current scope, which would yield a skolem for unbound vars anyway
            mbArgV env = case arg of
                L (Name name) -> Map.lookup name env.values.values
                _ -> Nothing
        (Match matches) ty -> do
            n <- whenNothing (getArgCount matches) $ typeError $ ArgCountMismatch loc
            (patTypes, bodyTy) <- unwrapFn n ty
            for_ matches \(pats, body) -> do
                typeMap <- fold <$> zipWithM checkPatternRelaxed pats (map (:@ tyLoc) patTypes)
                valDiff <- foldMap snd <$> traverse skolemizePattern' pats
                local' (defineMany valDiff . declareMany typeMap) $ check_ body bodyTy
          where
            unwrapFn 0 = pure . ([],)
            unwrapFn n =
                monoLayer' Out >=> \case
                    -- todo: this should support Pi and dependent pattern matching
                    -- V.Q{} -> uhhh
                    V.Function from to -> first (from :) <$> unwrapFn (pred n) to
                    V.UniVar uni ->
                        lookupUniVar uni >>= \case
                            Right ty' -> unwrapFn n $ unLoc $ unMono ty'
                            Left _ -> do
                                argVars <- replicateM n freshUniVar'
                                bodyVar <- freshUniVar'
                                solveUniVar uni $ Located tyLoc $ foldr (MFn . MUniVar) (MUniVar bodyVar) argVars
                                pure (V.UniVar <$> argVars, V.UniVar bodyVar)
                    _other -> typeError $ ArgCountMismatch loc
        (List items) (V.TyCon (L ListName) `V.App` itemTy) -> for_ items (`check` Located tyLoc itemTy)
        (E.Record row) ty@(V.RecordT tyRowUncompressed) -> do
            tyRow <- compress Record Out tyRowUncompressed
            let (inBoth, onlyVal, onlyTy) = Row.zipRows row tyRow.row

            for_ (IsList.toList onlyTy) \(name, _) -> typeError $ MissingField (Right $ Located loc e) name
            traverse_ (uncurry check_) inBoth

            -- since the row is compressed, we only care about the unsolved univar case here
            -- in any other case, missing fields are truly missing
            case Row.extension tyRow of
                -- solved skolems?
                Just v@V.UniVar{} -> check_ (Located loc e) v
                _ -> for_ (IsList.toList onlyVal) \(name, _) -> typeError $ MissingField (Left $ ty :@ tyLoc) name
        expr (V.UniVar uni) ->
            lookupUniVar uni >>= \case
                Right ty -> check (Located loc expr) $ unMono ty
                Left _ -> do
                    newTy <- mono In =<< infer (Located loc expr)
                    lookupUniVar uni >>= \case
                        Left _ -> solveUniVar uni newTy
                        Right _ -> pass
        (Sigma x y) (V.Q Exists Visible _e closure) -> do
            check_ x closure.ty
            env <- asks @Env (.values)
            -- I'm not sure 'V.eval' does the right thing here
            -- we should skolemize the unbound variables rather than failing
            xVal <- V.eval env x
            check_ y $ closure `V.app` xVal
        expr (V.Q Forall Implicit _e closure) -> check_ (expr :@ loc) =<< substitute Out closure
        expr (V.Q Forall Hidden _e closure) -> check_ (expr :@ loc) =<< substitute Out closure
        expr (V.Q Exists _vis _e closure) -> check_ (expr :@ loc) =<< substitute In closure
        -- todo: a case for do-notation
        expr ty -> do
            inferredTy <- infer (expr :@ loc)
            subtype inferredTy $ ty :@ tyLoc

-- a helper function for matches
getArgCount :: [([Pat], Expr 'Fixity)] -> Maybe Int
getArgCount [] = Just 0
getArgCount ((firstPats, _) : matches) = argCount <$ guard (all ((== argCount) . length . fst) matches)
  where
    argCount = length firstPats

{- Local equality in dependent pattern matching

Dependent pattern matching is performed in two ways

The first one is on the value level, where we refine the
value of a variable in each of the branches

> case n of
>   Z -> VNil -- we know that `n ~ Z` here
>   S m -> VCons 0 (something m) -- we know that `n ~ S m` for some unknown m here

The second is GADT pattern matching as it is in Haskell
This time, we only match type level information - unknown variables in
the type of `vec` are refined with the types of the patterns

> vec : Vec n a
> case vec of
>   VNil -> VNil
>   VCons x xs -> VCons (f x) (map f xs)

If we look closely, the mechanism is actually the same: we zip lhs and rhs types,
and lhs skolems are solved to the rhs where possible. The only difference is
\*what* are the lhs and rhs in each case - the matched var and a pattern in the first case
vs the type of the var and the type of the pattern in the second

To perform the refinement, we have to
- first case: turn the pattern into a skolemized value
- second case: figure out the type of the pattern
-}

-- an implementation of depedendent pattern matching, pretty much
-- invariant: two arguments are pattern-matching-compatible
-- todo: seems like localEquality should require monotypes. When do we skolemise, do we do it by layer or all at once?
localEquality :: InfEffs es => V.Value -> V.Value -> Eff (State ValueEnv : es) ()
localEquality argVal patVal = do
    venv <- get
    case (argVal, patVal) of
        (V.Skolem skolem, _) -> case LMap.lookup skolem venv.skolems of
            Just val' -> localEquality val' patVal
            Nothing -> put venv{V.skolems = LMap.insert skolem patVal $ V.skolems venv}
        (_, V.Skolem skolem) -> case LMap.lookup skolem venv.skolems of
            Just val' -> localEquality argVal val'
            Nothing -> pass
        (lhsF `V.App` lhsArg, rhsF `V.App` rhsArg) -> do
            localEquality lhsF rhsF
            localEquality lhsArg rhsArg
        (V.Con lhsName lhsVals, V.Con rhsName rhsVals)
            | lhsName == rhsName ->
                zipWithM_ localEquality lhsVals rhsVals
        (V.Record lhs, V.Record rhs) -> void $ Row.unionWithM (\l r -> l <$ localEquality l r) lhs rhs
        (V.Variant lhsName lhsArg, V.Variant rhsName rhsArg) | lhsName == rhsName -> localEquality lhsArg rhsArg
        (V.Sigma lhsX lhsY, V.Sigma rhsX rhsY) -> do
            localEquality lhsX rhsX
            localEquality lhsY rhsY
        (V.Function lhsFrom lhsTo, V.Function rhsFrom rhsTo) -> do
            localEquality lhsFrom rhsFrom
            localEquality lhsTo rhsTo
        -- todo: the rest of the cases
        -- RecordT and VariantT are complicated because of row extensions
        -- it's not clear whether we should touch UniVars at all
        _ -> pass

skolemizePattern' :: InfEffs es => Pat -> Eff es (V.Value, EnumMap Name V.Value)
skolemizePattern' pat = do
    (val, newEnv) <- runState V.ValueEnv{values = Map.empty, skolems = Map.empty} $ skolemizePattern pat
    pure (val, newEnv.values)

-- convert a pattern to a new skolemized value
skolemizePattern :: InfEffs es => Pat -> Eff (State ValueEnv : es) V.Value
skolemizePattern (Located loc pat') = case pat' of
    VarP name -> do
        valToDefine <- freshSkolem $ toSimpleName name
        modify \venv -> venv{V.values = LMap.insert name valToDefine venv.values}
        pure valToDefine
    WildcardP name -> freshSkolem $ Located loc $ Name' name -- todo: use SimpleName in WildcardP
    AnnotationP innerPat _ -> skolemizePattern innerPat
    ConstructorP con args -> V.Con con <$> traverse skolemizePattern args
    ListP args -> do
        argVs <- traverse skolemizePattern args
        -- this is not the first time I write out the List desugaring, is it?
        pure $ foldr (\h t -> V.Con (Located loc ConsName) [h, t]) (V.Con (Located loc NilName) []) argVs
    VariantP con arg -> V.Variant con <$> skolemizePattern arg
    RecordP row -> V.Record <$> traverse skolemizePattern row
    LiteralP lit -> pure $ V.PrimValue lit

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

infer :: InfEffs es => Expr 'Fixity -> Eff es TypeDT
infer (Located loc e) = case e of
    Name name -> Located loc . unLoc <$> lookupSig name
    E.Variant name -> do
        var <- freshUniVar
        rowVar <- freshUniVar
        -- #a -> [Name #a | #r]
        pure $ V.Function var (V.VariantT $ ExtRow (fromList [(name, var)]) rowVar) :@ loc
    App f x -> do
        fTy <- Located loc . unLoc <$> infer f
        inferApp loc fTy x
    TypeApp expr tyArg -> do
        ty <- infer expr
        inferTyApp expr ty tyArg
    Lambda arg body -> do
        (typeMap, argTy) <- inferPattern arg
        (_, valDiff) <- skolemizePattern' arg
        Located loc . V.Function (unLoc argTy) <$> local' (defineMany valDiff . declareMany typeMap) (unLoc <$> infer body)
    -- chances are, I'd want to add some specific error messages or context for wildcard lambdas
    -- for now, they are just desugared to normal lambdas before inference
    WildcardLambda args body -> infer $ foldr (\var -> Located loc . Lambda (Located (getLoc var) $ VarP var)) body args
    Let binding body -> do
        typeMap <- inferBinding binding
        local' (declareMany typeMap) $ infer body
    LetRec _bindings _body -> internalError loc "todo: typecheck of recursive bindings is not supported yet"
    {- do
    declareAll =<< (inferDecls . map (\b -> Located loc $ D.Value b []) . NE.toList) bindings
    infer body -}
    Annotation expr ty -> do
        tyV <- typeFromTerm ty
        tyV <$ check expr tyV
    If cond true false -> do
        check_ cond $ V.TyCon (BoolName :@ loc)
        result <- fmap unMono . mono In =<< infer true
        check false result
        pure result
    Case arg matches -> do
        result <- freshUniVar
        check_ (Case arg matches :@ loc) result
        pure $ result :@ loc
    Match [] -> typeError $ EmptyMatch loc
    Match matches@(_ : _) -> do
        argCount <- whenNothing (getArgCount matches) $ typeError $ ArgCountMismatch loc
        multArgFnTy <- foldr V.Function <$> freshUniVar <*> replicateM argCount freshUniVar
        check_ (Match matches :@ loc) multArgFnTy
        pure $ multArgFnTy :@ loc
    List items -> do
        itemTy <- freshUniVar
        traverse_ (`check_` itemTy) items
        pure $ Located loc $ V.TyCon (ListName :@ loc) `V.App` itemTy
    E.Record row -> Located loc . V.RecordT . NoExtRow <$> traverse (fmap unLoc . infer) row
    -- it's not clear whether we should special case dependent pairs where the first element is a variable, or always infer a non-dependent pair type
    Sigma x y -> do
        xName <- freshName_ $ Name' "x"
        xTy <- infer x
        yTy <- V.quote =<< infer y
        env <- asks @Env (.values)
        pure $ Located loc $ V.Q Exists Visible Retained V.Closure{var = xName :@ loc, ty = unLoc xTy, env, body = yTy}
    RecordLens fields -> do
        recordParts <- for fields \field -> do
            rowVar <- freshUniVar
            pure \nested -> V.RecordT $ ExtRow (one (field, nested)) rowVar
        let mkNestedRecord = foldr1 (.) recordParts
        a <- freshUniVar
        b <- freshUniVar
        pure $
            Located loc $
                V.TyCon
                    (Located loc LensName)
                    `V.App` mkNestedRecord a
                    `V.App` mkNestedRecord b
                    `V.App` a
                    `V.App` b
    Do _ _ -> internalError loc "do-notation is not supported yet"
    Literal (Located loc' lit) -> pure $ Located loc . V.TyCon . Located loc' $ case lit of
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
        tyV <- maybe freshUniVar (fmap unLoc . typeFromTerm) binder.kind
        local' (define binder.var tyV) $ check body type_

        pure type_
    VariantT row -> do
        traverse_ (`check` type_) row
        pure type_
    RecordT row -> do
        traverse_ (`check` type_) row
        pure type_
  where
    type_ = V.TyCon (TypeName :@ loc) :@ loc
    check_ expr ty = check expr (ty :@ loc)

inferApp :: InfEffs es => Loc -> TypeDT -> Expr 'Fixity -> Eff es TypeDT
inferApp appLoc (fTy :@ fLoc) arg = do
    monoLayer' In fTy >>= \case
        -- todo: this case is not ideal if the univar is already solved with a concrete function type
        V.UniVar uni -> do
            from <- infer arg
            to <- freshUniVar
            var <- freshName $ Located fLoc $ Name' "x"
            values <- asks @Env (.values)
            body <- V.quote (to :@ fLoc)
            let closure = V.Closure{var, env = values, ty = unLoc from, body}
            to :@ fLoc <$ subtype (V.UniVar uni :@ fLoc) (V.Q Forall Visible Retained closure :@ fLoc)
        V.Function from to -> do
            to :@ fLoc <$ check arg (from :@ fLoc)
        -- todo: special case for erased args
        V.Q Forall Visible _e closure -> do
            values <- asks @Env (.values)
            argV <- V.eval values arg
            V.app closure argV :@ fLoc <$ check arg (closure.ty :@ fLoc)
        _ -> typeError $ NotAFunction appLoc (fTy :@ fLoc)

inferTyApp :: InfEffs es => Expr 'Fixity -> TypeDT -> Type 'Fixity -> Eff es TypeDT
inferTyApp expr (ty :@ tyLoc) tyArg = case ty of
    V.Q Forall Implicit _e closure -> do
        check tyArg $ closure.ty :@ getLoc expr
        Subst{var, result} <- substitute' In closure
        values <- asks @Env (.values)
        tyArgV <- V.eval values tyArg
        subtype (var :@ tyLoc) $ tyArgV :@ getLoc tyArg
        pure $ result :@ getLoc expr
    V.Q q Hidden _e closure -> do
        Subst{result} <- substitute' (qVariance q) closure
        inferTyApp expr (result :@ tyLoc) tyArg
    _ -> typeError $ NoVisibleTypeArgument expr tyArg (ty :@ tyLoc)
  where
    qVariance = \case
        Forall -> In
        Exists -> Out

-- infers the type of a function / variables in a pattern
inferBinding :: InfEffs es => Binding 'Fixity -> Eff es (EnumMap Name TypeDT)
inferBinding = \case
    ValueB pat body -> do
        (typeMap, patTy) <- inferPattern pat
        -- we need the pattern itself to be in scope in case the binding is recursive
        bodyTy <- local' (declareMany typeMap) $ infer body
        subtype patTy bodyTy
        pure typeMap
    binding@(FunctionB name args body) -> do
        -- note: we can only infer monotypes for recursive functions
        -- while checking the body, the function itself is assigned a univar
        -- in the end, we check that the inferred type is compatible with the one in the univar (inferred from recursive calls)
        uni <- freshUniVar'
        local' (declare name (V.UniVar uni :@ getLoc binding)) do
            (typeMap, argTypes) <- traverseFold inferPattern args
            bodyTy <- local' (declareMany typeMap) $ infer body

            -- todo: infer dependent functions
            let ty = foldr (V.Function . unLoc) (unLoc bodyTy) argTypes :@ getLoc binding
            -- since we can still infer higher-rank types for non-recursive functions,
            -- we only need the subtype check when the univar is solved, i.e. when the
            -- function contains any recursive calls at all
            withUniVar uni (subtype ty . unMono)
            pure $ Map.singleton name ty

inferPattern :: InfEffs es => Pat -> Eff es (EnumMap Name TypeDT, TypeDT)
inferPattern = snd (patternFuncs pure)

-- | check a pattern, returning all of the newly bound vars
checkPattern :: InfEffs es => Pat -> TypeDT -> Eff es (EnumMap Name TypeDT)
checkPattern = fst (patternFuncs pure)

{- | check a pattern. A GADT constructor checks against a more specific type
> check VNil (Vec ?n a)
-}
checkPatternRelaxed :: InfEffs es => Pat -> TypeDT -> Eff es (EnumMap Name TypeDT)
checkPatternRelaxed = fst (patternFuncs go)
  where
    go = \case
        lhs `V.App` u@V.UniVar{} -> V.App <$> go lhs <*> pure u
        lhs `V.App` _ -> V.App <$> go lhs <*> freshUniVar
        other -> pure other

type CheckPattern es = Pat -> TypeDT -> Eff es (EnumMap Name TypeDT)
type InferPattern es = Pat -> Eff es (EnumMap Name TypeDT, TypeDT)
patternFuncs :: InfEffs es => (Type'_ -> Eff es Type'_) -> (CheckPattern es, InferPattern es)
patternFuncs postprocess = (checkP, inferP)
  where
    checkP (Located ploc outerPat) ty = case outerPat of
        -- we need this case, since inferPattern only infers monotypes for var patterns
        VarP name -> pure $ Map.singleton name ty
        -- we probably do need a case for ConstructorP for the same reason
        VariantP name arg ->
            deepLookup Variant name ty >>= \case
                Nothing -> typeError $ MissingVariant ty name
                Just argTy -> checkP arg argTy
        RecordP patRow -> do
            fold <$> for (IsList.toList patRow) \(name, pat) ->
                deepLookup Record name ty >>= \case
                    Nothing -> typeError $ MissingField (Left ty) name
                    Just fieldTy -> checkP pat fieldTy
        _ -> do
            (typeMap, inferredTy) <- inferP $ Located ploc outerPat
            subtype inferredTy ty
            pure typeMap

    inferP (Located loc p) = case p of
        VarP name -> do
            uni <- freshUniVar
            pure (Map.singleton name (uni :@ loc), uni :@ loc)
        WildcardP _ -> (Map.empty,) . Located loc <$> freshUniVar
        (AnnotationP pat ty) -> do
            tyV <- typeFromTerm ty
            (,tyV) <$> checkP pat tyV
        ConstructorP name args -> do
            (resultType, argTypes) <- conArgTypes name
            fixedResultType <- postprocess resultType
            unless (length argTypes == length args) do
                typeError $ ArgCountMismatchPattern (Located loc p) (length argTypes) (length args)
            typeMap <- fold <$> zipWithM checkP args (map (:@ loc) argTypes)
            pure (typeMap, fixedResultType :@ loc)
        ListP pats -> do
            result <- freshUniVar
            typeMap <- foldMapM (`checkP` (result :@ loc)) pats
            let listTy = V.TyCon (ListName :@ loc) `V.App` result
            pure (typeMap, listTy :@ loc)
        VariantP name arg -> do
            (typeMap, argTy) <- inferP arg
            ty <- Located loc . V.VariantT . ExtRow (fromList [(name, unLoc argTy)]) <$> freshUniVar
            pure (typeMap, ty)
        RecordP row -> do
            (typeMap, typeRow) <- traverseFold inferP row
            ty <- Located loc . V.RecordT . ExtRow (fmap unLoc typeRow) <$> freshUniVar
            pure (typeMap, ty)
        LiteralP (L lit) ->
            pure
                ( Map.empty
                , Located loc . V.TyCon . Located loc $ case lit of
                    IntLiteral num
                        | num >= 0 -> NatName
                        | otherwise -> IntName
                    TextLiteral _ -> TextName
                    CharLiteral _ -> CharName
                )

{- | splits the type singature of a value constructor into a list of args and the final type
todo: this should really be computed before the typecheck pass and put into a table
-}
conArgTypes :: InfEffs es => Name -> Eff es (V.Value, [V.Type'])
conArgTypes name = lookupSig name >>= go . unLoc
  where
    go =
        monoLayer' In >=> \case
            V.Function arg rest -> second (arg :) <$> go rest
            V.Q{} -> internalError (getLoc name) "dependent constructor types are not supported yet"
            -- MLQ _loc Forall _e closure -> second (closure.ty :) <$> go (V.closureBody closure) -- alpha-conversion?
            -- univars should never appear as the rightmost argument of a value constructor type
            -- i.e. types of value constructors have the shape `a -> b -> c -> d -> ConcreteType a b c d`
            --
            V.Con cname args -> pure (V.Con cname args, [])
            V.TyCon cname -> pure (V.TyCon cname, [])
            app@V.App{} -> pure (app, [])
            V.Skolem skolem -> pure (V.Skolem skolem, [])
            _ -> internalError (getLoc name) "invalid constructor type signature"

normalise :: InfEffs es => Eff es TypeDT -> Eff es Type'
normalise = fmap runIdentity . normaliseAll . fmap Identity

-- gets rid of all univars
normaliseAll :: (Traversable t, InfEffs es) => Eff es (t TypeDT) -> Eff es (t Type')
normaliseAll = generaliseAll >=> traverse (eval' <=< go <=< V.quote)
  where
    eval' :: InfEffs es => CoreTerm -> Eff es Type'
    eval' term = do
        values <- asks @Env (.values)
        pure $ V.evalCore values term :@ getLoc term
    go :: InfEffs es => CoreTerm -> Eff es CoreTerm
    go (term :@ loc) =
        Located loc <$> case term of
            C.UniVar uni ->
                lookupUniVar uni >>= \case
                    Left _ -> internalError loc $ "dangling univar" <+> pretty uni
                    Right body -> fmap unLoc . go =<< V.quote (unMono body)
            C.Skolem skolem -> internalError (getLoc skolem) $ "skolem" <+> pretty (V.Skolem skolem) <+> "remains in code"
            -- other cases could be eliminated by a type changing uniplate
            C.App lhs rhs -> C.App <$> go lhs <*> go rhs
            C.Function lhs rhs -> C.Function <$> go lhs <*> go rhs
            -- this might produce incorrect results if we ever share a single forall in multiple places
            C.Q Forall Visible e var ty body -> do
                ty' <- go ty
                body' <- go body
                pure
                    if occurs var body'
                        then C.Q Forall Visible e var ty' body'
                        else C.Function ty' body'
            C.Q q v e var ty body -> C.Q q v e var <$> go ty <*> go body
            C.VariantT row -> C.VariantT <$> traverse go row
            C.RecordT row -> C.RecordT <$> traverse go row
            C.Lambda name body -> C.Lambda name <$> go body
            C.Case arg matches -> C.Case <$> go arg <*> traverse (traverse go) matches
            C.Record row -> C.Record <$> traverse go row
            C.Sigma x y -> C.Sigma <$> go x <*> go y
            -- and these are just boilerplate
            C.Name name -> pure $ C.Name name
            C.TyCon name -> pure $ C.TyCon name
            C.Con name args -> pure $ C.Con name args
            C.Variant name -> pure $ C.Variant name
            C.Literal lit -> pure $ C.Literal lit
            C.Let name _ _ -> internalError (getLoc name) "unexpected let in a quoted value"

    -- check whether a variable occurs in a term
    occurs :: Name -> CoreTerm -> Bool
    occurs var (L ty) = case ty of
        C.Name name -> name == var
        C.UniVar{} -> False
        C.Skolem{} -> False
        C.App lhs rhs -> occurs var lhs || occurs var rhs
        C.Function lhs rhs -> occurs var lhs || occurs var rhs
        C.Q _ _ _ qvar qty body -> occurs qvar qty || occurs var body
        C.VariantT row -> any (occurs var) row
        C.RecordT row -> any (occurs var) row
        C.Lambda _ body -> occurs var body
        C.Case arg matches -> occurs var arg || (any . any) (occurs var) matches
        C.Record row -> any (occurs var) row
        C.Sigma x y -> occurs var x || occurs var y
        C.TyCon{} -> False
        C.Con{} -> False
        C.Variant{} -> False
        C.Literal{} -> False
        C.Let{} -> False
