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
    -- inferPattern,
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
import Effectful.Reader.Static (ask, asks)
import Effectful.State.Static.Local (State, execState, get, modify, put)
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
    values <- asks @InfState (.values)
    check term $ V.TyCon (Located (getLoc term) TypeName)
    V.eval values term

subtype :: InfEffs es => TypeDT -> TypeDT -> Eff es ()
subtype lhs_ rhs_ = join $ match <$> monoLayer In lhs_ <*> monoLayer Out rhs_
  where
    match = \cases
        (V.TyCon lhs) (V.TyCon rhs) | lhs == rhs -> pass
        (V.UniVar _ lhs) (V.UniVar _ rhs) | lhs == rhs -> pass
        (V.Skolem lhs) (V.Skolem rhs) | lhs == rhs -> pass
        lhs (V.UniVar _ uni) -> solveOr (mono In lhs) (subtype lhs . unMono) uni
        (V.UniVar _ uni) rhs -> solveOr (mono Out rhs) ((`subtype` rhs) . unMono) uni
        lhs rhs@(V.Skolem skolem) -> do
            skolems <- asks @InfState ((.skolems) . (.values))
            case LMap.lookup skolem skolems of
                Nothing -> typeError $ NotASubtype lhs rhs Nothing
                Just skolemTy -> subtype lhs skolemTy
        lhs@(V.Skolem skolem) rhs -> do
            skolems <- asks @InfState ((.skolems) . (.values))
            case LMap.lookup skolem skolems of
                Nothing -> typeError $ NotASubtype lhs rhs Nothing
                Just skolemTy -> subtype skolemTy rhs
        (V.TyCon (L NatName)) (V.TyCon (L IntName)) -> pass
        lhs@(V.Con lhsCon lhsArgs) rhs@(V.Con rhsCon rhsArgs) -> do
            unless (lhsCon == rhsCon) $ typeError $ CannotUnify lhs rhs
            -- we assume that the arg count is correct
            zipWithM_ subtype lhsArgs rhsArgs
        (V.Function _ inl outl) (V.Function _ inr outr) -> do
            subtype inr inl
            subtype outl outr
        -- I'm not sure whether the subtyping between erased and non-erased arguments is right, since
        -- those types would have different runtime representations
        (V.Q _ Forall Visible erasedl closurel) (V.Q _ Forall Visible erasedr closurer) | subErased erasedr erasedl -> do
            subtype closurer.ty closurel.ty
            skolem <- freshSkolem $ toSimpleName closurel.var
            subtype (V.app closurel skolem) (V.app closurer skolem)
        (V.Q _ Exists Visible erasedl closurel) (V.Q _ Exists Visible erasedr closurer) | subErased erasedl erasedr -> do
            subtype closurel.ty closurer.ty
            skolem <- freshSkolem $ toSimpleName closurel.var
            subtype (V.app closurel skolem) (V.app closurer skolem)
        (V.Function _ inl outl) (V.Q _ Forall Visible Retained closure) -> do
            subtype closure.ty inl
            skolem <- freshSkolem $ toSimpleName closure.var
            subtype outl (V.app closure skolem)
        (V.Q _ Forall Visible Retained closure) (V.Function _ inr outr) -> do
            subtype inr closure.ty
            skolem <- freshSkolem $ toSimpleName closure.var
            subtype (V.app closure skolem) outr
        (V.App lhs rhs) (V.App lhs' rhs') -> do
            -- note that we assume the same variance for all type parameters
            -- seems like we need to track variance in kinds for this to work properly
            -- higher-kinded types are also problematic when it comes to variance, i.e.
            -- is `f a` a subtype of `f b` when a is `a` subtype of `b` or the other way around?
            --
            -- QuickLook just assumes that all constructors are invariant and -> is a special case
            subtype lhs lhs'
            subtype rhs rhs'
        (V.VariantT locL lhs) (V.VariantT locR rhs) -> subtypeRows Variant (locL, lhs) (locR, rhs)
        (V.RecordT locL lhs) (V.RecordT locR rhs) -> subtypeRows Record (locL, lhs) (locR, rhs)
        lhs rhs -> typeError $ NotASubtype lhs rhs Nothing

    -- (forall a -> ty) <: (foreach a -> ty)
    -- (some a ** ty) <: (exists a ** ty)
    subErased :: Erased -> Erased -> Bool
    subErased _ Erased = True
    subErased Retained Retained = True
    subErased Erased Retained = False

    subtypeRows :: InfEffs es => RecordOrVariant -> (Loc, ExtRow TypeDT) -> (Loc, ExtRow TypeDT) -> Eff es ()
    subtypeRows whatToMatch (locL, lhs) (locR, rhs) = do
        lhsRow <- compress whatToMatch In lhs
        rhsRow <- compress whatToMatch Out rhs
        let (intersection, onlyL, onlyR) = Row.zipRows lhsRow.row rhsRow.row
        traverse_ (uncurry subtype) intersection
        -- we delegate the handling of univar row extensions to `subtype`
        -- by this point, any other extension would be factored out by `compress`
        newExt <- freshUniVar locL
        subtype (con locL onlyL newExt) (extensionOrEmpty locL rhsRow)
        subtype (extensionOrEmpty locL lhsRow) (con locR onlyR newExt)
      where
        con loc row ext
            | Row.isEmpty row = ext
            | otherwise = conOf whatToMatch loc $ ExtRow row ext
        extensionOrEmpty loc = fromMaybe (conOf whatToMatch loc $ NoExtRow Row.empty) . Row.extension

    -- turns out it's different enough from `withUniVar`
    solveOr :: InfEffs es => Eff es Monotype -> (Monotype -> Eff es ()) -> UniVar -> Eff es ()
    solveOr solveWith whenSolved uni = lookupUniVar uni >>= either (const $ solveUniVar uni =<< solveWith) whenSolved

check :: InfEffs es => Expr 'Fixity -> TypeDT -> Eff es ()
check (Located loc e) = match e
  where
    match = \cases
        -- the case for E.Name is redundant, since
        -- `infer` just looks up its type anyway
        (Lambda (L (VarP arg)) body) (V.Q _ Forall Visible Retained closure) -> do
            -- checkPattern arg closure.ty
            var <- freshSkolem (toSimpleName arg)
            local' (define arg var . declare arg closure.ty) do
                check body (closure `V.app` var)
        (Lambda arg body) (V.Function _ from to) -> do
            newTypes <- checkPattern arg from
            local' (\env -> (env{locals = newTypes <> env.locals})) do
                check body to
        (Annotation expr annTy) ty -> do
            annTyV <- typeFromTerm annTy
            check expr annTyV
            subtype annTyV ty
        (If cond true false) ty -> do
            check cond $ V.TyCon (Located loc BoolName)
            check true ty
            check false ty
        (Case arg matches) ty -> do
            argTy <- infer arg
            for_ matches \(pat, body) -> do
                typeMap <- checkPatternRelaxed pat argTy
                local' (declareMany typeMap) do
                    env <- ask @InfState
                    newValues <- execState env.values do
                        patValue <- skolemizePattern pat
                        truePatTy <- snd <$> inferPattern pat
                        localEquality argTy truePatTy
                        traverse_ (`localEquality` patValue) (mbArgV env)
                    local' (\infState -> infState{values = newValues}) do
                        check body ty
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
                typeMap <- fold <$> zipWithM checkPatternRelaxed pats patTypes
                local' (declareMany typeMap) $ check body bodyTy
          where
            unwrapFn 0 = pure . ([],)
            unwrapFn n =
                monoLayer Out >=> \case
                    -- todo: this should support Pi and dependent pattern matching
                    -- V.Q{} -> uhhh
                    V.Function _ from to -> first (from :) <$> unwrapFn (pred n) to
                    V.UniVar loc' uni ->
                        lookupUniVar uni >>= \case
                            Right ty' -> unwrapFn n $ unMono ty'
                            Left _ -> do
                                argVars <- replicateM n freshUniVar'
                                bodyVar <- freshUniVar'
                                solveUniVar uni $ foldr (MFn loc' . MUniVar loc') (MUniVar loc' bodyVar) argVars
                                pure (V.UniVar loc' <$> argVars, V.UniVar loc' bodyVar)
                    other -> typeError $ ArgCountMismatch $ getLoc other
        (List items) (V.TyCon (L ListName) `V.App` itemTy) -> for_ items (`check` itemTy)
        (E.Record row) ty@(V.RecordT _ tyRowUncompressed) -> do
            tyRow <- compress Record Out tyRowUncompressed
            let (inBoth, onlyVal, onlyTy) = Row.zipRows row tyRow.row

            for_ (IsList.toList onlyTy) \(name, _) -> typeError $ MissingField (Right $ Located loc e) name
            traverse_ (uncurry check) inBoth

            -- since the row is compressed, we only care about the unsolved univar case here
            -- in any other case, missing fields are truly missing
            case Row.extension tyRow of
                -- solved skolems?
                Just v@V.UniVar{} -> check (Located loc e) v
                _ -> for_ (IsList.toList onlyVal) \(name, _) -> typeError $ MissingField (Left ty) name
        expr (V.UniVar _ uni) ->
            lookupUniVar uni >>= \case
                Right ty -> check (Located loc expr) $ unMono ty
                Left _ -> do
                    newTy <- mono In =<< infer (Located loc expr)
                    lookupUniVar uni >>= \case
                        Left _ -> solveUniVar uni newTy
                        Right _ -> pass
        _expr (V.Q _ Exists Visible _e _closure) -> internalError loc "dependent pairs are not supported yet"
        expr (V.Q _ Forall Implicit _e closure) -> check (Located loc expr) =<< substitute Out closure
        expr (V.Q _ Forall Hidden _e closure) -> check (Located loc expr) =<< substitute Out closure
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
        (V.Function _ lhsFrom lhsTo, V.Function _ rhsFrom rhsTo) -> do
            localEquality lhsFrom rhsFrom
            localEquality lhsTo rhsTo
        -- todo: the rest of the cases
        -- RecordT and VariantT are complicated because of row extensions
        -- it's not clear whether we should touch UniVars at all
        _ -> pass

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

-- Vec @ n @ a     Vec @ Z @ a
--

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
        (typeMap, argTy) <- inferPattern arg
        V.Function loc argTy <$> local' (declareMany typeMap) (infer body)
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
        check cond $ V.TyCon (Located loc BoolName)
        result <- fmap unMono . mono In =<< infer true
        check false result
        pure result
    Case arg matches -> do
        argTy <- infer arg
        result <- freshUniVar loc
        for_ matches \(pat, body) -> do
            typeMap <- checkPatternRelaxed pat argTy
            local' (declareMany typeMap) do
                env <- ask @InfState
                newValues <- execState env.values do
                    patValue <- skolemizePattern pat
                    truePatTy <- snd <$> inferPattern pat
                    localEquality argTy truePatTy
                    traverse_ (`localEquality` patValue) (mbArgV env)
                local' (\infState -> infState{values = newValues}) do
                    check body result
        pure result
      where
        -- see the comment in the check impl
        mbArgV env = case arg of
            L (Name name) -> Map.lookup name env.values.values
            _ -> Nothing
    Match [] -> typeError $ EmptyMatch loc
    Match matches@(_ : _) -> do
        argCount <- case getArgCount matches of
            Just argCount -> pure argCount
            Nothing -> typeError $ ArgCountMismatch loc
        result <- freshUniVar loc
        patTypes <- replicateM argCount (freshUniVar loc)
        for_ matches \(pats, body) -> do
            typeMap <- fold <$> zipWithM checkPattern pats patTypes
            local' (declareMany typeMap) $ check body result
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
        local' (define binder.var tyV) $ check body type_

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
        V.UniVar loc uni -> do
            from <- infer arg
            to <- freshUniVar loc
            var <- freshName $ Located loc $ Name' "x"
            values <- asks @InfState (.values)
            let closure = V.Closure{var, env = values, ty = from, body = V.quote to}
            to <$ subtype (V.UniVar loc uni) (V.Q loc Forall Visible Retained closure)
        V.Function _ from to -> do
            to <$ check arg from
        -- todo: special case for erased args
        V.Q _ Forall Visible _e closure -> do
            values <- asks @InfState (.values)
            argV <- V.eval values arg
            V.app closure argV <$ check arg closure.ty
        _ -> typeError $ NotAFunction appLoc fTy

inferTyApp :: InfEffs es => Expr 'Fixity -> TypeDT -> Type 'Fixity -> Eff es TypeDT
inferTyApp expr ty tyArg = case ty of
    V.Q _ Forall Implicit _e closure -> do
        Subst{var, result} <- substitute' In closure
        values <- asks @InfState (.values)
        tyArgV <- V.eval values tyArg
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
        local' (declare name (V.UniVar (getLoc binding) uni)) do
            (typeMap, argTypes) <- traverseFold inferPattern args
            bodyTy <- local' (declareMany typeMap) $ infer body

            -- todo: infer dependent functions
            let ty = foldr (V.Function $ getLoc binding) bodyTy argTypes
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
        lhs `V.App` _ -> V.App <$> go lhs <*> freshUniVar Blank
        other -> pure other

type CheckPattern es = Pat -> TypeDT -> Eff es (EnumMap Name TypeDT)
type InferPattern es = Pat -> Eff es (EnumMap Name TypeDT, TypeDT)
patternFuncs :: InfEffs es => (Type' -> Eff es Type') -> (CheckPattern es, InferPattern es)
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
            uni <- freshUniVar $ getLoc name
            pure (Map.singleton name uni, uni)
        WildcardP _ -> (Map.empty,) <$> freshUniVar loc
        (AnnotationP pat ty) -> do
            tyV <- typeFromTerm ty
            (,tyV) <$> checkP pat tyV
        ConstructorP name args -> do
            (resultType, argTypes) <- conArgTypes name
            unless (length argTypes == length args) do
                typeError $ ArgCountMismatchPattern (Located loc p) (length argTypes) (length args)
            typeMap <- fold <$> zipWithM checkP args argTypes
            pure (typeMap, resultType)
        ListP pats -> do
            result <- freshUniVar loc
            typeMap <- foldMapM (`checkP` result) pats
            let listTy = V.TyCon (Located loc ListName) `V.App` result
            pure (typeMap, listTy)
        VariantP name arg -> do
            (typeMap, argTy) <- inferP arg
            ty <- V.VariantT loc . ExtRow (fromList [(name, argTy)]) <$> freshUniVar loc
            pure (typeMap, ty)
        RecordP row -> do
            (typeMap, typeRow) <- traverseFold inferP row
            ty <- V.RecordT loc . ExtRow typeRow <$> freshUniVar loc
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

    conArgTypes name = lookupSig name >>= go
      where
        go =
            monoLayer In >=> \case
                V.Function _ arg rest -> second (arg :) <$> go rest
                V.Q loc' _ _ _ _ -> internalError loc' "dependent constructor types are not supported yet"
                -- MLQ _loc Forall _e closure -> second (closure.ty :) <$> go (V.closureBody closure) -- alpha-conversion?
                -- univars should never appear as the rightmost argument of a value constructor type
                -- i.e. types of value constructors have the shape `a -> b -> c -> d -> ConcreteType a b c d`
                --
                V.Con cname args -> pure (V.Con cname args, [])
                V.TyCon cname -> pure (V.TyCon cname, [])
                app@V.App{} -> (,[]) <$> postprocess app
                V.Skolem skolem -> pure (V.Skolem skolem, [])
                _ -> internalError (getLoc name) "invalid constructor type signature"

normalise :: InfEffs es => Eff es TypeDT -> Eff es Type'
normalise = fmap runIdentity . normaliseAll . fmap Identity

-- gets rid of all univars
normaliseAll :: (Traversable t, InfEffs es) => Eff es (t TypeDT) -> Eff es (t Type')
normaliseAll = generaliseAll >=> traverse (eval' <=< go . V.quote)
  where
    eval' :: InfEffs es => CoreTerm -> Eff es V.Value
    eval' term = do
        values <- asks @InfState (.values)
        pure $ V.evalCore values term
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
