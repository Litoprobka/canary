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
    normaliseAll,
    Env (..),
    InfEffs,
    inferDeclaration,
) where

import Common (Name)
import Common hiding (Name)
import Data.List.NonEmpty (unzip)
import Data.Traversable (for)
import Diagnostic (internalError, internalError')
import Effectful
import Effectful.Reader.Static (ask, asks)
import Effectful.State.Static.Local (State, get, modify, put, runState)
import Eval (ValueEnv)
import Eval qualified as V
import GHC.IsList qualified as IsList
import IdMap qualified as LMap
import IdMap qualified as Map
import LangPrelude hiding (bool, unzip)
import NameGen
import Syntax
import Syntax.Core qualified as C
import Syntax.Declaration qualified as D
import Syntax.Elaborated (EBinding, EDeclaration, EPattern, ETerm, Typed (..), unTyped)
import Syntax.Elaborated qualified as El
import Syntax.Row (ExtRow (..))
import Syntax.Row qualified as Row
import Syntax.Term hiding (Record, Variant)
import Syntax.Term qualified as E (Term_ (Record, Variant))
import TypeChecker.Backend
import TypeChecker.Exhaustiveness (checkCaseExhaustiveness, checkCompletePattern, checkMatchExhaustiveness)
import TypeChecker.Exhaustiveness qualified as Ex
import TypeChecker.TypeError

-- todo: properly handle where clauses
-- data Locality = Local | NonLocal

inferDeclaration :: InfEffs es => Declaration 'Fixity -> Eff es (EDeclaration, ValueEnv -> ValueEnv)
inferDeclaration (decl :@ loc) =
    first (:@ loc) <$> case decl of
        D.Signature name sig -> do
            sigV <- normalise $ typeFromTerm sig
            modify $ Map.insert name sigV
            pure (El.SignatureD name sigV, id)
        D.Type name binders constrs -> do
            local' (define name (V.TyCon name [])) do
                typeKind <- normalise $ mkTypeKind binders
                modify $ Map.insert name typeKind
                for_ (mkConstrSigs name binders constrs) \(con, sig) -> do
                    sigV <- normalise $ typeFromTerm sig
                    modify $ Map.insert con sigV
                conMapEntry <- mkConstructorTableEntry (map (.var) binders) (map (\con -> (con.name, con.args)) constrs)
                modify \ConstructorTable{table} -> ConstructorTable{table = Map.insert (unLoc name) conMapEntry table}
                pure (El.TypeD name (map (\con -> (con.name, length con.args)) constrs), insertVal name (V.TyCon name []))
        D.GADT name mbKind constrs -> do
            local' (define name (V.TyCon name [])) do
                kind <- maybe (pure type_) typeFromTerm mbKind
                modify $ Map.insert name $ unLoc kind
                local' (declare name kind) $ for_ constrs \con -> do
                    checkGadtConstructor name con
                    conSig <- normalise $ typeFromTerm con.sig
                    modify $ Map.insert con.name conSig
            -- todo: add GADT constructors to the constructor table
            pure (El.TypeD name (map (\con -> (con.name, argCount con.sig)) constrs), insertVal name (V.TyCon name []))
        D.Value binding (_ : _) -> internalError (getLoc binding) "todo: proper support for where clauses"
        D.Value binding [] -> do
            sigs <- get
            let relevantSigs = collectNamesInBinding binding & mapMaybe (\k -> (k,) . (:@ getLoc k) <$> Map.lookup k sigs) & Map.fromList
            Compose (typedBinding, typeMap) <- normaliseAll $ Compose . swap <$> checkBinding binding relevantSigs
            modify (typeMap <>)
            pure (El.ValueD typedBinding, id)
  where
    insertVal name val venv = venv{V.values = LMap.insert name val venv.values}

    mkTypeKind = \case
        [] -> pure type_
        (binder : rest) -> fmap (:@ loc) $ V.Function <$> (unLoc <$> typeFromTerm (binderKind binder)) <*> (unLoc <$> mkTypeKind rest) -- ewww
    type_ :: Type'
    type_ = V.TyCon (TypeName :@ loc) [] :@ loc

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

    -- constructors should be reprocessed into a more convenenient form somewhere else, but I'm not sure where
    argCount = go 0
      where
        go acc (L e) = case e of
            Function _ rhs -> go (succ acc) rhs
            Q Forall Visible _ _ body -> go (succ acc) body
            Q _ _ _ _ body -> go acc body
            _ -> acc

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

-- | check a term against Type and evaluate it
typeFromTerm :: InfEffs es => Type 'Fixity -> Eff es Type'
typeFromTerm term = do
    values <- asks @Env (.values)
    typedTerm@(_ :@ loc) <- check term $ V.TyCon (TypeName :@ getLoc term) [] :@ getLoc term
    (:@ loc) . V.evalCore values <$> V.desugarElaborated typedTerm

mkConstructorTableEntry
    :: forall es. InfEffs es => [Name] -> [(Name, [Type 'Fixity])] -> Eff es (IdMap Name_ ([ExType] -> [ExType]))
mkConstructorTableEntry boundVars constrs =
    Map.fromList . map (first unLoc) <$> (traverse . traverse) mkConstructorEntry constrs
  where
    mkConstructorEntry :: [Type 'Fixity] -> Eff es ([ExType] -> [ExType])
    mkConstructorEntry args = do
        conFns <- traverse (Ex.simplifyPatternTypeWith . unLoc <=< typeFromTerm) args
        pure $ \types -> conFns <&> \fn -> fn $ Map.fromList (zip boundVars types)

-- this is more of a subsumption check than a subtype check
subtype :: InfEffs es => TypeDT -> TypeDT -> Eff es ()
subtype (lhs_ :@ locL) (rhs_ :@ locR) = do
    _valEnv <- asks @Env (.values)
    -- todo: unstack here causes an infinite loop, not sure why
    join $ match <$> ({- V.unstuck valEnv <$> -} monoLayer' In lhs_) <*> ({- V.unstuck valEnv <$> -} monoLayer' Out rhs_)
  where
    match = \cases
        -- Nat is mostly an example to test whether this kind of subtyping
        -- would even make sense in a system with no subtype inference
        (V.TyCon (L NatName) []) (V.TyCon (L IntName) []) -> pass
        lhs@(V.TyCon lhsCon lhsArgs) rhs@(V.TyCon rhsCon rhsArgs) -> do
            unless (lhsCon == rhsCon) $ typeError $ CannotUnify (lhs :@ locL) (rhs :@ locR)
            unless (length lhsArgs == length rhsArgs) $ internalError locL "attempted to unify TyCons with different arg counts"
            zipWithM_ subtypeLoc lhsArgs rhsArgs
        (V.UniVar lhs) (V.UniVar rhs) | lhs == rhs -> pass
        (V.Var lhs) (V.Var rhs) | lhs == rhs -> pass
        lhs (V.UniVar uni) -> solveOr (Located locL <$> mono' In lhs) (subtype (lhs :@ locL) . unMono) uni
        (V.UniVar uni) rhs -> solveOr (Located locR <$> mono' Out rhs) ((`subtype` (rhs :@ locR)) . unMono) uni
        lhs rhs@(V.Var skolem) -> do
            skolems <- asks @Env ((.values) . (.values))
            case LMap.lookup skolem skolems of
                Nothing -> typeError $ NotASubtype (lhs :@ locL) (rhs :@ locR) Nothing
                Just skolemTy -> subtype (lhs :@ locL) (skolemTy :@ locR)
        lhs@(V.Var skolem) rhs -> do
            skolems <- asks @Env ((.values) . (.values))
            case LMap.lookup skolem skolems of
                Nothing -> typeError $ NotASubtype (lhs :@ locL) (rhs :@ locR) Nothing
                Just skolemTy -> subtype (skolemTy :@ locL) (rhs :@ locR)
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
        (V.VariantT lhs) (V.VariantT rhs) -> subtypeRows Variant lhs rhs
        (V.RecordT lhs) (V.RecordT rhs) -> subtypeRows Record lhs rhs
        -- todo: unify applied univars with parametrised type constructors
        -- #1 Int <: List Int     #1 := List
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
    subErased :: Erasure -> Erasure -> Bool
    subErased _ Erased = True
    subErased Retained Retained = True
    subErased Erased Retained = False

    -- turns out it's different enough from `withUniVar`
    solveOr :: InfEffs es => Eff es Monotype -> (Monotype -> Eff es ()) -> UniVar -> Eff es ()
    solveOr solveWith whenSolved uni = lookupUniVar uni >>= either (const $ solveUniVar uni =<< solveWith) whenSolved

check :: InfEffs es => Expr 'Fixity -> TypeDT -> Eff es ETerm
check (e :@ loc) (typeToCheck :@ tyLoc) = do
    valEnv <- asks @Env (.values)
    match e $ V.force valEnv typeToCheck
  where
    check_ expr ty = check expr (ty :@ tyLoc)
    match = \cases
        -- the case for E.Name is redundant, since
        -- `infer` just looks up its type anyway
        (Lambda arg body) (V.Q Forall Visible Retained closure) -> do
            (argVars, elabArg) <- checkPattern arg $ closure.ty :@ tyLoc
            let typedArg = elabArg ::: closure.ty
            (argVal, valDiff) <- skolemizePattern' arg
            typedBody <- local' (defineMany valDiff . declareMany argVars) do
                check body $ (closure `V.app` argVal) :@ tyLoc
            checkCompletePattern typedArg
            pure $ El.Lambda typedArg typedBody :@ loc
        (Lambda arg body) (V.Function from to) -> do
            (newTypes, elabArg) <- checkPattern arg $ from :@ tyLoc
            let typedArg = elabArg ::: from
            (_, valDiff) <- skolemizePattern' arg
            typedBody <- local' (defineMany valDiff . declareMany newTypes) do
                check_ body to
            checkCompletePattern typedArg
            pure $ El.Lambda typedArg typedBody :@ loc
        (Annotation expr annTy) ty -> do
            annTyV <- typeFromTerm annTy
            subtype annTyV (ty :@ tyLoc)
            check expr annTyV
        -- todo: if 'cond' is a variable, it should be known in the branches that 'cond ~ True' or 'cond ~ False'
        (If cond true false) ty -> do
            cond' <- check_ cond $ V.TyCon (BoolName :@ loc) []
            true' <- check_ true ty
            false' <- check_ false ty
            pure (El.If cond' true' false' :@ loc)
        (Case arg matches) ty -> do
            elabArg@(_ :@ argLoc) ::: argTy <- infer arg
            typedMatches <- for matches \(pat, body) -> do
                (typeMap, _) <- checkPatternRelaxed pat $ argTy :@ argLoc
                local' (declareMany typeMap) do
                    env <- ask @Env
                    (elabPat, newValues) <- runState env.values do
                        patValue <- skolemizePattern pat
                        elabPat ::: truePatTy <- snd <$> inferPattern pat
                        localEquality (argTy :@ argLoc) truePatTy
                        argV <- V.eval env.values elabArg
                        localEquality (argV :@ argLoc) patValue
                        pure elabPat
                    typedBody <- local' (\tcenv -> tcenv{values = newValues}) do
                        check body $ ty :@ loc
                    pure (elabPat, typedBody)
            checkCaseExhaustiveness loc argTy (map fst typedMatches)
            pure $ El.Case elabArg typedMatches :@ loc
        (Match matches) ty -> do
            n <- whenNothing (getArgCount matches) $ typeError $ ArgCountMismatch loc
            (mbPatTypes, bodyTy) <- unwrapFn n ty
            patTypes <- case nonEmpty mbPatTypes of
                Just types -> pure types
                Nothing -> internalError' "unwrapFn returned the wrong amount of pattern types"

            typedMatches <- for matches \(pats, body) -> do
                (typeMap, typedPatterns) <- traverseFold pure =<< zipWithM1 checkAndElaborate pats (fmap (:@ tyLoc) patTypes)
                valDiff <- foldMap snd <$> traverse skolemizePattern' pats
                typedBody <- local' (defineMany valDiff . declareMany typeMap) $ check_ body bodyTy
                pure (typedPatterns, typedBody)
            checkMatchExhaustiveness loc patTypes (fmap (fmap unTyped . fst) typedMatches)
            pure $ El.Match typedMatches :@ loc
          where
            checkAndElaborate pat patTy = do
                (typeMap, elabPat) <- checkPatternRelaxed pat patTy
                pure (typeMap, elabPat ::: unLoc patTy)

            zipWithM1 :: Applicative m => (a -> b -> m c) -> NonEmpty a -> NonEmpty b -> m (NonEmpty c)
            zipWithM1 f (x :| xs) (y :| ys) = liftA2 (:|) (f x y) (zipWithM f xs ys)

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
        (List items) (V.TyCon (L ListName) [itemTy]) -> do
            typedItems <- for items (`check` Located tyLoc itemTy)
            pure $ (El.List typedItems :@ loc)
        (E.Record row) ty@(V.RecordT tyRowUncompressed) -> do
            tyRow <- compress Record Out tyRowUncompressed
            let (inBoth, onlyVal, onlyTy) = Row.zipRows row tyRow.row

            for_ (IsList.toList onlyTy) \(name, _) -> typeError $ MissingField (Right $ Located loc e) name
            typedRow <- traverse (uncurry check_) inBoth

            -- since the row is compressed, we only care about the unsolved univar case here
            -- in any other case, missing fields are truly missing
            otherFields <- case Row.extension tyRow of
                -- solved skolems?
                Just uniExt@V.UniVar{} -> do
                    typedRest <- check_ (E.Record onlyVal :@ loc) uniExt
                    case typedRest of
                        (El.Record typedFields :@ _) -> pure typedFields
                        _ -> internalError loc "elaborated a record to something else. What?"
                _ -> do
                    for_ (IsList.toList onlyVal) \(name, _) -> typeError $ MissingField (Left $ ty :@ tyLoc) name
                    pure Row.empty
            pure $ (El.Record (typedRow <> otherFields) :@ loc)
        expr (V.UniVar uni) ->
            lookupUniVar uni >>= \case
                Right ty -> check (Located loc expr) $ unMono ty
                Left _ -> do
                    elabExpr ::: polyTy <- infer (expr :@ loc)
                    newTy <- mono In $ polyTy :@ loc
                    lookupUniVar uni >>= \case
                        Left _ -> solveUniVar uni newTy
                        Right _ -> pass
                    pure elabExpr
        (Sigma x y) (V.Q Exists Visible _e closure) -> do
            x' <- check_ x closure.ty
            env <- asks @Env (.values)
            -- I'm not sure 'V.evalCore' does the right thing here
            -- we should skolemize the unbound variables rather than failing
            xVal <- V.evalCore env <$> V.desugarElaborated x'
            y' <- check_ y $ closure `V.app` xVal
            pure $ El.Sigma x' y' :@ loc
        expr (V.Q Forall Implicit _e closure) -> check_ (expr :@ loc) =<< substitute Out closure
        expr (V.Q Forall Hidden _e closure) -> check_ (expr :@ loc) =<< substitute Out closure
        expr (V.Q Exists Implicit _e closure) -> check_ (expr :@ loc) =<< substitute In closure
        expr (V.Q Exists Hidden _e closure) -> check_ (expr :@ loc) =<< substitute In closure
        -- todo: a case for do-notation
        expr ty -> do
            (elaborated ::: inferredTy) <- infer (expr :@ loc)
            subtype (inferredTy :@ loc) $ ty :@ tyLoc
            pure elaborated

-- a helper function for matches
getArgCount :: [(NonEmpty Pat, Expr 'Fixity)] -> Maybe Int
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
localEquality :: InfEffs es => Located V.Value -> V.Value -> Eff (State ValueEnv : es) ()
localEquality argVal@(_ :@ loc) patVal = do
    venv <- get
    case (unLoc argVal, patVal) of
        (V.Var skolem, _) -> case LMap.lookup skolem venv.values of
            Just val' -> localEquality (val' :@ loc) patVal
            Nothing -> put venv{V.values = LMap.insert skolem patVal $ V.values venv}
        (_, V.Var skolem) -> case LMap.lookup skolem venv.values of
            Just val' -> localEquality argVal val'
            Nothing -> pass
        (V.TyCon lhsCon lhsArgs, V.TyCon rhsCon rhsArgs)
            | lhsCon == rhsCon ->
                zipWithM_ localEquality (fmap (:@ loc) lhsArgs) rhsArgs
        (V.Con lhsName lhsVals, V.Con rhsName rhsVals)
            | lhsName == rhsName ->
                zipWithM_ localEquality (fmap (:@ loc) lhsVals) rhsVals
        (V.Record lhs, V.Record rhs) -> void $ Row.unionWithM (\l r -> l <$ localEquality (l :@ loc) r) lhs rhs
        (V.Variant lhsName lhsArg, V.Variant rhsName rhsArg) | lhsName == rhsName -> localEquality (lhsArg :@ loc) rhsArg
        (V.Sigma lhsX lhsY, V.Sigma rhsX rhsY) -> do
            localEquality (lhsX :@ loc) rhsX
            localEquality (lhsY :@ loc) rhsY
        (V.Function lhsFrom lhsTo, V.Function rhsFrom rhsTo) -> do
            localEquality (lhsFrom :@ loc) rhsFrom
            localEquality (lhsTo :@ loc) rhsTo
        -- todo: the rest of the cases, including Stuck
        -- RecordT and VariantT are complicated because of row extensions
        -- it's not clear whether we should touch UniVars at all
        (_, V.UniVar uni) ->
            lookupUniVar uni >>= \case
                Right body -> localEquality argVal . unLoc $ unMono body
                -- todo: because of this pesky Loc requirement I had to pollute the whole function with Loc propagation
                -- I should probably rethink location information in types
                Left _ -> solveUniVar uni =<< mono In argVal
        _ -> pass

skolemizePattern' :: InfEffs es => Pat -> Eff es (V.Value, IdMap Name V.Value)
skolemizePattern' pat = do
    (val, newEnv) <- runState V.ValueEnv{values = Map.empty} $ skolemizePattern pat
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
    SigmaP lhs rhs -> V.Sigma <$> skolemizePattern lhs <*> skolemizePattern rhs
    LiteralP lit -> pure $ V.PrimValue lit

-- | given a map of related signatures, check or infer a declaration
checkBinding :: InfEffs es => Binding 'Fixity -> IdMap Name TypeDT -> Eff es (IdMap Name TypeDT, EBinding)
checkBinding binding types = case binding of
    _ | Map.null types -> inferBinding binding
    FunctionB name args body -> case Map.lookup name types of
        Just ty -> do
            bindingAsLambda <- check (foldr (\var -> (:@ getLoc binding) . Lambda var) body args) ty
            (typedArgs, typedBody) <- unwrapArgs (length args) bindingAsLambda
            traverse_ checkCompletePattern typedArgs
            pure (Map.one name ty, El.FunctionB name typedArgs typedBody)
        Nothing -> inferBinding binding
    ValueB (VarP name :@ nameLoc) body -> case Map.lookup name types of
        Just ty -> do
            typedBinding <- El.ValueB (El.VarP name :@ nameLoc ::: unLoc ty) <$> check body ty
            pure (Map.one name ty, typedBinding)
        Nothing -> inferBinding binding
    ValueB pat _body -> do
        internalError (getLoc pat) "todo: type check destructuring bindings with partial signatures"
  where
    unwrapArgs n term@(_ :@ loc) =
        go n term >>= \case
            ([], _) -> internalError loc "checkBinding: couldn't unwrap enough arguments"
            (arg : args, body) -> pure (arg :| args, body)
    go 0 term = pure ([], term)
    go n (term :@ loc) = case term of
        El.Lambda pat body -> first (pat :) <$> go (pred n) body
        _ -> internalError loc "checkBinding: not enough arguments"

infer :: InfEffs es => Expr 'Fixity -> Eff es (Typed ETerm)
infer (e :@ loc) = case e of
    Name name -> ((El.Name name :@ loc) :::) <$> lookupSig name
    E.Variant name -> do
        var <- freshUniVar
        rowVar <- freshUniVar
        -- #a -> [Name #a | #r]
        let ty = V.Function var (V.VariantT $ ExtRow (fromList [(name, var)]) rowVar)
        pure $ (El.Variant name :@ loc) ::: ty
    App f x -> do
        typedF <- infer f
        inferApp loc typedF x
    TypeApp expr tyArg -> do
        typedExpr <- infer expr
        inferTyApp typedExpr tyArg
    -- todo: is it possible to infer a pi type for more complex patterns?
    Lambda (VarP var :@ argLoc) body -> do
        argTy <- freshUniVar
        skolem <- freshSkolem' $ toSimpleName var
        let argV = V.Var skolem
        elabBody ::: bodyTy <- local' (define var argV . declare var (argTy :@ argLoc)) do
            infer body
        env <- asks @Env (.values)
        resultTy <- V.quote bodyTy
        pure $
            El.Lambda (El.VarP var :@ argLoc ::: argTy) elabBody
                :@ loc
                ::: V.Q Forall Visible Retained (V.Closure{var = skolem, ty = argTy, env, body = resultTy})
    Lambda arg body -> do
        (typeMap, typedArg@(_ ::: argTy)) <- inferPattern arg
        (_, valDiff) <- skolemizePattern' arg
        elabBody ::: bodyTy <- local' (defineMany valDiff . declareMany typeMap) do
            infer body
        checkCompletePattern typedArg
        pure $ El.Lambda typedArg elabBody :@ loc ::: V.Function argTy bodyTy
    -- chances are, I'd want to add some specific error messages or context for wildcard lambdas
    -- for now, they are just desugared to normal lambdas before inference
    WildcardLambda args body -> infer $ foldr (\var -> Located loc . Lambda (Located (getLoc var) $ VarP var)) body args
    Let binding body -> do
        (typeMap, typedBinding) <- inferBinding binding
        elabBody ::: bodyTy <- local' (declareMany typeMap) $ infer body
        pure $ El.Let typedBinding elabBody :@ loc ::: bodyTy
    LetRec _bindings _body -> internalError loc "todo: typecheck of recursive bindings is not supported yet"
    {- do
    declareAll =<< (inferDecls . map (\b -> Located loc $ D.Value b []) . NE.toList) bindings
    infer body -}
    Annotation expr ty -> do
        tyV <- typeFromTerm ty
        (::: unLoc tyV) <$> check expr tyV
    expr@If{} -> do
        -- since we have to unify the branches, we can't infer a polytype anyway
        bodyTy <- freshUniVar
        (::: bodyTy) <$> check_ (expr :@ loc) bodyTy
    Case arg matches -> do
        result <- freshUniVar
        (::: result) <$> check_ (Case arg matches :@ loc) result
    Match [] -> typeError $ EmptyMatch loc
    Match matches@(_ : _) -> do
        argCount <- whenNothing (getArgCount matches) $ typeError $ ArgCountMismatch loc
        multArgFnTy <- foldr V.Function <$> freshUniVar <*> replicateM argCount freshUniVar
        (::: multArgFnTy) <$> check_ (Match matches :@ loc) multArgFnTy
    List items -> do
        itemTy <- freshUniVar
        typedItems <- traverse (`check_` itemTy) items
        let listTy = V.TyCon (ListName :@ loc) [itemTy]
        pure $ El.List typedItems :@ loc ::: listTy
    E.Record row -> do
        typedRow <- traverse infer row
        let (elabRow, fieldTypes) = unzip $ fmap (\(x ::: t) -> (x, t)) typedRow
        pure $ El.Record elabRow :@ loc ::: V.RecordT (NoExtRow fieldTypes)
    RecordAccess record field -> do
        elabRecord ::: recordTy <- infer record
        monoLayer' In recordTy >>= deepLookup Record field . (:@ loc) >>= \case
            Nothing -> typeError $ MissingField (Left $ recordTy :@ loc) field
            Just fieldTy -> pure $ El.RecordAccess elabRecord field :@ loc ::: unLoc fieldTy

    -- it's not clear whether we should special case dependent pairs where the first element is a variable, or always infer a non-dependent pair type
    -- in a way, a non-dependent type is *more* precise
    Sigma x y -> do
        xName <- freshName_ $ Name' "x"
        x' ::: xTy <- infer x
        y' ::: yTy <- infer y
        yTy' <- V.quote yTy
        env <- asks @Env (.values)
        pure $ El.Sigma x' y' :@ loc ::: V.Q Exists Visible Retained V.Closure{var = xName :@ loc, ty = xTy, env, body = yTy'}
    Do _ _ -> internalError loc "do-notation is not supported yet"
    Literal lit -> do
        let litTypeName = case lit of
                IntLiteral num
                    | num >= 0 -> NatName
                    | otherwise -> IntName
                TextLiteral _ -> TextName
                CharLiteral _ -> CharName
        pure $ El.Literal lit :@ loc ::: V.TyCon (litTypeName :@ loc) []
    Function lhs rhs -> do
        lhs' <- check lhs $ type_ :@ getLoc rhs
        rhs' <- check rhs $ type_ :@ getLoc rhs
        pure $ El.Function lhs' rhs' :@ loc ::: type_
    -- do we need alpha-conversion?
    Q q v er binder body -> do
        tyV <- maybe freshUniVar (fmap unLoc . typeFromTerm) binder.kind
        -- a univar might make more sense for existential quantifiers, but I'm not sure yet
        varV <- freshSkolem $ toSimpleName binder.var
        typedBody <- local' (define binder.var varV . declare binder.var (tyV :@ getLoc binder)) $ check_ body type_
        pure $ El.Q q v er binder.var tyV typedBody :@ loc ::: type_
    VariantT row -> do
        typedRow <- traverse (`check_` type_) row
        pure $ El.VariantT typedRow :@ loc ::: type_
    RecordT row -> do
        typedRow <- traverse (`check_` type_) row
        pure $ El.RecordT typedRow :@ loc ::: type_
  where
    type_ :: TypeDT_
    type_ = V.TyCon (TypeName :@ loc) []
    check_ expr ty = check expr (ty :@ loc)

inferApp :: InfEffs es => Loc -> (Typed ETerm) -> Expr 'Fixity -> Eff es (Typed ETerm)
inferApp appLoc (f@(_ :@ fLoc) ::: fTy) arg = do
    monoLayer' In fTy >>= \case
        -- todo: this case is not ideal if the univar is already solved with a concrete function type
        V.UniVar uni -> do
            elabArg ::: from <- infer arg
            to <- freshUniVar
            var <- freshName $ Located fLoc $ Name' "x"
            values <- asks @Env (.values)
            body <- V.quote to
            let closure = V.Closure{var, env = values, ty = from, body}
                typedApp = El.App f elabArg :@ appLoc ::: to
            typedApp <$ subtype (V.UniVar uni :@ fLoc) (V.Q Forall Visible Retained closure :@ fLoc)
        V.Function from to -> do
            typedArg <- check arg (from :@ fLoc)
            pure $ El.App f typedArg :@ appLoc ::: to
        -- todo: special case for erased args
        V.Q Forall Visible _e closure -> do
            values <- asks @Env (.values)
            elabArg <- check arg (closure.ty :@ fLoc)
            argV <- V.evalCore values <$> V.desugarElaborated elabArg
            pure $ El.App f elabArg :@ appLoc ::: V.app closure argV
        _ -> typeError $ NotAFunction fLoc (fTy :@ fLoc)

inferTyApp :: InfEffs es => Typed ETerm -> Type 'Fixity -> Eff es (Typed ETerm)
inferTyApp (expr :@ loc ::: ty) tyArg = case ty of
    V.Q Forall Implicit _e closure -> do
        elabArg <- check tyArg $ closure.ty :@ loc
        Subst{var, result} <- substitute' In closure
        values <- asks @Env (.values)
        tyArgV <- V.evalCore values <$> V.desugarElaborated elabArg
        subtype (var :@ loc) $ tyArgV :@ getLoc tyArg
        pure $ expr :@ loc ::: result
    V.Q q Hidden _e closure -> do
        Subst{result} <- substitute' (qVariance q) closure
        inferTyApp (expr :@ loc ::: result) tyArg
    _ -> typeError $ NoVisibleTypeArgument loc tyArg (ty :@ loc)
  where
    qVariance = \case
        Forall -> In
        Exists -> Out

-- infers the type of a function / variables in a pattern
inferBinding :: InfEffs es => Binding 'Fixity -> Eff es (IdMap Name TypeDT, EBinding)
inferBinding = \case
    ValueB pat body -> do
        (typeMap, typedPat@(_ :@ loc ::: patTy)) <- inferPattern pat
        -- we need the pattern itself to be in scope in case the binding is recursive
        elabBody@(_ :@ bloc) ::: bodyTy <- local' (declareMany typeMap) $ infer body
        subtype (patTy :@ loc) (bodyTy :@ bloc)
        checkCompletePattern typedPat
        pure (typeMap, El.ValueB typedPat elabBody)
    binding@(FunctionB name args body) -> do
        -- note: we can only infer monotypes for recursive functions
        -- while checking the body, the function itself is assigned a univar
        -- in the end, we check that the inferred type is compatible with the one in the univar (inferred from recursive calls)
        uni <- freshUniVar'
        local' (declare name (V.UniVar uni :@ getLoc binding)) do
            (typeMap, typedArgs) <- traverseFold inferPattern args
            elabBody ::: bodyTy <- local' (declareMany typeMap) $ infer body

            -- todo: infer dependent functions
            let ty = foldr (V.Function . (\(_ ::: argTy) -> argTy)) bodyTy typedArgs :@ getLoc binding
            -- since we can still infer higher-rank types for non-recursive functions,
            -- we only need the subtype check when the univar is solved, i.e. when the
            -- function contains any recursive calls at all
            withUniVar uni (subtype ty . unMono)
            traverse_ checkCompletePattern typedArgs
            pure (Map.one name ty, El.FunctionB name typedArgs elabBody)

inferPattern :: InfEffs es => Pat -> Eff es (IdMap Name TypeDT, Typed EPattern)
inferPattern = snd (patternFuncs pure)

-- | check a pattern, returning all of the newly bound vars
checkPattern :: InfEffs es => Pat -> TypeDT -> Eff es (IdMap Name TypeDT, EPattern)
checkPattern = fst (patternFuncs pure)

{- | check a pattern. A GADT constructor checks against a more specific type
> check VNil (Vec ?n a)
-}
checkPatternRelaxed :: InfEffs es => Pat -> TypeDT -> Eff es (IdMap Name TypeDT, EPattern)
checkPatternRelaxed = fst (patternFuncs go)
  where
    -- we convert a restricted constructor type, like `VCons x xs : Vec (S 'n) 'a` or `VNil : Vec Z 'a`
    -- to a relaxed one, like `VCons x xs : Vec 'm 'a` or `VNil : Vec 'n 'a`
    go = \case
        V.TyCon name args -> V.TyCon name <$> traverse (const freshUniVar) args
        other -> pure other

type CheckPattern es = Pat -> TypeDT -> Eff es (IdMap Name TypeDT, EPattern)
type InferPattern es = Pat -> Eff es (IdMap Name TypeDT, Typed EPattern)
patternFuncs :: forall es. InfEffs es => (Type'_ -> Eff es Type'_) -> (CheckPattern es, InferPattern es)
patternFuncs postprocess = (checkP, inferP)
  where
    checkP :: CheckPattern es
    checkP (Located ploc outerPat) ty = case outerPat of
        -- we need this case, since inferPattern only infers monotypes for var patterns
        VarP name -> pure (Map.one name ty, El.VarP name :@ ploc)
        -- we probably do need a case for ConstructorP for the same reason
        VariantP name arg -> do
            (typeMap, typedArg) <-
                deepLookup Variant name ty >>= \case
                    Nothing -> typeError $ MissingVariant ty name
                    Just argTy -> checkP arg argTy
            pure (typeMap, El.VariantP name typedArg :@ ploc)
        RecordP patRow -> do
            diff <- flip Row.traverseWithName patRow \name pat ->
                deepLookup Record name ty >>= \case
                    Nothing -> typeError $ MissingField (Left ty) name
                    Just fieldTy -> checkP pat fieldTy

            let newNames = foldMap fst diff
                typePats = fmap snd diff
            pure (newNames, El.RecordP typePats :@ ploc)
        SigmaP lhs rhs ->
            monoLayer In ty >>= \case
                V.Q Exists Visible Retained closure :@ loc -> do
                    (lhsTypes, checkedLhs) <- checkP lhs $ closure.ty :@ loc
                    (lhsVal, valDiff) <- skolemizePattern' lhs
                    (rhsTypes, checkedRhs) <- local' (defineMany valDiff . declareMany lhsTypes) do
                        let rhsTy = closure `V.app` lhsVal
                        checkP rhs $ rhsTy :@ loc
                    pure (lhsTypes <> rhsTypes, El.SigmaP checkedLhs checkedRhs :@ ploc)
                V.UniVar{} :@ _ -> fallthroughToInfer
                other -> typeError $ NotASigma ploc other
        _ -> fallthroughToInfer
      where
        fallthroughToInfer = do
            (typeMap, elaborated ::: inferredTy) <- inferP $ Located ploc outerPat
            subtype (inferredTy :@ ploc) ty
            pure (typeMap, elaborated)

    inferP :: InferPattern es
    inferP (Located loc p) = case p of
        VarP name -> do
            uni <- freshUniVar
            pure (Map.one name (uni :@ loc), El.VarP name :@ loc ::: uni)
        WildcardP txt -> do
            uni <- freshUniVar
            pure (Map.empty, El.WildcardP txt :@ loc ::: uni)
        (AnnotationP pat ty) -> do
            tyV <- typeFromTerm ty
            second (::: unLoc tyV) <$> checkP pat tyV
        ConstructorP name args -> do
            (resultType, argTypes) <- conArgTypes name
            fixedResultType <- postprocess resultType
            unless (length argTypes == length args) do
                typeError $ ArgCountMismatchPattern (Located loc p) (length argTypes) (length args)
            (typeMap, typedArgs) <- traverseFold pure =<< zipWithM checkP args (map (:@ loc) argTypes)
            pure (typeMap, El.ConstructorP name typedArgs :@ loc ::: fixedResultType)
        ListP pats -> do
            result <- freshUniVar
            (typeMap, elabPats) <- traverseFold (`checkP` (result :@ loc)) pats
            let listTy = V.TyCon (ListName :@ loc) [result]
            pure (typeMap, El.ListP elabPats :@ loc ::: listTy)
        VariantP name arg -> do
            (typeMap, elabArg ::: argTy) <- inferP arg
            ty <- V.VariantT . ExtRow (fromList [(name, argTy)]) <$> freshUniVar
            pure (typeMap, El.VariantP name elabArg :@ loc ::: ty)
        RecordP row -> do
            (typeMap, typedRow) <- traverseFold inferP row
            ext <- freshUniVar
            let (elabRow, typeRow) = unzip $ fmap (\(pat ::: ty) -> (pat, ty)) typedRow
                openRecordTy = V.RecordT (ExtRow typeRow ext)
            pure (typeMap, El.RecordP elabRow :@ loc ::: openRecordTy)
        SigmaP (VarP name :@ varLoc) rhs -> do
            varTy <- freshUniVar
            var <- freshSkolem' $ toSimpleName name
            (typeMap, typedRhs ::: rhsTy) <- local' (define name (V.Var var) . declare name (varTy :@ varLoc)) do
                inferP rhs
            env <- asks @Env (.values)
            body <- V.quote rhsTy
            let closure = V.Closure{var, ty = varTy, env, body}
            pure
                ( Map.insert name (varTy :@ varLoc) typeMap
                , El.SigmaP (El.VarP name :@ varLoc) typedRhs :@ loc ::: V.Q Exists Visible Retained closure
                )
        SigmaP{} -> internalError loc "can't infer the type of a sigma with non-var lhs pattern (yet?)"
        LiteralP lit -> do
            let litTypeName = case lit of
                    IntLiteral num
                        | num >= 0 -> NatName
                        | otherwise -> IntName
                    TextLiteral _ -> TextName
                    CharLiteral _ -> CharName
            pure (Map.empty, El.LiteralP lit :@ loc ::: V.TyCon (litTypeName :@ loc) [])

{- | splits the type singature of a value constructor into a list of args and the final type
todo: this should really be computed before the typecheck pass and put into a table
-}
conArgTypes :: InfEffs es => Name -> Eff es (V.Value, [V.Type'])
conArgTypes name = lookupSig name >>= go
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
            V.TyCon cname args -> pure (V.TyCon cname args, [])
            V.Var skolem -> pure (V.Var skolem, [])
            _ -> internalError (getLoc name) "invalid constructor type signature"

normalise :: InfEffs es => Eff es TypeDT -> Eff es Type'_
normalise = fmap runIdentity . normaliseAll . fmap Identity

-- gets rid of all univars
-- todo: since elaborated checks may contain type annotations, we have to traverse the whole AST, not just the inferred type
normaliseAll :: (Traversable t, InfEffs es) => Eff es (t TypeDT) -> Eff es (t Type'_)
normaliseAll = generaliseAll >=> traverse (eval' <=< go <=< V.quote . unLoc)
  where
    eval' :: InfEffs es => CoreTerm -> Eff es Type'_
    eval' term = do
        values <- asks @Env (.values)
        pure $ V.evalCore values term
    go :: InfEffs es => CoreTerm -> Eff es CoreTerm
    go = \case
        C.UniVar uni ->
            lookupUniVar uni >>= \case
                Left _ -> internalError' $ "dangling univar" <+> prettyDef uni
                Right body -> go =<< V.quote (unMono' $ unLoc body)
        -- this might produce incorrect results if we ever share a single forall in multiple places
        C.Q Forall Visible e var ty body -> do
            ty' <- go ty
            body' <- go body
            pure
                if occurs var body'
                    then C.Q Forall Visible e var ty' body'
                    else C.Function ty' body'
        C.Let name _ _ -> internalError (getLoc name) "unexpected let in a quoted value"
        other -> C.coreTraversal go other

    -- check whether a variable occurs in a term
    occurs :: Name -> CoreTerm -> Bool
    occurs var = getAny . getConst . goOC
      where
        goOC :: CoreTerm -> Const Any CoreTerm
        goOC = \case
            C.Name name -> Const $ Any $ name == var
            other -> C.coreTraversal goOC other
