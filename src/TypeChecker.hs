{-# LANGUAGE DuplicateRecordFields #-}

module TypeChecker where

import Common
import Data.EnumMap.Lazy qualified as EMap
import Data.IdMap qualified as Map
import Data.List.NonEmpty qualified as NE
import Data.Row (ExtRow (..))
import Desugar (desugar, flattenPattern)
import Diagnostic
import Effectful.Labeled (Labeled, runLabeled)
import Effectful.Reader.Static
import Effectful.State.Static.Local (State, evalState, get, modify, runState)
import Eval (ExtendedEnv (univars), UniVars, app, appM, eval, evalCore, forceM, mkTyCon, quote)
import LangPrelude
import NameGen (NameGen, freshName, freshName_, runNameGen)
import Syntax
import Syntax.Core qualified as C
import Syntax.Declaration qualified as D
import Syntax.Elaborated qualified as E
import Syntax.Term qualified as T
import Syntax.Value qualified as V
import TypeChecker.Backend
import TypeChecker.TypeError (TypeError (..), typeError)
import TypeChecker.Unification

processDeclaration'
    :: (NameGen :> es, Diagnose :> es) => TopLevel -> ValueEnv -> Declaration 'Fixity -> Eff es (EDeclaration, TopLevel, ValueEnv)
processDeclaration' topLevel env decl = runLabeled @UniVar runNameGen do
    ((eDecl, diff), types) <- runState topLevel $ evalState @UniVars EMap.empty $ processDeclaration (emptyContext env) decl
    pure (eDecl, types, env{V.topLevel = diff env.topLevel})

-- long story short, this is a mess. In the future, DependencyResolution should return declarations in a more structured format
processDeclaration
    :: (Labeled UniVar NameGen :> es, NameGen :> es, Diagnose :> es, State UniVars :> es, State TopLevel :> es)
    => Context
    -> Declaration 'Fixity
    -> Eff es (EDeclaration, IdMap Name_ Value -> IdMap Name_ Value)
processDeclaration ctx (decl :@ loc) = localLoc loc case decl of
    D.Signature name sig -> do
        sigV <- withTopLevel $ removeUniVars ctx =<< typeFromTerm ctx sig
        univars <- get @UniVars
        let eSig = E.Core $ quote univars ctx.level sigV
        modify @TopLevel $ Map.insert (unLoc name) sigV
        pure (E.SignatureD name eSig, id)
    D.Value binding (_ : _) -> internalError (getLoc binding) "todo: proper support for where clauses"
    D.Value (T.ValueB (L (T.VarP name)) body) [] -> do
        topLevel <- get @TopLevel
        eBody <- withTopLevel $ case Map.lookup (unLoc name) topLevel of
            Just sig -> check ctx body sig
            Nothing -> do
                (eBody, ty) <- removeUniVarsT ctx =<< infer ctx body
                modify @TopLevel $ Map.insert (unLoc name) ty
                pure eBody
        pure (E.ValueD (E.ValueB name eBody), id)
    D.Value (T.ValueB pat _) [] -> internalError (getLoc pat) "pattern destructuring bindings are not supported yet"
    -- this case is way oversimplified for now, we don't even allow recursion for untyped bindings
    D.Value (T.FunctionB name args body) [] -> do
        topLevel <- get @TopLevel
        let asLambda = foldr (\(vis, var) -> (:@ getLoc body) . T.Lambda vis var) body args
        eLambda <- withTopLevel $ case Map.lookup (unLoc name) topLevel of
            Just sig -> check ctx asLambda sig
            Nothing -> do
                (eLambda, ty) <- removeUniVarsT ctx =<< infer ctx asLambda
                modify @TopLevel $ Map.insert (unLoc name) ty
                pure eLambda
        -- ideally, we should unwrap 'eLambda' and construct a FunctionB here
        pure (E.ValueD (E.ValueB name eLambda), id)
    D.GADT name mbKind constrs -> do
        -- we can probably infer the kind of a type from its constructors, but we don't do that for now
        kind <- withTopLevel $ maybe (pure $ V.Type (TypeName :@ getLoc name)) (typeFromTerm ctx) mbKind
        univars <- get
        let kindC = quote univars ctx.level kind
            tyCon = mkTyCon kindC name
        modify @TopLevel $ Map.insert (unLoc name) kind
        let newCtx = ctx{env = ctx.env{V.topLevel = Map.insert (unLoc name) tyCon ctx.env.topLevel}}
        constrs <- withTopLevel $ for constrs \con -> do
            conSig <- removeUniVars newCtx =<< typeFromTerm newCtx con.sig
            checkGadtConstructor ctx.level name con.name conSig
            modify @TopLevel $ Map.insert (unLoc con.name) conSig
            pure (con, quote EMap.empty (Level 0) conSig)
        -- todo: add GADT constructors to the constructor table
        pure (E.TypeD name (map (\(con, conSig) -> (con.name, C.functionTypeArity conSig)) constrs), Map.insert (unLoc name) tyCon)
    D.Type name binders constrs -> do
        kind <- withTopLevel $ removeUniVars ctx =<< typeFromTerm ctx (mkTypeKind binders)
        univars <- get
        let kindC = quote univars ctx.level kind
            tyCon = mkTyCon kindC name
        modify $ Map.insert (unLoc name) kind
        let newCtx = ctx{env = ctx.env{V.topLevel = Map.insert (unLoc name) tyCon ctx.env.topLevel}}
        withTopLevel $ for_ (mkConstrSigs name binders constrs) \(con, sig) -> do
            sigV <- removeUniVars newCtx =<< typeFromTerm newCtx sig
            modify @TopLevel $ Map.insert (unLoc con) sigV
        -- _conMapEntry <- mkConstructorTableEntry (map (.var) binders) (map (\con -> (con.name, con.args)) constrs)
        let argVisibilities con = (Implicit <$ C.functionTypeArity kindC) <> fromList (Visible <$ con.args)
        pure
            (E.TypeD name (map (\con -> (con.name, argVisibilities con)) constrs), Map.insert (unLoc name) tyCon)
  where
    withTopLevel action = do
        topLevel <- get @TopLevel
        runReader topLevel action

    -- convert a list of binders to a type expression
    -- e.g. a b (c : Int) d
    -- ===> foreach (a : Type) (b : Type) (c : Int) (d : Type) -> Type
    mkTypeKind = \case
        [] -> T.Name (TypeName :@ loc) :@ loc
        (binder : rest) ->
            T.Q Forall Visible Retained binder{T.kind = Just (T.binderKind binder)} (mkTypeKind rest) :@ loc

    -- constructing constructor signatures as pre-typecheck terms is not nice,
    -- but we still need to typecheck them either way
    mkConstrSigs :: Name -> [VarBinder 'Fixity] -> [Constructor 'Fixity] -> [(Name, Type 'Fixity)]
    mkConstrSigs name binders constrs =
        constrs <&> \(D.Constructor loc' con params) ->
            ( con
            , foldr
                (\var acc -> T.Q Forall Implicit Erased var acc :@ loc')
                (foldr (\lhs acc -> T.Function lhs acc :@ loc') (fullType loc') params)
                binders
            )
      where
        fullType loc' = foldl' (\lhs -> (:@ loc') . T.App Visible lhs) (T.Name name :@ getLoc name) ((:@ loc') . T.Name . (.var) <$> binders)

    -- check that a GADT constructor actually returns the declared type
    checkGadtConstructor :: TC es => Level -> Name -> Name -> VType -> Eff es ()
    checkGadtConstructor lvl tyName con conTy = do
        univars <- get @UniVars
        case fnResult (quote univars lvl conTy) of
            C.TyCon name _
                | name /= tyName -> typeError $ ConstructorReturnType{con, expected = tyName, returned = name}
                | otherwise -> pass
            _ -> internalError (getLoc con) "something weird in a GADT constructor type"
      where
        fnResult = \case
            C.Q _ _ _ _ _ rhs -> fnResult rhs
            other -> other

-- todo: this should also handle implicit pattern matches on existentials
insertApp :: TC es => Context -> (ETerm, VType) -> Eff es (ETerm, VType)
insertApp ctx = go
  where
    go (term, ty) =
        forceM ty >>= \case
            V.Q Forall vis _e closure | vis /= Visible -> do
                arg <- freshUniVar ctx closure.ty
                env <- extendEnv ctx.env
                let argV = evalCore env arg
                innerTy <- closure `appM` argV
                go (E.App vis term (E.Core arg), innerTy)
            ty' -> pure (term, ty')

insertNeutralApp :: TC es => Context -> (ETerm, VType) -> Eff es (ETerm, VType)
insertNeutralApp ctx (term, ty) = case term of
    E.Lambda vis _ _ | vis /= Visible -> pure (term, ty)
    _ -> insertApp ctx (term, ty)

check :: TC es => Context -> Term 'Fixity -> VType -> Eff es ETerm
check ctx (t :@ loc) ty = localLoc loc do
    ty' <- forceM ty
    univars <- get
    case (t, ty') of
        (T.Lambda vis (L (T.VarP arg)) body, V.Q Forall qvis _e closure) | vis == qvis -> do
            bodyTy <- closure `appM` V.Var ctx.level
            eBody <- check (bind univars (unLoc arg) closure.ty ctx) body bodyTy
            pure $ E.Lambda vis (E.VarP (toSimpleName_ $ unLoc arg)) eBody
        -- this case doesn't work, but I don't why
        {-
         (T.Lambda vis pat body, V.Q Forall qvis _e closure) | vis == qvis -> do
             arg <- freshName_ "x"
             let ctx' = bind univars arg closure.ty ctx
             ((ePat, val), ctx) <- checkPattern ctx' pat closure.ty
             bodyTy <- closure `appM` val
             eBody <- check ctx body bodyTy
             pure (E.Lambda vis ePat eBody)
        -}
        -- we can check against a dependent type, but I'm not sure how
        (T.If cond true false, _) -> do
            eCond <- check ctx cond $ V.Type (BoolName :@ loc)
            eTrue <- check ctx true ty'
            eFalse <- check ctx false ty'
            pure (E.If eCond eTrue eFalse)
        -- insert implicit / hidden lambda
        (_, V.Q Forall vis _e closure) | vis /= Visible -> do
            x <- freshName_ closure.var
            closureBody <- closure `appM` V.Var ctx.level
            eBody <- check (bind univars x closure.ty ctx) (t :@ loc) closureBody
            pure $ E.Lambda vis (E.VarP closure.var) eBody
        (T.Case arg branches, result) -> do
            (eArg, argTy) <- infer ctx arg
            eBranches <- for branches \(pat, body) -> do
                ((ePat, _), ctx) <- checkPattern ctx pat argTy
                (ePat,) <$> check ctx body result
            pure (E.Case eArg eBranches)
        (T.Match branches, ty) ->
            E.Match <$> for branches \(pats, body) -> do
                (ePats, ctx, bodyTy) <- checkPatterns ctx pats ty
                (ePats,) <$> check ctx body bodyTy
          where
            checkPatterns ctx (pat :| pats) fnTy = do
                closure <- ensurePi ctx fnTy
                -- I'm not sure whether we should quote with
                -- the old context or with the updated context
                let patTy = E.Core $ quote univars ctx.level closure.ty
                ((ePat, patVal), ctx) <- checkPattern ctx pat closure.ty
                innerTy <- closure `appM` patVal
                case nonEmpty pats of
                    Nothing -> pure ((ePat ::: patTy) :| [], ctx, innerTy)
                    Just pats -> do
                        (ePats, ctx, resultTy) <- checkPatterns ctx pats innerTy
                        pure (NE.cons (ePat ::: patTy) ePats, ctx, resultTy)
        (other, expected) -> do
            -- this case happens after the implicit forall case, so we know that we're checking against a monomorphic type here
            --
            -- however, there's a degenerate case where we are checking against a univar and inferring solves it to a polytype
            -- can that ever happen? I'm not sure
            (eTerm, inferred) <- insertNeutralApp ctx =<< infer ctx (other :@ loc)
            unify ctx inferred expected
            pure eTerm
  where
    type_ = V.Type (TypeName :@ loc)
    ensurePi ctx =
        forceM >=> \case
            V.Pi closure -> pure closure
            uni@(V.Stuck V.UniVarApp{}) -> do
                ty <- freshUniVarV ctx type_
                name <- freshName_ "x"
                univars <- get
                body <- freshUniVar (bind univars name ty ctx) type_
                let closure = V.Closure{var = "x", env = ctx.env, ty, body}
                unify ctx uni (V.Pi closure)
                pure closure
            -- I think this should throw NotAFunction or something like that
            other -> internalError' $ "ensurePi: not a pi type:" <+> pretty other

infer :: TC es => Context -> Term 'Fixity -> Eff es (ETerm, VType)
infer ctx (t :@ loc) = localLoc loc case t of
    T.Name name -> lookupSig name ctx
    T.Annotation term ty -> do
        vty <- typeFromTerm ctx ty
        (,vty) <$> check ctx term vty
    T.Literal lit -> pure (E.Literal lit, V.Type $ litTypeName :@ loc)
      where
        litTypeName = case lit of
            IntLiteral{} -> IntName
            TextLiteral{} -> TextName
            CharLiteral{} -> CharName
    -- this is case is redundant (inferring a function type and then checking an immediate application works just fine),
    -- but since variants are guaranteed to have exactly one argument, checking it right away feels cleaner
    T.App Visible (L (T.Variant con)) payload -> do
        (ePayload, payloadTy) <- infer ctx payload
        rowExt <- freshUniVarV ctx type_
        let ty = V.VariantT $ ExtRow (fromList [(con, payloadTy)]) rowExt
        pure (E.App Visible (E.Variant con) ePayload, ty)
    T.App vis lhs rhs -> do
        (eLhs, lhsTy) <- case vis of
            Visible -> insertApp ctx =<< infer ctx lhs
            _ -> infer ctx lhs
        closure <-
            forceM lhsTy >>= \case
                V.Q Forall vis2 _e closure | vis == vis2 -> pure closure
                V.Q Forall vis2 _e _ -> internalError' $ "visibility mismatch" <+> pretty (show @Text vis) <+> "!=" <+> pretty (show @Text vis2)
                other -> do
                    argTy <- freshUniVarV ctx type_
                    univars <- get
                    x <- freshName_ "x"
                    closure <- V.Closure (toSimpleName_ x) argTy ctx.env <$> freshUniVar (bind univars x argTy ctx) type_
                    unify ctx (V.Q Forall vis Retained closure) other
                    pure closure
        eRhs <- check ctx rhs closure.ty
        env <- extendEnv ctx.env
        resultTy <- closure `appM` eval env eRhs
        pure (E.App vis eLhs eRhs, resultTy)
    T.Lambda vis (T.WildcardP txt :@ patLoc) body -> do
        name <- freshName $ Name' txt :@ patLoc
        infer ctx $ T.Lambda vis (T.VarP name :@ patLoc) body :@ loc
    T.Lambda vis (L (T.VarP (L arg))) body -> do
        ty <- freshUniVarV ctx type_
        univars <- get
        let bodyCtx = bind univars arg ty ctx
        (eBody, bodyTy) <- insertNeutralApp bodyCtx =<< infer bodyCtx body
        let var = toSimpleName_ arg
            quotedBody = quote univars (succ ctx.level) bodyTy
        pure (E.Lambda vis (E.VarP var) eBody, V.Q Forall vis Retained V.Closure{ty, var, env = ctx.env, body = quotedBody})
    -- a special case for an annotation, since it doesn't require a case at type level, unlike other patterns
    T.Lambda vis (L (T.AnnotationP (L (T.VarP (L arg))) ty)) body -> do
        ty <- typeFromTerm ctx ty
        univars <- get
        let bodyCtx = bind univars arg ty ctx
        (eBody, bodyTy) <- insertNeutralApp bodyCtx =<< infer bodyCtx body
        let var = toSimpleName_ arg
            quotedBody = quote univars (succ ctx.level) bodyTy
        pure (E.Lambda vis (E.VarP var) eBody, V.Q Forall vis Retained V.Closure{ty, var, env = ctx.env, body = quotedBody})
    -- the type of a pattern lambda has the shape '(x : argTy) -> (case x of pat -> bodyTy)'
    T.Lambda vis pat body -> do
        argTy <- freshUniVarV ctx type_
        arg <- freshName_ "x"
        univars <- get
        let ctx' = bind univars arg argTy ctx
        ((ePat, _), ty, ctx) <- inferPattern ctx' pat
        unify ctx argTy ty
        (eBody, bodyTy) <- insertNeutralApp ctx =<< infer ctx body
        univars <- get
        -- todo: if the `bodyTy` doesn't contain our new variables at all, we don't have to construct the case
        -- also, since the pattern is guaranteed to be infallible, we can define each new variable as 'case x of (Pat ... var ...) -> var'
        -- that way, unused variables would naturally disappear
        let bodyTyC = quote univars (Level $ ctx.level.getLevel + E.patternArity ePat + 1) bodyTy
            body = C.Case (C.Var (Index 0)) [(flattenPattern ePat, bodyTyC)]
            lambdaTy = V.Q Forall vis Retained V.Closure{ty, var = "x", env = ctx.env, body}
        pure (E.Lambda vis (E.VarP "x") eBody, lambdaTy)
    T.WildcardLambda{} -> internalError' "wip: wildcard lambda"
    T.Let (T.ValueB (T.VarP name :@ _) definition) body -> do
        (eDef, ty) <- infer ctx definition
        env <- extendEnv ctx.env
        (eBody, bodyTy) <- infer (define (unLoc name) (desugar eDef) (eval env eDef) (quote env.univars ctx.level ty) ty ctx) body
        pure (E.Let (E.ValueB name eDef) eBody, bodyTy)
    T.Let{} -> internalError' "destructuring bindings and function bindings are not supported yet"
    T.LetRec{} -> internalError' "let rec not supported yet"
    T.Do{} -> internalError' "do notation not supported yet"
    case'@T.Case{} -> do
        result <- freshUniVarV ctx type_
        (,result) <$> check ctx (case' :@ loc) result
    T.Match [] -> typeError $ EmptyMatch loc
    T.Match (branch : _) -> do
        fullType <- mkMultiArgPi ctx (length branch)
        (,fullType) <$> check ctx (t :@ loc) fullType
    -- we don't infer dependent if, because that would mask type errors a lot of the time
    T.If cond true false -> do
        eCond <- check ctx cond $ V.Type (BoolName :@ loc)
        (eTrue, trueTy) <- infer ctx true
        (eFalse, falseTy) <- infer ctx false
        unify ctx trueTy falseTy
        pure (E.If eCond eTrue eFalse, trueTy)
    T.Variant con -> do
        payloadTy <- freshUniVarV ctx type_
        payload <- freshName_ "payload"
        univars <- get
        rowExt <- freshUniVar (bind univars payload payloadTy ctx) type_
        let body = C.VariantT $ ExtRow (fromList [(con, quote univars ctx.level payloadTy)]) rowExt
        -- '(x : ?a) -> [| Con ?a | ?r x ]'
        pure (E.Variant con, V.Pi V.Closure{env = ctx.env, ty = payloadTy, var = toSimpleName_ payload, body})
    T.RecordAccess{} -> internalError' "wip: record access"
    T.Record{} -> internalError' "wip: record"
    T.Sigma lhs rhs -> do
        (eLhs, lhsTy) <- infer ctx lhs
        env <- extendEnv ctx.env
        x <- freshName_ "x"
        (eRhs, rhsTy) <- infer (define x (desugar eLhs) (eval env eLhs) (quote env.univars ctx.level lhsTy) lhsTy ctx) rhs
        univars <- get @UniVars
        -- I *think* we have to quote with increased level here, but I'm not sure
        let body = quote univars (succ ctx.level) rhsTy
        pure (E.Sigma eLhs eRhs, V.Q Exists Visible Retained $ V.Closure{ty = lhsTy, var = "x", env = ctx.env, body})
    T.List items -> do
        itemTy <- freshUniVar ctx type_
        env <- extendEnv ctx.env
        let itemTyV = evalCore env itemTy
        eItems <- traverse (\item -> check ctx item itemTyV) items
        pure (E.List (E.Core itemTy) eItems, V.TyCon (ListName :@ loc) $ fromList [(Visible, itemTyV)])
    T.RecordT row -> do
        eRow <- traverse (\field -> check ctx field type_) row
        pure (E.RecordT eRow, type_)
    T.VariantT row -> do
        eRow <- traverse (\field -> check ctx field type_) row
        pure (E.VariantT eRow, type_)
    -- normal function syntax is just sugar for '(_ : a) -> b'
    T.Function from to -> do
        eFrom <- check ctx from type_
        env <- extendEnv ctx.env
        x <- freshName_ "x"
        univars <- get
        eTo <- check (bind univars x (eval env eFrom) ctx) to type_
        pure (E.Q Forall Visible Retained (toSimpleName_ x ::: eFrom) eTo, type_)
    T.Q q v e binder body -> do
        eTy <- maybe (E.Core <$> freshUniVar ctx type_) (\term -> check ctx term type_) binder.kind
        env <- extendEnv ctx.env
        univars <- get
        eBody <- check (bind univars (unLoc binder.var) (eval env eTy) ctx) body type_
        pure (E.Q q v e (unLoc (toSimpleName binder.var) ::: eTy) eBody, type_)
  where
    type_ = V.Type $ TypeName :@ loc

    mkMultiArgPi ctx n = do
        env <- extendEnv ctx.env
        evalCore env <$> mkMultiArgPi' ctx n

    mkMultiArgPi' ctx 0 = freshUniVar ctx type_
    mkMultiArgPi' ctx n = do
        ty <- freshUniVar ctx type_
        argName <- freshName_ "x"
        env <- extendEnv ctx.env
        resultTy <- mkMultiArgPi' (bind env.univars argName (evalCore env ty) ctx) (pred n)
        pure $ C.Q Forall Visible Retained "x" ty resultTy

-- check a term against Type and evaluate it
typeFromTerm :: TC es => Context -> Term 'Fixity -> Eff es VType
typeFromTerm ctx term = do
    eTerm <- check ctx term (V.Type (TypeName :@ getLoc term))
    env <- extendEnv ctx.env
    pure $ eval env eTerm

checkPattern :: TC es => Context -> Pattern 'Fixity -> VType -> Eff es ((EPattern, Value), Context)
checkPattern ctx (pat :@ pLoc) ty = do
    univars <- get
    localLoc pLoc case pat of
        T.VarP (L name) -> do
            value <- freshUniVarV ctx ty
            pure ((E.VarP (toSimpleName_ name), value), bind univars name ty ctx)
        T.WildcardP txt -> do
            name <- freshName_ $ Name' txt
            value <- freshUniVarV ctx ty
            pure ((E.WildcardP txt, value), bind univars name ty ctx)
        T.VariantP{} -> internalError' "todo: check variant pattern"
        T.RecordP{} -> internalError' "todo: check record pattern"
        T.SigmaP vis lhs rhs -> do
            forceM ty >>= \case
                V.Q Exists vis2 _e closure
                    | vis /= vis2 -> internalError' "sigma type: visibility mismatch"
                    | otherwise -> do
                        ((eLhs, lhsV), ctx) <- checkPattern ctx lhs closure.ty
                        ((eRhs, rhsV), ctx) <- checkPattern ctx rhs =<< closure `appM` lhsV
                        pure ((E.SigmaP vis eLhs eRhs, V.Sigma lhsV rhsV), ctx)
                _ -> fallthroughToInfer
        _ -> fallthroughToInfer
  where
    fallthroughToInfer = do
        (ePat, inferred, ctx) <- inferPattern ctx $ pat :@ pLoc
        unify ctx inferred ty
        pure (ePat, ctx)

inferPattern :: TC es => Context -> Pattern 'Fixity -> Eff es ((EPattern, Value), VType, Context)
inferPattern ctx (p :@ loc) = do
    univars <- get
    localLoc loc case p of
        T.VarP (L name) -> do
            ty <- freshUniVarV ctx type_
            value <- freshUniVarV ctx ty
            pure ((E.VarP (toSimpleName_ name), value), ty, bind univars name ty ctx)
        T.WildcardP txt -> do
            name <- freshName_ $ Name' txt
            ty <- freshUniVarV ctx type_
            value <- freshUniVarV ctx ty
            pure ((E.WildcardP txt, value), ty, bind univars name ty ctx)
        (T.AnnotationP pat ty) -> do
            tyV <- typeFromTerm ctx ty
            (ePat, newLocals) <- checkPattern ctx pat tyV
            pure (ePat, tyV, newLocals)
        T.ConstructorP name args -> do
            (_, conType) <- lookupSig name ctx
            (argsWithVals, ty, ctx) <- inferConArgs ctx conType args
            let (eArgs, argVals) = unzip argsWithVals
                valsWithVis = zip (map fst eArgs) argVals
            pure ((E.ConstructorP name eArgs, V.Con name (fromList valsWithVis)), ty, ctx)
        T.SigmaP{} -> internalError' "todo: not sure how to infer sigma"
        -- this is a lazy desugaring, I can do better
        T.ListP pats -> do
            itemType <- freshUniVarV ctx type_
            let listType = V.TyCon (ListName :@ loc) $ fromList [(Visible, itemType)]
                patToCheck = case pats of
                    [] -> T.ConstructorP (NilName :@ loc) [] :@ loc
                    (pat : pats) -> T.ConstructorP (ConsName :@ loc) [(Visible, pat), (Visible, T.ListP pats :@ loc)] :@ loc
            (ePat, ctx) <- checkPattern ctx patToCheck listType
            pure (ePat, listType, ctx)
        T.LiteralP lit -> do
            let litTypeName = case lit of
                    IntLiteral{} -> IntName
                    TextLiteral{} -> TextName
                    CharLiteral{} -> CharName
            pure ((E.LiteralP lit, V.PrimValue lit), V.Type (litTypeName :@ loc), ctx)
        T.VariantP{} -> internalError' "todo: infer variant pattern"
        T.RecordP{} -> internalError' "todo: infer record pattern"
  where
    type_ = V.Type $ TypeName :@ loc

    inferConArgs
        :: TC es => Context -> VType -> [(Visibility, Pattern 'Fixity)] -> Eff es ([((Visibility, EPattern), Value)], VType, Context)
    inferConArgs ctx conType args = do
        conType <- forceM conType
        case (conType, args) of
            (V.Q Forall vis _e closure, (vis2, arg) : rest) | vis == vis2 -> do
                ((eArg, argV), ctx) <- checkPattern ctx arg closure.ty
                univars <- get
                (pats, vty, ctx) <- inferConArgs ctx (app univars closure argV) rest
                pure (((vis, eArg), argV) : pats, vty, ctx)
            -- insert an implicit argument: 'Cons x xs' --> 'Cons @a x xs'
            (V.Q Forall vis _e closure, args) | vis /= Visible -> do
                name <- freshName_ "a"
                ((insertedPat, insertedVal), ctx) <- checkPattern ctx (T.VarP (name :@ loc) :@ loc) closure.ty
                univars <- get
                (pats, vty, ctx) <- inferConArgs ctx (app univars closure insertedVal) args
                pure (((vis, insertedPat), insertedVal) : pats, vty, ctx)
            (V.Q Forall Visible _ _, (vis2, _) : _) ->
                internalError' $
                    "visibility mismatch: expected a visible argument, got an" <+> pretty (show @Text vis2) <+> "one."
            (V.Q Exists _ _ _, _) -> internalError' "existentials in constructor types are not supported yet"
            (ty@V.TyCon{}, []) -> do
                pure (mempty, ty, ctx)
            (V.TyCon{}, _) -> internalError' "too many arguments in a pattern"
            _ -> internalError' "not enough arguments in a pattern"
