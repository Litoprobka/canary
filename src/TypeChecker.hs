{-# LANGUAGE DuplicateRecordFields #-}

module TypeChecker where

import Common
import Data.EnumMap.Lazy qualified as EMap
import Data.Vector qualified as Vec
import Desugar (desugar, resugar)
import Diagnostic
import Effectful.Labeled (Labeled, runLabeled)
import Effectful.Reader.Static
import Effectful.State.Static.Local (State, evalState, get, modify, runState)
import Eval (ExtendedEnv (univars), UniVars, appM, eval, evalCore, forceM, mkTyCon, quote)
import IdMap qualified as Map
import LangPrelude
import NameGen (NameGen, freshName, freshName_, runNameGen)
import Syntax
import Syntax.Core qualified as C
import Syntax.Declaration qualified as D
import Syntax.Elaborated qualified as E
import Syntax.Row (ExtRow (..))
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
processDeclaration ctx (decl :@ loc) = case decl of
    D.Signature name sig -> do
        sigV <- withTopLevel $ removeUniVars ctx.level =<< typeFromTerm ctx sig
        univars <- get @UniVars
        let eSig = resugar $ quote univars ctx.level sigV
        modify @TopLevel $ Map.insert (unLoc name) sigV
        pure (E.SignatureD name eSig, id)
    D.Value binding (_ : _) -> internalError (getLoc binding) "todo: proper support for where clauses"
    D.Value (T.ValueB (L (T.VarP name)) body) [] -> do
        topLevel <- get @TopLevel
        eBody <- withTopLevel $ case Map.lookup (unLoc name) topLevel of
            Just sig -> check ctx body sig
            Nothing -> do
                (eBody, ty) <- bitraverse (removeUniVarsT ctx.level) (removeUniVars ctx.level) =<< infer ctx body
                modify @TopLevel $ Map.insert (unLoc name) ty
                pure eBody
        pure (E.ValueD (E.ValueB name eBody), id)
    D.Value T.ValueB{} [] -> internalError loc "pattern destructuring bindings are not supported yet"
    -- this case is way oversimplified for now, we don't even allow recursion for untyped bindings
    D.Value (T.FunctionB name args body) [] -> do
        topLevel <- get @TopLevel
        let asLambda = foldr (\(vis, var) -> (:@ getLoc body) . T.Lambda vis var) body args
        eLambda <- withTopLevel $ case Map.lookup (unLoc name) topLevel of
            Just sig -> check ctx asLambda sig
            Nothing -> do
                (eLambda, ty) <- bitraverse (removeUniVarsT ctx.level) (removeUniVars ctx.level) =<< infer ctx asLambda
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
        withTopLevel $ for_ constrs \con -> do
            conSig <- removeUniVars newCtx.level =<< typeFromTerm newCtx con.sig
            checkGadtConstructor ctx.level name con.name conSig
            modify @TopLevel $ Map.insert (unLoc con.name) conSig
        -- todo: add GADT constructors to the constructor table
        pure (E.TypeD name (map (\con -> (con.name, argCount con.sig)) constrs), Map.insert (unLoc name) tyCon)
    D.Type name binders constrs -> do
        kind <- withTopLevel $ removeUniVars ctx.level =<< typeFromTerm ctx (mkTypeKind binders)
        univars <- get
        let kindC = quote univars ctx.level kind
            tyCon = mkTyCon kindC name
        modify $ Map.insert (unLoc name) kind
        let newCtx = ctx{env = ctx.env{V.topLevel = Map.insert (unLoc name) tyCon ctx.env.topLevel}}
        withTopLevel $ for_ (mkConstrSigs name binders constrs) \(con, sig) -> do
            sigV <- removeUniVars newCtx.level =<< typeFromTerm newCtx sig
            modify @TopLevel $ Map.insert (unLoc con) sigV
        -- _conMapEntry <- mkConstructorTableEntry (map (.var) binders) (map (\con -> (con.name, con.args)) constrs)
        pure
            (E.TypeD name (map (\con -> (con.name, length con.args + C.functionTypeArity kindC)) constrs), Map.insert (unLoc name) tyCon)
  where
    withTopLevel action = do
        topLevel <- get @TopLevel
        runReader topLevel action

    -- convert a list of binders to a type term
    -- e.g. a b (c : Int) d
    -- ===> foreach (a : Type) (b : Type) (c : Int) (d : Type) -> Type
    mkTypeKind = \case
        [] -> T.Name (TypeName :@ loc) :@ loc
        (binder : rest) ->
            let newKind = T.binderKind binder
             in T.Q Forall Visible Retained binder{T.kind = Just newKind} (mkTypeKind rest) :@ loc

    mkConstrSigs :: Name -> [VarBinder 'Fixity] -> [Constructor 'Fixity] -> [(Name, Type 'Fixity)]
    mkConstrSigs name binders constrs =
        constrs <&> \(D.Constructor loc' con params) ->
            ( con
            , foldr
                -- Implicit Erased
                (\var acc -> T.Q Forall Visible Retained var acc :@ loc')
                (foldr (\lhs acc -> T.Function lhs acc :@ loc') (fullType loc') params)
                binders
            )
      where
        fullType loc' = foldl' (\lhs -> (:@ loc') . T.App Visible lhs) (T.Name name :@ getLoc name) ((:@ loc') . T.Name . (.var) <$> binders)

    -- constructors should be reprocessed into a more convenenient form somewhere else, but I'm not sure where
    argCount = go 0
      where
        go acc (L e) = case e of
            T.Function _ rhs -> go (succ acc) rhs
            T.Q Forall _ _ _ body -> go (succ acc) body
            T.Q _ _ _ _ body -> go acc body
            _ -> acc

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
                go (E.App vis term (resugar arg), innerTy)
            ty' -> pure (term, ty')

insertNeutralApp :: TC es => Context -> (ETerm, VType) -> Eff es (ETerm, VType)
insertNeutralApp ctx (term, ty) = case term of
    E.Lambda vis _ _ | vis /= Visible -> pure (term, ty)
    _ -> insertApp ctx (term, ty)

check :: TC es => Context -> Term 'Fixity -> VType -> Eff es ETerm
check ctx (t :@ loc) ty = do
    ty' <- forceM ty
    univars <- get
    case (t, ty') of
        (T.Lambda vis (L (T.VarP arg)) body, V.Q Forall qvis _e closure) | vis == qvis -> do
            bodyTy <- closure `appM` V.Var ctx.level
            eBody <- check (bind univars (unLoc arg) closure.ty ctx) body bodyTy
            pure $ E.Lambda vis (E.VarP (toSimpleName_ $ unLoc arg)) eBody
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
        (other, expected) -> do
            -- this case happens after the implicit forall case, so we know that we're checking against a monomorphic type here
            --
            -- however, there's a degenerate case where we are checking against a univar and inferring solves it to a polytype
            -- can that ever happen? I'm not sure
            (eTerm, inferred) <- insertNeutralApp ctx =<< infer ctx (other :@ loc)
            unify ctx inferred expected
            pure eTerm

infer :: TC es => Context -> Term 'Fixity -> Eff es (ETerm, VType)
infer ctx (t :@ loc) = case t of
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
    T.App vis lhs rhs -> do
        (eLhs, lhsTy) <- case vis of
            Visible -> insertApp ctx =<< infer ctx lhs
            _ -> infer ctx lhs
        closure <-
            forceM lhsTy >>= \case
                V.Q Forall vis2 _e closure | vis == vis2 -> pure closure
                V.Q Forall vis2 _e _ -> internalError loc $ "visibility mismatch" <+> pretty (show @Text vis) <+> "!=" <+> pretty (show @Text vis2)
                other -> do
                    argTy <- freshUniVarV ctx type_
                    univars <- get
                    x <- freshName_ (Name' "x")
                    closure <- V.Closure (toSimpleName_ x) argTy ctx.env <$> freshUniVar (bind univars x argTy ctx) argTy
                    unify ctx (V.Q Forall vis Retained closure) other
                    pure closure
        eRhs <- check ctx rhs closure.ty
        env <- extendEnv ctx.env
        resultTy <- closure `appM` eval env eRhs
        pure (E.App vis eLhs eRhs, resultTy)
    T.Lambda vis (T.WildcardP txt :@ patLoc) body -> do
        name <- freshName $ Name' txt :@ patLoc
        infer ctx $ T.Lambda vis (T.VarP name :@ patLoc) body :@ loc
    T.Lambda vis (L (T.VarP arg)) body -> do
        ty <- freshUniVarV ctx type_
        univars <- get
        let bodyCtx = bind univars (unLoc arg) ty ctx
        (eBody, bodyTy) <- insertNeutralApp bodyCtx =<< infer bodyCtx body
        let var = toSimpleName_ $ unLoc arg
            quotedBody = quote univars (succ ctx.level) bodyTy
        pure (E.Lambda vis (E.VarP var) eBody, V.Q Forall vis Retained V.Closure{ty, var, env = ctx.env, body = quotedBody})
    T.Lambda{} -> internalError loc "wip: pattern matching lambda"
    T.WildcardLambda{} -> internalError loc "wip: wildcard lambda"
    T.Let (T.ValueB (T.VarP name :@ _) definition) body -> do
        (eDef, ty) <- infer ctx definition
        env <- extendEnv ctx.env
        (eBody, bodyTy) <- infer (define (unLoc name) (desugar eDef) (eval env eDef) (quote env.univars ctx.level ty) ty ctx) body
        pure (E.Let (E.ValueB name eDef) eBody, bodyTy)
    T.Let{} -> internalError loc "destructuring bindings and function bindings are not supported yet"
    T.LetRec{} -> internalError loc "let rec not supported yet"
    T.Do{} -> internalError loc "do notation not supported yet"
    T.Case arg branches -> do
        (eArg, argTy) <- infer ctx arg
        result <- freshUniVarV ctx type_
        eBranches <- for branches \(pat, body) -> do
            (ePat, newLocals) <- checkPattern ctx pat argTy
            univars <- get
            (ePat,) <$> check (bindMany univars newLocals ctx) body result
        pure (E.Case eArg eBranches, result)
    T.Match{} -> internalError loc "wip: match"
    -- we don't infer dependent if, because that would mask type errors a lot of time
    T.If cond true false -> do
        eCond <- check ctx cond $ V.Type (BoolName :@ loc)
        (eTrue, trueTy) <- infer ctx true
        (eFalse, falseTy) <- infer ctx false
        unify ctx trueTy falseTy
        pure (E.If eCond eTrue eFalse, trueTy)
    T.Variant con -> do
        payloadTy <- freshUniVarV ctx type_
        payload <- freshName_ $ Name' "payload"
        univars <- get
        rowExt <- freshUniVar (bind univars payload payloadTy ctx) type_
        let body = C.VariantT $ ExtRow (fromList [(con, quote univars ctx.level payloadTy)]) rowExt
        -- '(x : ?a) -> [| Con ?a | ?r x ]'
        pure (E.Variant con, V.Pi V.Closure{env = ctx.env, ty = payloadTy, var = toSimpleName_ payload, body})
    T.RecordAccess{} -> internalError loc "wip: record access"
    T.Record{} -> internalError loc "wip: record"
    T.Sigma lhs rhs -> do
        (eLhs, lhsTy) <- infer ctx lhs
        env <- extendEnv ctx.env
        x <- freshName_ $ Name' "x"
        (eRhs, rhsTy) <- infer (define x (desugar eLhs) (eval env eLhs) (quote env.univars ctx.level lhsTy) lhsTy ctx) rhs
        univars <- get @UniVars
        -- I *think* we have to quote with increased level here, but I'm not sure
        let body = quote univars (succ ctx.level) rhsTy
        pure (E.Sigma eLhs eRhs, V.Q Exists Visible Retained $ V.Closure{ty = lhsTy, var = Name' "x", env = ctx.env, body})
    T.List items -> do
        itemTy <- freshUniVarV ctx type_
        eItems <- traverse (\item -> check ctx item itemTy) items
        pure (E.List eItems, itemTy)
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
        x <- freshName_ $ Name' "x"
        univars <- get
        eTo <- check (bind univars x (eval env eFrom) ctx) to type_
        pure (E.Q Forall Visible Retained (toSimpleName_ x ::: eFrom) eTo, type_)
    T.Q q v e binder body -> do
        eTy <- maybe (resugar <$> freshUniVar ctx type_) (\term -> check ctx term type_) binder.kind
        env <- extendEnv ctx.env
        univars <- get
        eBody <- check (bind univars (unLoc binder.var) (eval env eTy) ctx) body type_
        pure (E.Q q v e (unLoc (toSimpleName binder.var) ::: eTy) eBody, type_)
  where
    type_ = V.Type $ TypeName :@ loc

-- check a term against Type and evaluate it
typeFromTerm :: TC es => Context -> Term 'Fixity -> Eff es VType
typeFromTerm ctx term = do
    eTerm <- check ctx term (V.Type (TypeName :@ getLoc term))
    env <- extendEnv ctx.env
    pure $ eval env eTerm

checkPattern :: TC es => Context -> Pattern 'Fixity -> VType -> Eff es (EPattern, [(Name_, VType)])
checkPattern ctx (pat :@ pLoc) ty = case pat of
    T.VarP (L name) -> pure (E.VarP (toSimpleName_ name), [(name, ty)])
    T.VariantP{} -> internalError pLoc "todo: check variant pattern"
    T.RecordP{} -> internalError pLoc "todo: check record pattern"
    T.SigmaP{} -> internalError pLoc "todo: check sigma pattern"
    _ -> fallthroughToInfer
      where
        fallthroughToInfer = do
            (ePat, inferred, newLocals) <- inferPattern ctx $ pat :@ pLoc
            unify ctx inferred ty
            pure (ePat, newLocals)

inferPattern :: TC es => Context -> Pattern 'Fixity -> Eff es (EPattern, VType, [(Name_, VType)])
inferPattern ctx (p :@ loc) = case p of
    T.VarP (L name) -> do
        ty <- freshUniVarV ctx type_
        pure (E.VarP (toSimpleName_ name), ty, [(name, ty)])
    T.WildcardP txt -> do
        name <- freshName_ $ Name' txt
        ty <- freshUniVarV ctx type_
        pure (E.WildcardP txt, ty, [(name, ty)])
    (T.AnnotationP pat ty) -> do
        tyV <- typeFromTerm ctx ty
        (ePat, newLocals) <- checkPattern ctx pat tyV
        pure (ePat, tyV, newLocals)
    T.ConstructorP{} -> internalError loc "todo: inferPattern: constructor"
    T.ListP pats -> do
        result <- freshUniVarV ctx type_
        patsAndLocals <- traverse (\pat -> checkPattern ctx pat result) pats
        let ePats = map fst patsAndLocals
            -- [2, 1] [5, 4, 3] --> [5, 4, 3, 2, 1]
            -- our lists are actually snoc lists
            newLocals = fold . reverse $ map snd patsAndLocals
            listType = V.TyCon (ListName :@ loc) (Vec.singleton result)
        pure (E.ListP ePats, listType, newLocals)
    _ -> internalError loc "todo: non-trivial inferPattern"
  where
    type_ = V.Type $ TypeName :@ loc

{-
T.ConstructorP name args -> do
    (resultType, argTypes) <- conArgTypes name
    fixedResultType <- postprocess resultType
    unless (length argTypes == length args) do
        typeError $ ArgCountMismatchPattern (Located loc p) (length argTypes) (length args)
    (typeMap, typedArgs) <- traverseFold pure =<< zipWithM checkP args (map (:@ loc) argTypes)
    pure (typeMap, El.ConstructorP name typedArgs :@ loc ::: fixedResultType)
T.VariantP name arg -> do
    (typeMap, elabArg ::: argTy) <- inferP arg
    ty <- V.VariantT . ExtRow (fromList [(name, argTy)]) <$> freshUniVar
    pure (typeMap, El.VariantP name elabArg :@ loc ::: ty)
T.RecordP row -> do
    (typeMap, typedRow) <- traverseFold inferP row
    ext <- freshUniVar
    let (elabRow, typeRow) = unzip $ fmap (\(pat ::: ty) -> (pat, ty)) typedRow
        openRecordTy = V.RecordT (ExtRow typeRow ext)
    pure (typeMap, El.RecordP elabRow :@ loc ::: openRecordTy)
T.SigmaP (T.VarP name :@ varLoc) rhs -> do
    varTy <- freshUniVar
    var <- freshSkolem' $ toSimpleName name
    (typeMap, typedRhs ::: rhsTy) <- local' (define name (V.Var var) . declare name (varTy :@ varLoc)) do
        inferP rhs
    env <- asks (.values)
    body <- V.quote rhsTy
    let closure = V.Closure{var, ty = varTy, env, body}
    pure
        ( Map.insert name (varTy :@ varLoc) typeMap
        , El.SigmaP (El.VarP name :@ varLoc) typedRhs :@ loc ::: V.Q Exists Visible Retained closure
        )
T.SigmaP{} -> internalError loc "can't infer the type of a sigma with non-var lhs pattern (yet?)"
T.LiteralP lit -> do
    let litTypeName = case lit of
            IntLiteral num
                | num >= 0 -> NatName
                | otherwise -> IntName
            TextLiteral _ -> TextName
            CharLiteral _ -> CharName
    pure (Map.empty, El.LiteralP lit :@ loc ::: V.TyCon (litTypeName :@ loc) [])
-}
