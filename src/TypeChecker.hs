{-# LANGUAGE DuplicateRecordFields #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module TypeChecker where

import Common
import Data.EnumMap.Lazy qualified as EMap
import Data.Functor (unzip)
import Data.IdMap qualified as Map
import Data.List.NonEmpty qualified as NE
import Data.Row (ExtRow (..), OpenName)
import Data.Row qualified as Row
import Data.Vector qualified as Vec
import Desugar (desugar)
import Diagnostic
import Effectful.Reader.Static
import Effectful.State.Static.Local (State, get, modify, put, runState)
import Eval (ExtendedEnv (univars), app, appM, eval, evalCore, forceM, mkTyCon, quote, quoteM)
import GHC.IsList qualified as IsList
import LangPrelude hiding (unzip)
import NameGen (NameGen, freshName, freshName_)
import Syntax
import Syntax.Core qualified as C
import Syntax.Declaration qualified as D
import Syntax.Elaborated qualified as E
import Syntax.Term qualified as T
import Syntax.Value qualified as V
import Trace
import TypeChecker.Backend
import TypeChecker.Generalisation
import TypeChecker.TypeError (TypeError (..), typeError)
import TypeChecker.Unification (refine, unify)

type DeclTC es =
    ( NameGen :> es
    , Diagnose :> es
    , Trace :> es
    , UniEffs es
    , State TopLevel :> es
    , State ConMetaTable :> es
    )

processDeclaration'
    :: (NameGen :> es, Diagnose :> es, Trace :> es, State TopLevel :> es, State ConMetaTable :> es)
    => ValueEnv
    -> Declaration 'Fixity
    -> Eff es (EDeclaration, ValueEnv)
processDeclaration' env decl = runUniEffs do
    (eDecl, diff) <- processDeclaration (emptyContext env) decl
    pure (eDecl, env{V.topLevel = diff env.topLevel})

processDeclaration
    :: DeclTC es => Context -> Declaration 'Fixity -> Eff es (EDeclaration, IdMap Name_ Value -> IdMap Name_ Value)
processDeclaration ctx (decl :@ loc) = localLoc loc case decl of
    D.Signature name sig -> (,id) <$> processSignature ctx name sig
    D.Value binding locals -> (,id) <$> checkBinding ctx binding locals
    D.GADT name mbKind constructors -> second (Map.insert (unLoc name)) <$> processGadt ctx name mbKind constructors
    D.Type name binders constructors -> second (Map.insert (unLoc name)) <$> processType ctx name binders constructors

processSignature :: DeclTC es => Context -> Name -> Term 'Fixity -> Eff es EDeclaration
processSignature ctx name sig = do
    sigV <- withTopLevel $ generalise ctx =<< typeFromTerm ctx sig
    univars <- get
    let eSig = E.Core $ quote univars ctx.level sigV
    modify $ Map.insert (unLoc name) sigV
    pure (E.SignatureD (unLoc name) eSig)

checkBinding
    :: DeclTC es
    => Context
    -> Binding 'Fixity
    -> [Declaration 'Fixity]
    -> Eff es EDeclaration
checkBinding _ binding (_ : _) = internalError (getLoc binding) "todo: proper support for where clauses"
checkBinding ctx binding [] = do
    topLevel <- get
    (name, body) <- case binding of
        (T.ValueB (L (T.VarP name)) body) -> pure (name, body)
        (T.FunctionB name args body) ->
            pure (name, foldr (\(vis, var) -> (:@ getLoc body) . T.Lambda vis var) body args)
        T.ValueB pat _ -> internalError (getLoc pat) "pattern destructuring bindings are not supported yet"
    eBody <- withTopLevel case Map.lookup (unLoc name) topLevel of
        Just sig -> traceScope_ (specSymBlue "check" <+> prettyDef name <+> ":" <+> prettyValCtx ctx sig) do
            zonkTerm ctx =<< check ctx body sig
        Nothing -> traceScope_ (specSym "infer" <+> prettyDef name) do
            -- since we don't have a signature for our binding, we need a placeholder type for recursive calls
            recType <- freshUniVarV ctx (V.Type TypeName)
            let recCtx = ctx{env = ctx.env{V.topLevel = Map.insert (unLoc name) (V.Stuck $ V.Opaque (unLoc name) []) ctx.env.topLevel}}
            modify $ Map.insert (unLoc name) recType

            inferred@(_, monoTy) <- infer recCtx body

            -- check that the type of recursive calls matches the inferred type
            -- if there have been no recursive calls, 'monoTy' would stay the same
            unify recCtx recType monoTy

            -- after checking recursive calls, we can generalise
            (eBody, ty) <- generaliseRecursiveTerm recCtx (unLoc name) inferred
            modify $ Map.insert (unLoc name) ty
            pure eBody
    -- ideally, we should unwrap the body and construct a FunctionB if the original binding was a function
    pure (E.ValueD (E.ValueB (unLoc name) eBody))

processGadt :: DeclTC es => Context -> Name -> Maybe (Type 'Fixity) -> [GadtConstructor 'Fixity] -> Eff es (EDeclaration, VType)
processGadt ctx name mbKind constructors = do
    -- we can probably infer the kind of a type from its constructors, but we don't do that for now
    kind <- withTopLevel $ maybe (pure $ V.Type TypeName) (typeFromTerm ctx) mbKind
    kindC <- quoteM ctx.level kind
    let tyCon = mkTyCon kindC (unLoc name)
    modify $ Map.insert (unLoc name) kind
    modify $ Map.insert (unLoc name) (mkTypeConstructorMetadata (getLoc name) kind)
    let newCtx = ctx{env = ctx.env{V.topLevel = Map.insert (unLoc name) tyCon ctx.env.topLevel}}
    constructors <- withTopLevel $ for constructors \con -> do
        conSig <- generalise newCtx =<< typeFromTerm newCtx con.sig
        checkGadtConstructor ctx.level (unLoc name) con.name conSig
        modify $ Map.insert (unLoc con.name) conSig
        modify $ Map.insert (unLoc con.name) (mkConstructorMetadata (name, kind) conSig)
        pure (con, quote EMap.empty (Level 0) conSig)
    pure (E.TypeD (unLoc name) (map (\(con, conSig) -> (unLoc con.name, C.functionTypeArity conSig)) constructors), tyCon)
  where
    -- check that a GADT constructor actually returns the declared type
    checkGadtConstructor :: TC es => Level -> Name_ -> Name -> VType -> Eff es ()
    checkGadtConstructor lvl typeName con conType = do
        univars <- get
        case fnResult (quote univars lvl conType) of
            C.TyCon name _
                | name == typeName -> pass
                | otherwise -> typeError ConstructorReturnType{con, expected = typeName, returned = C.TyCon name Vec.empty}
            returned -> typeError ConstructorReturnType{con, expected = typeName, returned}
      where
        fnResult = \case
            C.Q _ _ _ _ _ rhs -> fnResult rhs
            other -> other

processType :: DeclTC es => Context -> Name -> [VarBinder 'Fixity] -> [Constructor 'Fixity] -> Eff es (EDeclaration, VType)
processType ctx name binders constructors = do
    kind <- withTopLevel $ generalise ctx =<< typeFromTerm ctx (mkTypeKind binders)
    univars <- get
    let kindC = quote univars ctx.level kind
        tyCon = mkTyCon kindC (unLoc name)
    modify $ Map.insert (unLoc name) kind
    modify $ Map.insert (unLoc name) (mkTypeConstructorMetadata (getLoc name) kind)
    let newCtx = ctx{env = ctx.env{V.topLevel = Map.insert (unLoc name) tyCon ctx.env.topLevel}}
    withTopLevel $ for_ (mkConstrSigs name binders constructors) \(con, sig) -> do
        sigV <- generalise newCtx =<< typeFromTerm newCtx sig
        modify $ Map.insert (unLoc con) sigV
        modify $ Map.insert (unLoc con) (mkConstructorMetadata (name, kind) sigV)
    -- _conMapEntry <- mkConstructorTableEntry (map (.var) binders) (map (\con -> (con.name, con.args)) constrs)
    let argVisibilities con = (Implicit <$ C.functionTypeArity kindC) <> fromList (Visible <$ con.args)
    pure
        (E.TypeD (unLoc name) (map (\con -> (unLoc con.name, argVisibilities con)) constructors), tyCon)
  where
    -- convert a list of binders to a type expression
    -- e.g. a b (c : Int) d
    -- ===> foreach (a : Type) (b : Type) (c : Int) (d : Type) -> Type
    mkTypeKind = \case
        [] -> T.Name (TypeName :@ getLoc name) :@ getLoc name
        (binder : rest) ->
            T.Q Forall Visible Retained binder{T.kind = Just (T.binderKind binder)} (mkTypeKind rest) :@ getLoc name

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

mkTypeConstructorMetadata :: Loc -> VType -> ConMetadata
mkTypeConstructorMetadata loc = mkConstructorMetadata (TypeName :@ loc, V.Type TypeName)

mkConstructorMetadata :: (Name, VType) -> VType -> ConMetadata
mkConstructorMetadata (L typeName, kind) conType = ConMetadata \ctx -> do
    params <- getTypeParams ctx.level conType
    (lvlMap, uniParams) <- instantiate ctx EMap.empty kind params
    let goalType = V.TyCon typeName $ fromList uniParams
    univars <- get
    pure (goalType, go univars lvlMap ctx.level conType)
  where
    getTypeParams lvl = \case
        V.Q Forall _vis _e closure -> getTypeParams (succ lvl) =<< closure `appM` V.Var lvl
        V.TyCon name params | typeName == name -> pure $ toList params
        _ -> internalError' "invalid constructor type"

    --  instantiate type parameters with fresh unification variables:
    -- 'List : Type -> Type' --> '?a'
    instantiate
        :: (UniEffs es, Reader TopLevel :> es, Diagnose :> es)
        => Context
        -> EnumMap Level Value
        -> VType
        -> [(Visibility, Value)]
        -> Eff es (EnumMap Level Value, [(Visibility, Value)])
    instantiate ctx lvlMap = \cases
        (V.Q Forall _ _ closure) ((vis, V.Var vlvl) : rest) -> do
            val <- freshUniVarV ctx closure.ty
            innerType <- closure `appM` val
            second ((vis, val) :) <$> instantiate ctx (EMap.insert vlvl val lvlMap) innerType rest
        (V.Q Forall _ _ closure) ((vis, _) : rest) -> do
            val <- freshUniVarV ctx closure.ty
            innerType <- closure `appM` val
            second ((vis, val) :) <$> instantiate ctx lvlMap innerType rest
        -- this case is slightly more permissive, so that `instantiate` can also be used on constructor signatures
        (V.TyCon{}) [] -> pure (lvlMap, [])
        _ _ -> internalError' "parameter count mismatch"

    go univars params lvl = \case
        (V.Q Forall vis _e closure) -> case EMap.lookup lvl params of
            Just val -> UsedInType vis closure.var closure.ty val (go univars params (succ lvl) (app univars closure val))
            Nothing -> UnusedInType vis closure.var closure.ty (go univars params (succ lvl) . app univars closure)
        ty@V.TyCon{} -> FinalType ty
        _ -> error "invalid constructor type"

-- the type is slightly imprecise, but whatever

-- | a helper for 'processDeclaration' subfunctions that provides the current metadata table and top level binding state as read only
withTopLevel
    :: (State TopLevel :> es, State ConMetaTable :> es) => Eff (Reader TopLevel : Reader ConMetaTable : es) a -> Eff es a
withTopLevel action = do
    topLevel <- get
    metaTable <- get
    runReader topLevel $ runReader metaTable action

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
check ctx (t :@ loc) ty = traceScope_ (prettyDef t <+> specSymBlue "⇐" <+> prettyValCtx ctx ty) $ localLoc loc do
    ty' <- forceM ty
    univars <- get
    case (t, ty') of
        (T.Lambda vis (L (T.VarP arg)) body, V.Q Forall qvis _e closure) | vis == qvis -> do
            bodyTy <- closure `appM` V.Var ctx.level
            eBody <- check (bind univars (unLoc arg) closure.ty ctx) body bodyTy
            pure $ E.Lambda vis (E.VarP (toSimpleName_ $ unLoc arg)) eBody
        -- this case doesn't work at the moment, because the new var is not
        -- present in the elaborated term, and the indices no longer line up
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
            eCond <- check ctx cond $ V.Type BoolName
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
            env <- extendEnv ctx.env
            let argV = eval env eArg
            eBranches <- for branches \(pat, body) -> do
                ((ePat, patV), ctx) <- checkPattern ctx pat argTy
                ctx <- refine ctx patV argV
                (ePat,) <$> check ctx body result
            pure (E.Case eArg eBranches)
        -- an empty match checks against any type
        -- it should be later caught by the exhaustiveness check, though
        (T.Match [], _) -> pure $ E.Match []
        (T.Match branches@((pats, _) : _), ty) ->
            E.Match <$> for branches \(pats, body) -> do
                (ePats, ctx, bodyTy) <- checkPatterns 0 ctx pats ty
                (ePats,) <$> check ctx body bodyTy
          where
            errorMsg actualArgCount = NotEnoughArgumentsInTypeOfMatch{loc, expectedArgCount = length pats, actualArgCount, ty = quote univars ctx.level ty}
            -- todo: when checking a match expression, implicit arguments may appear between other binders
            -- we need to insert new implicit arguments if needed; I'm not sure whether it makes sense to allow
            -- allow an implicit argument in one branch and lack thereof in others
            checkPatterns n ctx (pat :| pats) fnTy = do
                closure <- ensurePi ctx (errorMsg n) fnTy
                -- I'm not sure whether we should quote with
                -- the old context or with the updated context
                let patTy = E.Core $ quote univars ctx.level closure.ty
                ((ePat, patVal), ctx) <- checkPattern ctx pat closure.ty
                innerTy <- closure `appM` patVal
                case nonEmpty pats of
                    Nothing -> pure ((ePat ::: patTy) :| [], ctx, innerTy)
                    Just pats -> do
                        (ePats, ctx, resultTy) <- checkPatterns (succ n) ctx pats innerTy
                        pure (NE.cons (ePat ::: patTy) ePats, ctx, resultTy)
        (T.Record exprRow, V.RecordType (V.Row typeRow ext)) -> do
            let (both, onlyExpr, onlyType) = Row.zipRows exprRow typeRow
            eBoth <- traverse (uncurry $ check ctx) both
            for_ (IsList.toList onlyType) \(_field, _item) -> do
                internalError' "missing field in record" -- typeError $ MissingField (Left $ item :@ loc) field
            eOnlyExpr <- case ext of
                _ | Row.isEmpty onlyExpr -> pure Row.empty
                Nothing -> internalError' "missing field in type"
                -- the extension is a VType, and we want a Row here
                -- perhaps RecordT / VariantT should be single-argument constructors that expect a row?
                Just ext -> do
                    onlyExprAsRec <- check ctx (T.Record onlyExpr :@ loc) (V.RecordType (V.Stuck ext))
                    case onlyExprAsRec of
                        E.Record row -> pure row
                        _ -> internalError' "elaborated a record to a non-record"
            pure $ E.Record (eBoth <> eOnlyExpr)
        (T.Sigma lhs rhs, V.Q Exists Visible _ closure) -> do
            eLhs <- check ctx lhs closure.ty
            env <- extendEnv ctx.env
            let lhsV = eval env eLhs
            rhsTy <- closure `appM` lhsV
            eRhs <- check ctx rhs rhsTy
            pure $ E.Sigma Visible eLhs eRhs
        (T.List items, V.TyCon ListName ((_, itemTy) :< Nil)) -> do
            eItems <- traverse (\item -> check ctx item itemTy) items
            eItemTy <- quoteM ctx.level itemTy
            pure $ E.List (E.Core eItemTy) eItems
        (expr, V.Q Exists vis _ closure) | vis /= Visible -> do
            argV <- freshUniVarV ctx closure.ty
            ty <- closure `appM` argV
            eArg <- E.Core <$> quoteM ctx.level argV
            E.Sigma vis eArg <$> check ctx (expr :@ loc) ty
        (other, expected) -> do
            -- this case happens after the implicit forall case, so we know that we're checking against a monomorphic type here
            --
            -- however, there's a degenerate case where we are checking against a univar and inferring solves it to a polytype
            -- can that ever happen? I'm not sure
            (eTerm, inferred) <- insertNeutralApp ctx =<< infer ctx (other :@ loc)
            unify ctx inferred expected
            pure eTerm
  where
    type_ = V.Type TypeName
    ensurePi ctx errorMsg =
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
            _ -> typeError errorMsg

infer :: TC es => Context -> Term 'Fixity -> Eff es (ETerm, VType)
infer ctx (t :@ loc) = traceScope (\(_, ty) -> prettyDef t <+> specSym "⇒" <+> prettyValCtx ctx ty) $ localLoc loc case t of
    T.Name name -> lookupSig name ctx
    T.Annotation term ty -> do
        vty <- typeFromTerm ctx ty
        (,vty) <$> check ctx term vty
    T.Literal lit -> pure (E.Literal lit, litType)
      where
        litType = V.Type case lit of
            IntLiteral{} -> IntName
            TextLiteral{} -> TextName
            CharLiteral{} -> CharName
    -- this is case is redundant (inferring a function type and then checking an immediate application works just fine),
    -- but since variants are guaranteed to have exactly one argument, checking it right away feels cleaner
    T.App Visible (L (T.Variant con)) payload -> do
        (ePayload, payloadTy) <- infer ctx payload
        rowExt <- freshUniVarS ctx type_
        let ty = V.VariantType $ V.Row (fromList [(con, payloadTy)]) (Just rowExt)
        pure (E.App Visible (E.Variant con) ePayload, ty)
    T.App vis lhs rhs -> do
        (eLhs, lhsTy) <- case vis of
            Visible -> insertApp ctx =<< infer ctx lhs
            _ -> infer ctx lhs
        closure <-
            forceM lhsTy >>= \case
                lhsTy@(V.Q Forall vis2 _e closure)
                    | vis == vis2 -> pure closure
                    | otherwise -> typeError . NoVisibleTypeArgument loc rhs =<< quoteM ctx.level lhsTy
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
    T.Lambda{} -> internalError' "can't infer a type for a non-trivial pattern lambda (yet)"
    -- the type of a pattern lambda has the shape '(x : argTy) -> (case x of pat -> bodyTy)'
    -- this case is broken for the same reason as the `check` case for pattern lambdas
    {-
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
        let bodyTyC = quote univars (ctx.level `incLevel` (E.patternArity ePat + 1)) bodyTy
            body = C.Case (C.Var (Index 0)) [(flattenPattern ePat, bodyTyC)]
            lambdaTy = V.Q Forall vis Retained V.Closure{ty, var = "x", env = ctx.env, body}
        pure (E.Lambda vis ePat eBody, lambdaTy)
    -}
    T.WildcardLambda{} -> internalError' "wip: wildcard lambda"
    T.Let (T.ValueB (T.VarP name :@ _) definition) body -> do
        (eDef, ty) <- infer ctx definition
        env <- extendEnv ctx.env
        (eBody, bodyTy) <- infer (define (unLoc name) (desugar eDef) (eval env eDef) (quote env.univars ctx.level ty) ty ctx) body
        pure (E.Let (E.ValueB (unLoc name) eDef) eBody, bodyTy)
    T.Let{} -> internalError' "destructuring bindings and function bindings are not supported yet"
    T.LetRec{} -> internalError' "let rec not supported yet"
    T.Do{} -> internalError' "do notation not supported yet"
    case'@T.Case{} -> do
        result <- freshUniVarV ctx type_
        (,result) <$> check ctx (case' :@ loc) result
    T.Match [] -> typeError $ EmptyMatch loc
    T.Match (branch : _) -> do
        -- if we try to infer a dependent type for a match, we quiclky run
        -- into non-pattern unification cases, which we don't handle yet
        --
        -- inferring a non-dependent type seems like a reasonable compromise
        env <- extendEnv ctx.env
        fullType <- evalCore env <$> mkNonDependentPi ctx (length branch)
        eBody <- check ctx (t :@ loc) fullType
        pure (eBody, fullType)
    -- we don't infer dependent if, because that would mask type errors a lot of the time
    T.If cond true false -> do
        eCond <- check ctx cond $ V.Type BoolName
        (eTrue, trueTy) <- infer ctx true
        (eFalse, falseTy) <- infer ctx false
        unify ctx trueTy falseTy
        pure (E.If eCond eTrue eFalse, trueTy)
    T.Variant con -> do
        payloadTy <- freshUniVarV ctx type_
        payload <- freshName_ "payload"
        univars <- get
        rowExt <- freshUniVar (bind univars payload payloadTy ctx) type_
        let mkVariant row = C.TyCon RowName ((Visible, row) :< Nil)
        let body = mkVariant $ C.Row $ ExtRow (fromList [(con, quote univars ctx.level payloadTy)]) rowExt
        -- '(x : ?a) -> [| Con ?a | ?r x ]'
        pure (E.Variant con, V.Pi V.Closure{env = ctx.env, ty = payloadTy, var = toSimpleName_ payload, body})
    T.RecordAccess record field -> do
        (eRecord, recordType) <- infer ctx record
        fieldType <- case recordType of
            V.RecordType (V.Row typeRow _) | Just fieldType <- Row.lookup field typeRow -> pure fieldType
            V.RecordType (V.Row _ Nothing) -> internalError' "missing field"
            other -> do
                fieldType <- freshUniVarV ctx type_
                fieldExt <- freshUniVarS ctx (V.Type RowName)
                unify ctx (V.RecordType $ V.Row (fromList [(field, fieldType)]) (Just fieldExt)) other
                pure fieldType
        pure (E.RecordAccess eRecord field, fieldType)
    T.Record row -> do
        (fields, types) <- unzip <$> traverse (infer ctx) row
        pure (E.Record fields, V.RecordType $ V.Row types Nothing)
    T.Sigma lhs rhs -> do
        (eLhs, lhsTy) <- infer ctx lhs
        env <- extendEnv ctx.env
        x <- freshName_ "x"
        (eRhs, rhsTy) <- infer (define x (desugar eLhs) (eval env eLhs) (quote env.univars ctx.level lhsTy) lhsTy ctx) rhs
        univars <- get
        -- I *think* we have to quote with increased level here, but I'm not sure
        let body = quote univars (succ ctx.level) rhsTy
        pure (E.Sigma Visible eLhs eRhs, V.Q Exists Visible Retained $ V.Closure{ty = lhsTy, var = "x", env = ctx.env, body})
    T.List items -> do
        itemTy <- freshUniVar ctx type_
        env <- extendEnv ctx.env
        let itemTyV = evalCore env itemTy
        eItems <- traverse (\item -> check ctx item itemTyV) items
        pure (E.List (E.Core itemTy) eItems, V.TyCon ListName $ fromList [(Visible, itemTyV)])
    T.RecordT row -> do
        eRow <- traverse (\field -> check ctx field type_) row.row
        eExt <- traverse (\ext -> check ctx ext $ V.Type RowName) (Row.extension row)
        pure (E.RecordT $ Row.mkExtRow eRow eExt, type_)
    T.VariantT row -> do
        eRow <- traverse (\field -> check ctx field type_) row.row
        eExt <- traverse (\ext -> check ctx ext $ V.Type RowName) (Row.extension row)
        pure (E.VariantT $ Row.mkExtRow eRow eExt, type_)
    -- normal function syntax is just sugar for 'Π (_ : a) -> b'
    T.Function from to -> do
        eFrom <- check ctx from type_
        env <- extendEnv ctx.env
        x <- freshName_ "_"
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
    type_ = V.Type TypeName

    -- construct a multi-arg non-dependent function type
    -- ?a -> ?b -> ?c -> ?d
    mkNonDependentPi ctx n = do
        argTypes <- replicateM n (freshUniVar ctx type_)
        resultType <- freshUniVar ctx type_
        pure $ foldr (C.Q Forall Visible Retained "_") (C.lift n resultType) $ zipWith C.lift [0 ..] argTypes

-- check a term against Type and evaluate it
typeFromTerm :: TC es => Context -> Term 'Fixity -> Eff es VType
typeFromTerm ctx term = do
    eTerm <- check ctx term (V.Type TypeName)
    env <- extendEnv ctx.env
    pure $ eval env eTerm

checkPattern :: TC es => Context -> Pattern 'Fixity -> VType -> Eff es ((EPattern, Value), Context)
checkPattern ctx (pat :@ pLoc) ty = do
    univars <- get
    traceScope_ (prettyDef pat <+> specSymBlue "⇐" <+> prettyValCtx ctx ty) $ localLoc pLoc case pat of
        T.VarP (L name) -> do
            let value = V.Var ctx.level
            pure ((E.VarP (toSimpleName_ name), value), bind univars name ty ctx)
        T.WildcardP txt -> do
            name <- freshName_ $ Name' txt
            let value = V.Var ctx.level
            pure ((E.WildcardP txt, value), bind univars name ty ctx)
        T.ConstructorP (L name) args -> do
            conMeta <-
                asks @ConMetaTable (Map.lookup name) >>= \case
                    Just conMeta -> pure conMeta
                    Nothing -> internalError' $ "no constructor metadata for" <+> prettyDef name
            (goalType, argsOrParams) <- getConMetadata conMeta ctx
            (argsWithVals, actualType, ctx) <- inferConArgs pLoc ctx argsOrParams args
            unify ctx goalType ty
            ctx <- refine ctx actualType ty
            let (eArgs, argVals) = unzip argsWithVals
                valsWithVis = zip (map fst eArgs) argVals
            pure ((E.ConstructorP name eArgs, V.Con name (fromList valsWithVis)), ctx)
        T.VariantP con arg ->
            forceM ty >>= \case
                V.VariantType (V.Row row _) | Just argType <- Row.lookup con row -> do
                    ((eArg, argV), ctx) <- checkPattern ctx arg argType
                    pure ((E.VariantP con eArg, V.Variant con argV), ctx)
                _ -> fallthroughToInfer
        T.RecordP row ->
            forceM ty >>= \case
                V.RecordType (V.Row typeRow ext) -> do
                    let (both, onlyPat, _) = Row.zipRows row typeRow
                    (eBoth, ctx) <- runState ctx $ for (Row.sortedRow both) \(field, (pat, ty)) -> do
                        ctx <- get
                        (ePat, ctx) <- checkPattern ctx pat ty
                        put ctx
                        pure (field, ePat)
                    (eOnlyPat, onlyPatVals, ctx) <- case ext of
                        _ | Row.isEmpty onlyPat -> pure ([], Row.empty, ctx)
                        Nothing -> internalError' "missing fields in record type"
                        Just e -> do
                            newExt <- freshUniVarS ctx $ V.Type RowName
                            (eOnlyPat, onlyPatVals, fieldTypes, ctx) <- inferRow ctx (Row.sortedRow onlyPat) (Just newExt)
                            unify ctx (V.Stuck e) fieldTypes
                            pure (eOnlyPat, onlyPatVals, ctx)
                    let (eBoth', bothVals) = unzip $ map (\(k, (p, v)) -> ((k, p), (k, v))) eBoth
                        eRow = eBoth' <> eOnlyPat
                        values = fromList bothVals <> onlyPatVals
                    pure ((E.RecordP $ fromList eRow, V.Record values), ctx)
                _ -> fallthroughToInfer
        T.SigmaP vis lhs rhs -> do
            forceM ty >>= \case
                V.Q Exists vis2 _e closure
                    | vis /= vis2 -> typeError SigmaVisibilityMismatch{loc = getLoc lhs, expectedVis = vis, actualVis = vis2}
                    | otherwise -> do
                        ((eLhs, lhsV), ctx) <- checkPattern ctx lhs closure.ty
                        ((eRhs, rhsV), ctx) <- checkPattern ctx rhs =<< closure `appM` lhsV
                        pure ((E.SigmaP vis eLhs eRhs, V.Sigma vis lhsV rhsV), ctx)
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
    traceScope (\(_, ty, ctx) -> prettyDef p <+> specSym "⇒" <+> prettyValCtx ctx ty) $ localLoc loc case p of
        T.VarP (L name) -> do
            ty <- freshUniVarV ctx type_
            let value = V.Var ctx.level
            pure ((E.VarP (toSimpleName_ name), value), ty, bind univars name ty ctx)
        T.WildcardP txt -> do
            name <- freshName_ $ Name' txt
            ty <- freshUniVarV ctx type_
            let value = V.Var ctx.level
            pure ((E.WildcardP txt, value), ty, bind univars name ty ctx)
        (T.AnnotationP pat ty) -> do
            tyV <- typeFromTerm ctx ty
            (ePat, newLocals) <- checkPattern ctx pat tyV
            pure (ePat, tyV, newLocals)
        T.ConstructorP (L name) args -> do
            conMeta <-
                asks @ConMetaTable (Map.lookup name) >>= \case
                    Just conMeta -> pure conMeta
                    Nothing -> internalError' $ "no constructor metadata for" <+> prettyDef name
            (goalType, argsOrParams) <- getConMetadata conMeta ctx
            (argsWithVals, actualType, ctx) <- inferConArgs loc ctx argsOrParams args
            unify ctx actualType goalType
            let (eArgs, argVals) = unzip argsWithVals
                valsWithVis = zip (map fst eArgs) argVals
            pure ((E.ConstructorP name eArgs, V.Con name (fromList valsWithVis)), goalType, ctx)
        T.SigmaP{} -> internalError' "todo: not sure how to infer sigma"
        -- list patterns should be desugared later on
        T.ListP pats -> do
            itemType <- freshUniVarV ctx type_
            let listType = V.TyCon ListName $ fromList [(Visible, itemType)]
                patToCheck = case pats of
                    [] -> T.ConstructorP (NilName :@ loc) [] :@ loc
                    (pat : pats) -> T.ConstructorP (ConsName :@ loc) [(Visible, pat), (Visible, T.ListP pats :@ loc)] :@ loc
            (ePat, ctx) <- checkPattern ctx patToCheck listType
            pure (ePat, listType, ctx)
        T.LiteralP lit -> pure ((E.LiteralP lit, V.PrimValue lit), litType, ctx)
          where
            litType = V.Type case lit of
                IntLiteral{} -> IntName
                TextLiteral{} -> TextName
                CharLiteral{} -> CharName
        T.VariantP con arg -> do
            ext <- freshUniVarS ctx (V.Type RowName)
            ((eArg, argV), patType, ctx) <- inferPattern ctx arg
            pure ((E.VariantP con eArg, V.Variant con argV), V.VariantType $ V.Row (fromList [(con, patType)]) (Just ext), ctx)
        -- since records are non-dependent, inferring fields one-by-one like this and passing the context is a bit too permissive
        -- it shouldn't lead to unsoundness, but it might produce a cryptic type error somewhere else
        T.RecordP row -> do
            ext <- freshUniVarS ctx $ V.Type RowName
            (eRow, valueRow, rowType, ctx) <- inferRow ctx (Row.sortedRow row) (Just ext)
            pure ((E.RecordP (fromList eRow), V.Record valueRow), V.RecordType rowType, ctx)
  where
    type_ = V.Type TypeName

inferRow
    :: TC es => Context -> [(OpenName, Pattern 'Fixity)] -> Maybe V.Stuck -> Eff es ([(OpenName, EPattern)], Row Value, VType, Context)
inferRow ctx row mbExt = do
    (eRow, ctx) <- runState ctx $ for row \(field, pat) -> do
        ctx <- get
        (ePat, val, ctx) <- inferPattern ctx pat
        put ctx
        pure (field, ePat, val)
    let rowType = V.Row (fromList $ map (\(field, _, ty) -> (field, ty)) eRow) mbExt
        (patRow, values) = unzip $ map (\(k, (p, v), _) -> ((k, p), (k, v))) eRow
    pure (patRow, fromList values, rowType, ctx)

inferConArgs
    :: TC es
    => Loc
    -> Context
    -> ConArgList
    -> [(Visibility, Pattern 'Fixity)]
    -> Eff es ([((Visibility, EPattern), Value)], VType, Context)
inferConArgs loc ctx = \cases
    (FinalType ty) [] -> pure ([], ty, ctx)
    arg@Arg{vis, ty} ((vis2, pat) : pats) | vis == vis2 -> do
        (((ePat, patV), ctx), rest) <- case arg of
            UsedInType{unifyWith, rest} -> do
                (ePat@(_, patV), ctx) <- checkPattern ctx pat ty
                ctx <- refine ctx patV unifyWith
                pure ((ePat, ctx), rest)
            UnusedInType{mkRest} -> do
                checked@((_, patV), _) <- checkPattern ctx pat ty
                pure (checked, mkRest patV)
            FinalType{} -> error "[bug] Arg matches FinalType"
        (pats, ty, ctx) <- inferConArgs loc ctx rest pats
        pure (((vis, ePat), patV) : pats, ty, ctx)
    arg@Arg{vis, name, ty} pats | vis /= Visible -> do
        name <- freshName_ name
        (((insertedPat, insertedVal), ctx), rest) <- case arg of
            UsedInType{unifyWith, rest} -> do
                (inserted@(_, insertedVal), ctx) <- checkPattern ctx (T.VarP (name :@ loc) :@ loc) ty
                ctx <- refine ctx insertedVal unifyWith
                pure ((inserted, ctx), rest)
            UnusedInType{mkRest} -> do
                checked@((_, patV), _) <- checkPattern ctx (T.VarP (name :@ loc) :@ loc) ty
                pure (checked, mkRest patV)
            FinalType{} -> error "[bug] Arg matches FinalType"
        (pats, ty, ctx) <- inferConArgs loc ctx rest pats
        pure (((vis, insertedPat), insertedVal) : pats, ty, ctx)
    Arg{} (_ : _) -> typeError ConstructorVisibilityMismatch{loc}
    FinalType{} (_ : _) -> typeError TooManyArgumentsInPattern{loc}
    Arg{} [] -> typeError NotEnoughArgumentsInPattern{loc}
