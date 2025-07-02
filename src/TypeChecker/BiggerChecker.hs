{-# LANGUAGE RecordWildCards #-}

module TypeChecker.BiggerChecker where

import Common
import Diagnostic
import Effectful.Reader.Static
import Effectful.State.Static.Local (State, get, modify)
import Eval (ExtendedEnv (..), UniVars, ValueEnv, app', captured, eval, force', quote, resugar)
import IdMap qualified as Map
import LangPrelude
import NameGen (freshName_)
import Syntax
import Syntax.Core qualified as C
import Syntax.Declaration qualified as D
import Syntax.Elaborated (Typed (..))
import Syntax.Elaborated qualified as E
import Syntax.Row (ExtRow (..))
import Syntax.Term (Erasure (..), Quantifier (..), Visibility (..))
import Syntax.Term qualified as T
import Syntax.Value qualified as V
import TypeChecker.TypeError (TypeError (..), typeError)
import TypeChecker.Unification

-- long story short, this is a mess. In the future, DependencyResolution should return declarations in a more structured format
processDeclaration
    :: (TC es, State TopLevel :> es) => Context -> Declaration 'Fixity -> Eff es (EDeclaration, IdMap Name_ Value -> IdMap Name_ Value)
processDeclaration ctx (decl :@ loc) = case decl of
    D.Signature name sig -> do
        sigV <- removeUniVars ctx.level =<< typeFromTerm ctx sig
        univars <- get @UniVars
        let eSig = resugar $ quote univars ctx.level sigV
        pure (E.SignatureD name eSig, Map.insert (unLoc name) sigV)
    D.Value binding (_ : _) -> internalError (getLoc binding) "todo: proper support for where clauses"
    D.Value (T.ValueB (L (T.VarP name)) body) [] -> do
        topLevel <- get @TopLevel
        eBody <- case Map.lookup (unLoc name) topLevel of
            Just sig -> check ctx body sig
            Nothing -> do
                (eBody, ty) <- traverse (removeUniVars ctx.level) =<< infer ctx body
                modify @TopLevel $ Map.insert (unLoc name) ty
                pure eBody
        env <- extendEnv ctx.env
        val <- eval loc env eBody
        pure (E.ValueD (E.ValueB name eBody), Map.insert (unLoc name) val)
    D.Value T.ValueB{} [] -> internalError loc "pattern destructuring bindings are not supported yet"
    -- this case is way oversimplified for now, we don't even allow recursion for untyped bindings
    D.Value (T.FunctionB name args body) [] -> do
        topLevel <- get @TopLevel
        let asLambda = foldr (\var -> (:@ getLoc body) . T.Lambda var) body args
        eLambda <- case Map.lookup (unLoc name) topLevel of
            Just sig -> check ctx asLambda sig
            Nothing -> do
                (eLambda, ty) <- infer ctx asLambda
                modify @TopLevel $ Map.insert (unLoc name) ty
                pure eLambda
        env <- extendEnv ctx.env
        val <- eval loc env eLambda
        -- ideally, we should unwrap 'eLambda' and construct a FunctionB here
        pure (E.ValueD (E.ValueB name eLambda), Map.insert (unLoc name) val)
    D.GADT name mbKind constrs -> do
        -- we can probably infer the kind of a type from its constructors, but we don't do that for now
        kind <- maybe (pure $ V.Type (TypeName :@ getLoc name)) (typeFromTerm ctx) mbKind
        modify @TopLevel $ Map.insert (unLoc name) kind
        let newCtx = ctx{env = ctx.env{V.topLevel = Map.insert (unLoc name) kind ctx.env.topLevel}}
        for_ constrs \con -> do
            conSig <- removeUniVars newCtx.level =<< typeFromTerm newCtx con.sig
            checkGadtConstructor ctx.level name con.name conSig
            modify @TopLevel $ Map.insert (unLoc con.name) conSig
        -- todo: add GADT constructors to the constructor table
        pure (E.TypeD name (map (\con -> (con.name, argCount con.sig)) constrs), Map.insert (unLoc name) (V.TyCon name []))
    D.Type name binders constrs -> do
        kind <- removeUniVars ctx.level =<< mkTypeKind binders
        modify $ Map.insert (unLoc name) kind
        let newCtx = ctx{env = ctx.env{V.topLevel = Map.insert (unLoc name) kind ctx.env.topLevel}}
        for_ (mkConstrSigs name binders constrs) \(con, sig) -> do
            sigV <- removeUniVars newCtx.level =<< typeFromTerm newCtx sig
            modify @TopLevel $ Map.insert (unLoc con) sigV
        -- _conMapEntry <- mkConstructorTableEntry (map (.var) binders) (map (\con -> (con.name, con.args)) constrs)
        pure (E.TypeD name (map (\con -> (con.name, length con.args)) constrs), Map.insert (unLoc name) (V.TyCon name []))
  where
    -- no dependent kinds for now
    mkTypeKind = \case
        [] -> pure $ V.Type (TypeName :@ loc)
        (binder : rest) -> V.Function <$> typeFromTerm ctx (T.binderKind binder) <*> mkTypeKind rest

    mkConstrSigs :: Name -> [VarBinder 'Fixity] -> [Constructor 'Fixity] -> [(Name, Type 'Fixity)]
    mkConstrSigs name binders constrs =
        constrs <&> \(D.Constructor loc' con params) ->
            ( con
            , foldr
                (\var -> Located loc' . T.Q Forall Implicit Erased var)
                (foldr (\lhs -> Located loc' . T.Function lhs) (fullType loc') params)
                binders
            )
      where
        fullType loc' = foldl' (\lhs -> Located loc' . T.App lhs) (Located (getLoc name) $ T.Name name) (Located loc' . T.Name . (.var) <$> binders)

    -- constructors should be reprocessed into a more convenenient form somewhere else, but I'm not sure where
    argCount = go 0
      where
        go acc (L e) = case e of
            T.Function _ rhs -> go (succ acc) rhs
            T.Q Forall Visible _ _ body -> go (succ acc) body
            T.Q _ _ _ _ body -> go acc body
            _ -> acc

    -- check that a GADT constructor actually returns the declared type
    checkGadtConstructor :: TC es => Level -> Name -> Name -> VType -> Eff es ()
    checkGadtConstructor lvl tyName con conTy = do
        univars <- get @UniVars
        case unwrapApp (fnResult $ quote univars lvl conTy) of
            (C.Name name, _)
                | name /= tyName -> typeError $ ConstructorReturnType{con, expected = tyName, returned = name}
                | otherwise -> pass
            _ -> internalError (getLoc con) "something weird in a GADT constructor type"
      where
        fnResult = \case
            (C.Function _ rhs) -> fnResult rhs
            (C.Q _ _ _ _ _ rhs) -> fnResult rhs
            other -> other
        unwrapApp = go []
          where
            go acc = \case
                (C.App lhs rhs) -> go (rhs : acc) lhs
                other -> (other, acc)

check :: TC es => Context -> Term 'Fixity -> VType -> Eff es ETerm
check ctx (t :@ loc) ty = do
    ty' <- force' ty
    case (t, ty') of
        -- we can check against a dependent type, but I'm not sure how
        (T.If cond true false, _) -> do
            eCond <- check ctx cond $ V.Type (BoolName :@ loc)
            eTrue <- check ctx true ty'
            eFalse <- check ctx false ty'
            pure (E.If eCond eTrue eFalse)
        (other, expected) -> do
            (eTerm, inferred) <- infer ctx $ other :@ loc
            unify ctx.env.topLevel ctx.level inferred expected
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
    T.App lhs rhs -> do
        (eLhs, lhsTy) <- infer ctx lhs
        (argTy, closure) <-
            force' lhsTy >>= \case
                V.Pi closure -> pure (closure.ty, closure)
                other -> do
                    argTy <- freshUniVarV ctx
                    x <- freshName_ (Name' "x")
                    closure <- V.Closure (toSimpleName_ x) argTy ctx.env <$> freshUniVar (bind x argTy ctx)
                    unify ctx.env.topLevel ctx.level (V.Pi closure) other
                    pure (argTy, closure)
        eRhs <- check ctx rhs argTy
        resultTy <- closure `app'` lhsTy
        pure (E.App eLhs eRhs, resultTy)
    T.TypeApp{} -> internalError loc "wip: type app"
    T.Lambda (L (T.VarP arg)) body -> do
        ty <- freshUniVarV ctx
        (eBody, bodyTy) <- infer (bind (unLoc arg) ty ctx) body
        univars <- get @UniVars
        let var = toSimpleName_ $ unLoc arg
            argTy = resugar $ quote univars ctx.level ty
            quotedBody = quote univars (succ ctx.level) bodyTy
        pure (E.Lambda (E.VarP var ::: argTy) eBody, V.Pi V.Closure{ty, var, env = ctx.env, body = quotedBody})
    T.Lambda{} -> internalError loc "wip: pattern matching lambda"
    T.WildcardLambda{} -> internalError loc "wip: wildcard lambda"
    T.Let (T.ValueB (T.VarP name :@ nameLoc) definition) body -> do
        (eDef, ty) <- infer ctx definition
        env <- extendEnv ctx.env
        val <- eval nameLoc env eDef
        (eBody, bodyTy) <- infer (define (unLoc name) val ty ctx) body
        pure (E.Let (E.ValueB name eDef) eBody, bodyTy)
    T.Let{} -> internalError loc "destructuring bindings and function bindings are not supported yet"
    T.LetRec{} -> internalError loc "let rec not supported yet"
    T.Do{} -> internalError loc "do notation not supported yet"
    T.Case{} -> internalError loc "wip: case"
    T.Match{} -> internalError loc "wip: match"
    -- we don't infer dependent if, because that would mask type errors a lot of time
    T.If cond true false -> do
        eCond <- check ctx cond $ V.Type (BoolName :@ loc)
        (eTrue, trueTy) <- infer ctx true
        (eFalse, falseTy) <- infer ctx false
        unify ctx.env.topLevel ctx.level trueTy falseTy
        pure (E.If eCond eTrue eFalse, trueTy)
    T.Variant con -> do
        payloadTy <- freshUniVarV ctx
        rowExt <- freshUniVarV ctx
        -- todo: we can infer '(x : ?a) -> [| Con ?a | ?r x ]'
        pure (E.Variant con, V.Function rowExt (V.VariantT $ ExtRow (fromList [(con, payloadTy)]) rowExt))
    T.RecordAccess{} -> internalError loc "wip: record access"
    T.Record{} -> internalError loc "wip: record"
    T.Sigma lhs rhs -> do
        (eLhs, lhsTy) <- infer ctx lhs
        env <- extendEnv ctx.env
        lhsVal <- eval loc env eLhs
        x <- freshName_ $ Name' "x"
        (eRhs, rhsTy) <- infer (define x lhsVal lhsTy ctx) rhs
        univars <- get @UniVars
        -- I *think* we have to quote with increased level here, but I'm not sure
        let body = quote univars (succ ctx.level) rhsTy
        pure (E.Sigma eLhs eRhs, V.Q Exists Visible Retained $ V.Closure{ty = lhsTy, var = Name' "x", env = ctx.env, body})
    T.List items -> do
        itemTy <- freshUniVarV ctx
        eItems <- traverse (\item -> check ctx item itemTy) items
        pure (E.List eItems, itemTy)
    T.RecordT row -> do
        eRow <- traverse (\field -> check ctx field type_) row
        pure (E.RecordT eRow, type_)
    T.VariantT row -> do
        eRow <- traverse (\field -> check ctx field type_) row
        pure (E.VariantT eRow, type_)
    T.Function from to -> do
        eFrom <- check ctx from type_
        eTo <- check ctx to type_
        pure (E.Function eFrom eTo, type_)
    T.Q q v e binder body -> do
        tyV <- maybe (freshUniVarV ctx) (typeFromTerm ctx) binder.kind
        eBody <- check (bind (unLoc binder.var) tyV ctx) body type_
        univars <- get @UniVars
        let eTy = resugar $ quote univars ctx.level tyV
        pure (E.Q q v e (unLoc (toSimpleName binder.var) ::: eTy) eBody, type_)
  where
    {-
    type Sigma : (a : Type) -> (f : a -> Type) -> Type where
        Pair : (x : 'a) -> 'f x -> Sigma 'a 'f

    type Sigma a (f : a -> Type) =
        Pair (x : a) (f x)
    -}

    type_ = V.Type $ TypeName :@ loc

-- check a term against Type and evaluate it
typeFromTerm :: TC es => Context -> Term 'Fixity -> Eff es VType
typeFromTerm ctx term = do
    eTerm <- check ctx term (V.Type (TypeName :@ getLoc term))
    env <- extendEnv ctx.env
    eval (getLoc term) env eTerm

-- | extend the value environment with current UniVar state for pure evaluation
extendEnv :: TC es => ValueEnv -> Eff es ExtendedEnv
extendEnv V.ValueEnv{..} = do
    univars <- get @UniVars
    pure ExtendedEnv{..}

-- * helpers (will be the new TypeChecker.Backend)

bind :: Name_ -> VType -> Context -> Context
bind name ty Context{env = V.ValueEnv{locals, ..}, ..} =
    Context
        { level = succ level
        , env = V.ValueEnv{locals = V.Var level : locals, ..}
        , types = Map.insert name (level, ty) types
        , bounds = C.Bound : bounds
        }

define :: Name_ -> Value -> VType -> Context -> Context
define name val ty Context{env = V.ValueEnv{locals, ..}, ..} =
    Context
        { level = succ level
        , env = V.ValueEnv{locals = val : locals, ..}
        , types = Map.insert name (level, ty) types
        , bounds = C.Defined : bounds
        }

-- todo: this should handle globals
lookupSig :: TC es => Name -> Context -> Eff es (ETerm, VType)
lookupSig name ctx = do
    topLevel <- ask @TopLevel
    case (Map.lookup (unLoc name) ctx.types, Map.lookup (unLoc name) topLevel) of
        (Just (lvl, ty), _) -> pure (E.Var (levelToIndex ctx.level lvl), ty)
        (_, Just ty) -> pure (E.Name name, ty)
        (Nothing, Nothing) -> internalError' $ pretty name <+> "not in scope"

{- | replace solved univars with their solutions and unsolved univars with a placeholder type
in the future, unsolved unis should get converted to a forall with the appropriate type
-}
removeUniVars :: TC es => Level -> Value -> Eff es Value
removeUniVars lvl = go
  where
    go =
        force' >=> \case
            V.TyCon name args -> V.TyCon name <$> traverse go args
            V.Con name args -> V.Con name <$> traverse go args
            V.Lambda closure@V.Closure{var, env = V.ValueEnv{topLevel}} -> do
                newBody <- removeUniVars (succ lvl) =<< closure `app'` V.Var lvl
                univars <- get @UniVars
                let emptyEnv = V.ValueEnv{topLevel, locals = []}
                pure $ V.Lambda V.Closure{var, ty = (), env = emptyEnv, body = quote univars (succ lvl) newBody}
            V.PrimFunction fn -> do
                captured <- traverse go fn.captured
                pure $ V.PrimFunction fn{captured}
            V.Record row -> V.Record <$> traverse go row
            V.Variant name arg -> V.Variant name <$> go arg
            V.Sigma lhs rhs -> V.Sigma <$> go lhs <*> go rhs
            V.PrimValue lit -> pure $ V.PrimValue lit
            V.Function from to -> V.Function <$> go from <*> go to
            V.Q q v e closure@V.Closure{var, env = V.ValueEnv{topLevel}} -> do
                ty <- go closure.ty
                newBody <- removeUniVars (succ lvl) =<< closure `app'` V.Var lvl
                univars <- get @UniVars
                let emptyEnv = V.ValueEnv{topLevel, locals = []}
                pure $ V.Q q v e V.Closure{var, ty, env = emptyEnv, body = quote univars (succ lvl) newBody}
            V.RecordT row -> V.RecordT <$> traverse go row
            V.VariantT row -> V.VariantT <$> traverse go row
            V.Stuck stuck -> V.Stuck <$> goStuck stuck
    goStuck = \case
        V.VarApp vlvl spine -> V.VarApp vlvl <$> traverse go spine
        -- if we reach this case, it means the univar is still unsolved
        -- in the future, we will collect all unsolved unis and convert them to
        -- a forall clause
        uniApp@V.UniVarApp{} -> pure uniApp
        V.Fn fn arg -> do
            captured <- traverse go fn.captured
            V.Fn fn{captured} <$> goStuck arg
        V.Case _arg _matches -> internalError' "todo: remove univars from stuck case" -- V.Case <$> goStuck arg <*> _ matches
