{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE PatternSynonyms #-}

module Eval where

import Common (
    Literal,
    Loc (..),
    Located (..),
    Name,
    Name_ (ConsName, NilName, TrueName, TypeName),
    Pass (..),
    SimpleName_ (Name'),
    Skolem,
    UniVar,
    getLoc,
    toSimpleName,
    unLoc,
    pattern L,
 )
import Data.EnumMap.Lazy qualified as LMap -- note that we use the lazy functions here
import Data.Traversable (for)
import Diagnostic
import LangPrelude
import NameGen (NameGen, freshName)
import Prettyprinter (line, vsep)
import Syntax
import Syntax.Core qualified as C
import Syntax.Declaration qualified as D
import Syntax.Row (ExtRow (..), OpenName)
import Syntax.Row qualified as Row
import Syntax.Term (Erased, Quantifier, Visibility (..))
import Syntax.Term qualified as T
import Prelude qualified (Show (..))

data ValueEnv = ValueEnv
    { values :: EnumMap Name Value
    , skolems :: EnumMap Skolem Value
    }
type Type' = Value

-- unlike the AST types, the location information on Values are shallow, since
-- the way we use it is difference from the AST nodes
-- in AST, the location corresponds to the source span where the AST node is written
-- in Values, the location is the source space that the location is *arising from*
data Value
    = Var Name -- an unbound variable; seems like they are only used for quoting, hmmm
    | TyCon Name -- a type constructor. unlike value constructors, `Either a b` is represented as a stuck application Either `App` a `App` b
    | Con Name [Value] -- a fully-applied counstructor
    | Lambda (Closure ())
    | PrimFunction Name (Value -> Value) -- an escape hatch for interpreter primitives and similar stuff
    | Record (Row Value)
    | Variant OpenName Value
    | -- | RecordLens (NonEmpty OpenName)
      PrimValue Literal -- the name 'Literal' is slightly misleading here
    | -- types
      Function Type' Type'
    | Q Quantifier Visibility Erased (Closure Type')
    | VariantT (ExtRow Type')
    | RecordT (ExtRow Type')
    | -- stuck computations
      App Value ~Value
    | Case Value [(CorePattern, Value)]
    | -- typechecking metavars
      UniVar UniVar
    | Skolem Skolem

data Closure ty = Closure {var :: Name, ty :: ty, env :: ValueEnv, body :: CoreTerm}

quote :: Located Value -> CoreTerm
quote (Located loc value) = Located loc case value of
    Var x -> C.Name x
    TyCon name -> C.TyCon name
    Con con args -> C.Con con (map quote (Located loc <$> args))
    -- if we use quote for anything but pretty-printing,
    -- we'd probably need alpha conversion for all the function-like cases
    Lambda closure -> C.Lambda closure.var (quoteWithLoc $ closureBody closure)
    PrimFunction name f -> unLoc . quoteWithLoc $ f (Var name)
    Record vals -> C.Record $ fmap quoteWithLoc vals
    Variant name val -> C.App (Located (getLoc name) $ C.Variant name) $ quoteWithLoc val
    -- RecordLens path -> RecordLens path
    PrimValue lit -> C.Literal lit
    Function l r -> C.Function (quoteWithLoc l) (quoteWithLoc r)
    Q q vis e closure -> C.Q q vis e closure.var (quoteWithLoc closure.ty) $ quoteWithLoc (closureBody closure)
    VariantT row -> C.VariantT $ fmap quoteWithLoc row
    RecordT row -> C.RecordT $ fmap quoteWithLoc row
    App lhs rhs -> C.App (quoteWithLoc lhs) (quoteWithLoc rhs)
    Case arg cases -> C.Case (quoteWithLoc arg) $ (fmap . fmap) quoteWithLoc cases
    Skolem skolem -> C.Skolem skolem
    UniVar uni -> C.UniVar uni
  where
    quoteWithLoc = quote . Located loc

instance Pretty Value where
    pretty = pretty . quote . Located Blank

instance Show Value where
    show = Prelude.show . pretty

evalCore :: ValueEnv -> CoreTerm -> Value
evalCore !env (L term) = case term of
    -- note that env is a lazy enummap, so we only force the outer structure here
    C.Name name -> fromMaybe (error . show $ "whoopsie, out of scope" <+> pretty name) $ LMap.lookup name env.values
    C.TyCon name -> TyCon name
    C.Con name args -> Con name $ map (evalCore env) args
    C.Lambda name body -> Lambda $ Closure{var = name, ty = (), env, body}
    C.App (L (C.Variant name)) arg -> Variant name $ evalCore env arg -- this is a bit of an ugly case
    C.App lhs rhs -> case (evalCore env lhs, evalCore env rhs) of
        (Lambda closure, arg) -> closure `app` arg
        (other, arg) -> App other arg
    C.Case arg matches ->
        let val = evalCore env arg
         in fromMaybe
                (error $ show $ "pattern mismatch when matching " <+> pretty val <+> "with:" <> line <> vsep (map (pretty . fst) matches))
                . (<|> mbStuckCase val matches)
                . asum
                $ matches <&> \(pat, body) -> evalCore <$> matchCore env pat val <*> pure body
    C.Let name expr body ->
        let newEnv = env{values = LMap.insert name (evalCore env expr) env.values}
         in evalCore newEnv body
    C.Literal lit -> PrimValue lit
    C.Record row -> Record $ evalCore env <$> row
    C.Variant _name -> error "todo: seems like evalCore needs namegen" -- Lambda (Located Blank $ Name' "x") $ C.Variant name `C.App`
    C.Function lhs rhs -> Function (evalCore env lhs) (evalCore env rhs)
    C.Q q vis e var ty body -> Q q vis e $ Closure{var, ty = evalCore env ty, env, body}
    C.VariantT row -> VariantT $ evalCore env <$> row
    C.RecordT row -> RecordT $ evalCore env <$> row
    -- should normal evaluation resolve univars?
    C.Skolem skolem -> Skolem skolem
    C.UniVar uni -> UniVar uni
  where
    mbStuckCase (Var x) matches = Just $ Case (Var x) (mkStuckBranches matches)
    mbStuckCase (Skolem s) matches = Just $ Case (Skolem s) (mkStuckBranches matches)
    mbStuckCase (UniVar u) matches = Just $ Case (UniVar u) (mkStuckBranches matches)
    mbStuckCase (App lhs rhs) matches = Just $ Case (App lhs rhs) (mkStuckBranches matches)
    mbStuckCase _ _ = Nothing

    mkStuckBranches :: [(CorePattern, CoreTerm)] -> [(CorePattern, Value)]
    mkStuckBranches = map \(pat, body) -> (pat, evalCore (stuckBranchEnv pat) body)

    stuckBranchEnv :: CorePattern -> ValueEnv
    stuckBranchEnv = \case
        (C.VarP name) -> env{values = LMap.insert name (Var name) env.values}
        (C.ConstructorP _ argNames) -> env{values = LMap.fromList (argNames <&> \arg -> (arg, Var arg)) <> env.values}
        (C.VariantP _ argName) -> env{values = LMap.insert argName (Var argName) env.values}
        _ -> env

app :: Closure a -> Value -> Value
app Closure{var, env, body} arg = evalCore (env{values = LMap.insert var arg env.values}) body

-- do we need a fresh name here?
closureBody :: Closure a -> Value
closureBody closure = closure `app` Var closure.var

closureBody' :: NameGen :> es => Closure a -> Eff es Value
closureBody' closure = do
    var <- freshName $ toSimpleName closure.var
    pure $ closure `app` Var var

matchCore :: ValueEnv -> CorePattern -> Value -> Maybe ValueEnv
matchCore env = \cases
    (C.VarP name) val -> Just $ env{values = LMap.insert name val env.values}
    C.WildcardP{} _ -> Just env
    (C.ConstructorP pname argNames) (Con name args)
        | pname == name && length argNames == length args ->
            Just $ env{values = foldl' (flip $ uncurry LMap.insert) env.values (zip argNames args)}
    (C.VariantP pname argName) (Variant name val)
        | pname == name -> Just $ env{values = LMap.insert argName val env.values}
    (C.RecordP varRow) (Record row) ->
        let (pairs, _, _) = Row.zipRows varRow row
         in Just $ env{values = foldl' (flip $ uncurry LMap.insert) env.values pairs}
    (C.LiteralP lit) (PrimValue (L val)) -> env <$ guard (lit == val)
    _ _ -> Nothing

-- desugar could *almost* be pure, but unfortunately, we need name gen here
-- perhaps we should use something akin to locally nameless?
-- TODO: properly handle recursive bindings (that is, don't infinitely loop on them)
desugar :: forall es. (NameGen :> es, Diagnose :> es) => Term 'Fixity -> Eff es CoreTerm
desugar = go
  where
    go :: Term 'Fixity -> Eff es CoreTerm
    go (Located loc e) =
        Located loc <$> case e of
            T.Name name -> pure $ C.Name name
            T.Literal lit -> pure $ C.Literal lit
            T.Annotation expr _ -> unLoc <$> go expr
            T.App lhs rhs -> C.App <$> go lhs <*> go rhs
            T.Lambda (L (T.VarP arg)) body -> C.Lambda arg <$> go body
            T.Lambda pat body -> do
                name <- freshName $ Located loc $ Name' "lamArg"
                C.Lambda name <$> go (Located loc $ T.Case (Located (getLoc name) $ T.Name name) [(pat, body)])
            T.WildcardLambda args body -> do
                body' <- go body
                pure . unLoc $ foldr (\arg -> Located loc . C.Lambda arg) body' args
            T.Let binding expr -> case binding of
                T.ValueB (L (T.VarP name)) body -> C.Let name <$> go body <*> go expr
                T.ValueB _ _ -> internalError loc "todo: desugar pattern bindings"
                T.FunctionB name args body -> C.Let name <$> go (foldr (\x -> Located loc . T.Lambda x) body args) <*> go expr
            T.LetRec _bindings _body -> internalError loc "todo: letrec desugar"
            T.TypeApp expr _ -> unLoc <$> go expr
            T.Case arg matches -> C.Case <$> go arg <*> traverse (bitraverse flattenPattern go) matches
            T.Match matches@(([_], _) : _) -> do
                name <- freshName $ Located Blank $ Name' "matchArg"
                matches' <- for matches \case
                    ([pat], body) -> bitraverse flattenPattern desugar (pat, body)
                    _ -> internalError loc "inconsistent pattern count in a match expression"
                pure $ C.Lambda name $ Located loc $ C.Case (nameLoc name) matches'
            T.Match _ -> internalError loc "todo: multi-arg match desugar"
            T.If cond true false -> do
                cond' <- go cond
                true' <- go true
                false' <- go false
                pure . C.Case cond' $
                    [ (C.ConstructorP (Located (getLoc cond) TrueName) [], true')
                    , (C.WildcardP "", false')
                    ]
            T.RecordLens _ -> internalError loc "todo: desugar RecordLens"
            T.Variant name -> pure $ C.Variant name
            T.Record fields -> C.Record <$> traverse go fields
            T.List xs -> unLoc . foldr (appLoc . appLoc cons) nil <$> traverse go xs
            T.Do{} -> error "todo: desugar do blocks"
            T.Function from to -> C.Function <$> go from <*> go to
            T.Q q vis er binder body -> C.Q q vis er binder.var <$> maybe type_ desugar binder.kind <*> go body
            T.VariantT row -> C.VariantT <$> traverse go row
            T.RecordT row -> C.RecordT <$> traverse go row
      where
        cons = nameLoc $ Located loc ConsName
        nil = nameLoc $ Located loc NilName
        nameLoc = Located loc . C.Name
        appLoc l r = Located loc $ C.App l r
        type_ = pure $ Located loc $ C.TyCon $ Located loc TypeName

    -- we only support non-nested patterns for now
    flattenPattern :: Pattern 'Fixity -> Eff es CorePattern
    flattenPattern (Located loc p) = case p of
        T.VarP name -> pure $ C.VarP name
        T.WildcardP name -> pure $ C.WildcardP name
        T.AnnotationP pat _ -> flattenPattern pat
        T.ConstructorP name pats -> C.ConstructorP name <$> traverse asVar pats
        T.VariantP name pat -> C.VariantP name <$> asVar pat
        T.RecordP row -> C.RecordP <$> traverse asVar row
        T.ListP _ -> internalError loc "todo: list pattern desugaring"
        T.LiteralP (L lit) -> pure $ C.LiteralP lit
    asVar (L (T.VarP name)) = pure name
    asVar (Located loc (T.WildcardP txt)) = freshName $ Located loc $ Name' txt
    asVar v = internalError (getLoc v) "todo: nested patterns"

eval :: (Diagnose :> es, NameGen :> es) => ValueEnv -> Term 'Fixity -> Eff es Value
eval env term = evalCore env <$> desugar term

evalAll :: (Diagnose :> es, NameGen :> es) => [Declaration 'Fixity] -> Eff es ValueEnv
evalAll = modifyEnv ValueEnv{values = LMap.empty, skolems = LMap.empty}

modifyEnv
    :: forall es
     . (Diagnose :> es, NameGen :> es)
    => ValueEnv
    -> [Declaration 'Fixity]
    -> Eff es ValueEnv
modifyEnv env decls = do
    desugared <- (traverse . traverse) desugar . LMap.fromList =<< foldMapM collectBindings decls
    let newEnv = env{values = fmap (either id (evalCore newEnv)) desugared <> env.values}
    pure newEnv
  where
    collectBindings :: Declaration 'Fixity -> Eff es [(Name, Either Value (Term 'Fixity))]
    collectBindings (Located loc decl) = case decl of
        D.Value _ (_ : _) -> internalError loc "local bindings are not supported yet"
        D.Value (T.ValueB (L (T.VarP name)) body) [] -> pure [(name, Right body)]
        D.Value (T.ValueB _ _) _ -> internalError loc "whoops, destructuring bindings are not supported yet"
        D.Value (T.FunctionB name args body) [] -> pure [(name, Right $ foldr (\x -> Located Blank . T.Lambda x) body args)]
        -- todo: value constructors have to be in scope by the time we typecheck definitions that depend on them (say, GADTs)
        -- the easiest way is to just apply `typecheck` and `modifyEnv` declaration-by-declaration
        D.Type _ _ constrs -> traverse mkConstr constrs
        D.GADT _ _ constrs -> traverse mkGadtConstr constrs
        D.Signature{} -> pure mempty

    mkConstr con = (con.name,) . Left <$> mkConLambda (length con.args) con.name env
    mkGadtConstr con = (con.name,) . Left <$> mkConLambda (argCount con.sig) con.name env
    argCount = go 0
      where
        go acc (L e) = case e of
            T.Function _ rhs -> go (succ acc) rhs
            T.Q T.Forall Visible _ _ body -> go (succ acc) body
            T.Q _ _ _ _ body -> go acc body
            _ -> acc

mkConLambda :: NameGen :> es => Int -> Name -> ValueEnv -> Eff es Value
mkConLambda n con env = do
    names <- replicateM n (freshName (Located Blank $ Name' "conArg"))
    -- fused foldl/foldr go brrr
    pure $
        foldr
            ( \var bodyFromEnv env' ->
                let newEnv = env'{values = LMap.insert var (Var var) env'.values}
                 in Lambda $ Closure{var, ty = (), env = newEnv, body = quote $ Located (getLoc var) $ bodyFromEnv newEnv}
            )
            (const $ Con con (map Var names))
            names
            env

mkLambda' :: [Name] -> ([Value] -> Value) -> Value
mkLambda' [] f = f []
mkLambda' (name : names) f =
    PrimFunction name \x -> mkLambda' names \args -> f (x : args)
