{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedRecordDot #-}

module Interpreter where

import Common (
    HasLoc,
    Literal,
    Loc (..),
    Located (..),
    Name,
    Name_ (ConsName, NilName, TrueName),
    Pass (..),
    SimpleName_ (Name'),
    Skolem,
    UniVar,
    getLoc,
    toSimpleName,
 )
import Data.HashMap.Lazy qualified as HashMap -- note that we use the lazy functions here
import Data.Traversable (for)
import Diagnostic
import LangPrelude
import NameGen (NameGen, freshName)
import Prettyprinter (line, vsep)
import Syntax
import Syntax.Core qualified as C
import Syntax.Declaration qualified as D
import Syntax.Row (ExtRow (..), OpenName)
import Syntax.Term qualified as T
import Prelude qualified (Show (..))

type ValueEnv = HashMap Name Value
type Type' = Value

data Value
    = Var Name -- an unbound variable; seems like they are only used for quoting, hmmm
    | TyCon Name -- a type constructor. unlike value constructors, `Either a b` is represented as a stuck application Either `App` a `App` b
    | Con Name [Value] -- a fully-applied counstructor
    | Lambda Closure
    | PrimFunction Name (Value -> Value) -- an escape hatch for interpreter primitives and similar stuff
    | Record (Row Value)
    | Variant OpenName Value
    | -- | RecordLens (NonEmpty OpenName)
      PrimValue Literal -- the name 'Literal' is slightly misleading here
    | -- types
      Function Loc Type' Type'
    | Forall Loc Closure
    | Exists Loc Closure
    | VariantT Loc (ExtRow Type')
    | RecordT Loc (ExtRow Type')
    | -- stuck computations
      App Value ~Value
    | Case Value [(CorePattern, Value)]
    | -- typechecking metavars
      UniVar Loc UniVar
    | Skolem Skolem

data Closure = Closure {var :: Name, env :: ValueEnv, body :: CoreTerm}

quote :: Value -> CoreTerm
quote = \case
    Var x -> C.Name x
    TyCon name -> C.TyCon name
    Con con args -> C.Con con (map quote args)
    -- if we use quote for anything but pretty-printing,
    -- we'd probably need alpha conversion for all the function-like cases
    Lambda closure -> C.Lambda closure.var $ quote (closureBody closure)
    PrimFunction name f -> quote $ f (Var name)
    Record vals -> C.Record $ fmap quote vals
    Variant name val -> C.App (C.Variant name) $ quote val
    -- RecordLens path -> RecordLens path
    PrimValue lit -> C.Literal lit
    Function loc l r -> C.Function loc (quote l) (quote r)
    Forall loc closure -> C.Forall loc closure.var $ quote (closureBody closure)
    Exists loc closure -> C.Exists loc closure.var $ quote (closureBody closure)
    VariantT loc row -> C.VariantT loc $ fmap quote row
    RecordT loc row -> C.RecordT loc $ fmap quote row
    App lhs rhs -> C.App (quote lhs) (quote rhs)
    Case arg cases -> C.Case (quote arg) $ (fmap . fmap) quote cases
    Skolem skolem -> C.Skolem skolem
    UniVar loc uni -> C.UniVar loc uni

instance Pretty Value where
    pretty = pretty . quote

instance Show Value where
    show = Prelude.show . pretty

instance HasLoc Value where
    getLoc = \case
        Con name _ -> getLoc name
        Var name -> getLoc name
        Skolem skolem -> getLoc skolem
        _other -> Blank -- fixme

evalCore :: ValueEnv -> CoreTerm -> Value
evalCore !env = \case
    -- note that env is a lazy hashmap, so we only force the outer structure here
    C.Name name -> fromMaybe (Var name) $ HashMap.lookup name env
    C.TyCon name -> TyCon name
    C.Con name args -> Con name $ map (evalCore env) args
    C.Lambda name body -> Lambda $ Closure{var = name, env, body}
    C.App (C.Variant name) arg -> Variant name $ evalCore env arg -- this is a bit of an ugly case
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
    C.Let name expr body -> evalCore (HashMap.insert name (evalCore env expr) env) body
    C.Literal lit -> PrimValue lit
    C.Record row -> Record $ evalCore env <$> row
    C.Variant _name -> error "todo: seems like evalCore needs namegen" -- Lambda (Located Blank $ Name' "x") $ C.Variant name `C.App`
    C.Function loc lhs rhs -> Function loc (evalCore env lhs) (evalCore env rhs)
    C.Forall loc var body -> Forall loc $ Closure{var, env, body}
    C.Exists loc var body -> Exists loc $ Closure{var, env, body}
    C.VariantT loc row -> VariantT loc $ evalCore env <$> row
    C.RecordT loc row -> RecordT loc $ evalCore env <$> row
    -- should normal evaluation resolve univars?
    C.Skolem skolem -> Skolem skolem
    C.UniVar loc uni -> UniVar loc uni
  where
    -- mbStuckCase arg _ = Nothing -- error $ "stuck case, too bad: " <> show arg
    mbStuckCase (Var x) matches = Just $ Case (Var x) (map (second $ evalCore env) matches)
    mbStuckCase (Skolem s) matches = Just $ Case (Skolem s) (map (second $ evalCore env) matches)
    mbStuckCase (UniVar loc u) matches = Just $ Case (UniVar loc u) (map (second $ evalCore env) matches)
    mbStuckCase (App lhs rhs) matches = Just $ Case (App lhs rhs) (map (second $ evalCore env) matches)
    mbStuckCase _ _ = Nothing

app :: Closure -> Value -> Value
app Closure{var, env, body} arg = evalCore (HashMap.insert var arg env) body

-- do we need a fresh name here?
closureBody :: Closure -> Value
closureBody closure = closure `app` Var closure.var

closureBody' :: NameGen :> es => Closure -> Eff es Value
closureBody' closure = do
    var <- freshName $ toSimpleName closure.var
    pure $ closure `app` Var var

matchCore :: ValueEnv -> CorePattern -> Value -> Maybe ValueEnv
matchCore env = \cases
    (C.VarP name) val -> Just $ HashMap.insert name val env
    C.WildcardP{} _ -> Just env
    (C.ConstructorP pname argNames) (Con name args)
        | pname == name && length argNames == length args ->
            Just $ foldr (uncurry HashMap.insert) env (zip argNames args)
    (C.VariantP pname argName) (Variant name val)
        | pname == name -> Just $ HashMap.insert argName val env
    (C.LiteralP lit) (PrimValue (Located _ val)) -> env <$ guard (lit == val)
    _ _ -> Nothing

-- desugar *almost* could be pure, but unfortunately, we need name gen here
-- perhaps we should use something akin to locally nameless?
-- TODO: properly handle recursive bindings (that is, don't infinitely loop on them)
desugar :: forall es. (NameGen :> es, Diagnose :> es) => Term 'Fixity -> Eff es CoreTerm
desugar = go
  where
    go :: Term 'Fixity -> Eff es CoreTerm
    go = \case
        T.Name name -> pure $ C.Name name
        T.Literal lit -> pure $ C.Literal lit
        T.Annotation expr _ -> go expr
        T.App lhs rhs -> C.App <$> go lhs <*> go rhs
        T.Lambda loc pat body -> do
            name <- freshName $ Located Blank $ Name' "x"
            C.Lambda name <$> go (T.Case loc (T.Name name) [(pat, body)])
        T.WildcardLambda _ args body -> do
            body' <- go body
            pure $ foldr C.Lambda body' args
        T.Let loc binding expr -> case binding of
            T.ValueB (T.VarP name) body -> C.Let name <$> go body <*> go expr
            T.ValueB _ _ -> internalError loc "todo: desugar pattern bindings"
            T.FunctionB name args body -> C.Let name <$> go (foldr (T.Lambda loc) body args) <*> go expr
        T.LetRec loc _bindings _body -> internalError loc "todo: letrec desugar"
        T.TypeApp expr _ -> go expr
        T.Case _ arg matches -> C.Case <$> go arg <*> traverse (bitraverse flattenPattern go) matches
        T.Match loc matches@(([_], _) : _) -> do
            x <- freshName $ Located Blank $ Name' "x"
            matches' <- for matches \case
                ([pat], body) -> bitraverse flattenPattern desugar (pat, body)
                _ -> internalError loc "inconsistent pattern count in a match expression"
            pure $ C.Lambda x $ C.Case (C.Name x) matches'
        T.Match loc _ -> internalError loc "todo: multi-arg match desugar"
        T.If _ cond true false -> do
            cond' <- go cond
            true' <- go true
            false' <- go false
            pure . C.Case cond' $
                [ (C.ConstructorP (Located (getLoc cond) TrueName) [], true')
                , (C.WildcardP "", false')
                ]
        T.RecordLens loc _ -> internalError loc "todo: desugar RecordLens"
        T.Variant name -> pure $ C.Variant name
        T.Record _ fields -> C.Record <$> traverse go fields
        T.List loc xs -> foldr (C.App . C.App (C.Name $ Located loc ConsName)) (C.Name $ Located loc NilName) <$> traverse go xs
        T.Do{} -> error "todo: desugar do blocks"
        T.Function loc from to -> C.Function loc <$> go from <*> go to
        T.Forall loc binder body -> C.Forall loc binder.var <$> go body
        T.Exists loc binder body -> C.Exists loc binder.var <$> go body
        T.VariantT loc row -> C.VariantT loc <$> traverse go row
        T.RecordT loc row -> C.RecordT loc <$> traverse go row

    -- we only support non-nested patterns for now
    flattenPattern :: Pattern 'Fixity -> Eff es CorePattern
    flattenPattern = \case
        T.VarP name -> pure $ C.VarP name
        T.WildcardP _ name -> pure $ C.WildcardP name
        T.AnnotationP pat _ -> flattenPattern pat
        T.ConstructorP name pats -> C.ConstructorP name <$> traverse asVar pats
        T.VariantP name pat -> C.VariantP name <$> asVar pat
        T.RecordP loc _ -> internalError loc "todo: record pattern desugaring"
        T.ListP loc _ -> internalError loc "todo: list pattern desugaring"
        T.LiteralP (Located _ lit) -> pure $ C.LiteralP lit
    asVar (T.VarP name) = pure name
    asVar (T.WildcardP loc txt) = freshName $ Located loc $ Name' txt
    asVar v = internalError (getLoc v) "todo: nested patterns"

eval :: (Diagnose :> es, NameGen :> es) => ValueEnv -> Term 'Fixity -> Eff es Value
eval env term = evalCore env <$> desugar term

{- a pure version
desugar :: InterpreterBuiltins Name -> Term 'Fixity -> CoreTerm
desugar builtins = go
  where
    go :: Term 'Fixity -> CoreTerm
    go = \case
        T.Name name -> NameC name
        T.Literal (Located _ lit) -> LiteralC lit
        T.Annotation expr _ -> go expr
        T.App lhs rhs -> AppC (go lhs) (go rhs)
        T.Lambda loc pat body ->
            let name = _fresh
            in LambdaC name $ go $ T.Case loc (T.Name name) [(pat, body)]
        T.WildcardLambda loc args body -> foldr LambdaC (go body) args
        T.Let loc binding expr -> case binding of
            T.ValueB (T.VarP name) body -> LetC name (go body) (go expr)
            T.ValueB _ _ -> error "todo: desugar pattern bindings"
            T.FunctionB name args body -> LetC name (go $ foldr (T.Lambda loc) body args) (go expr)
        T.LetRec _ _bindings _body -> error "todo: letrec desugar"
        T.TypeApp expr _ -> go expr
        T.Case _ arg matches -> CaseC (go arg) (bimap flattenPattern go <$> matches)
        T.Match _ _ -> error "todo: match desugar"
        T.If _ cond true false ->
            CaseC
                (go cond)
                [ (ConstructorP builtins.true [], go true)
                , (ConstructorP builtins.false [], go false)
                ]
        T.RecordLens{} -> error "todo: desugar RecordLens"
        T.Variant name -> VariantC name
        T.Record _ fields -> RecordC (fmap go fields)
        T.List _ xs -> (foldr ((AppC . AppC (NameC builtins.cons)) . go) (NameC builtins.nil) xs)
        T.Do{} -> error "todo: desugar do blocks"
        T.Function _ from to -> FunctionC (go from) (go to)
        T.Forall _ binder body -> ForallC binder.name (go body)
        T.Exists _ binder body -> ExistsC binder.name (go body)
        T.VariantT _ row -> VariantTC $ fmap go row
        T.RecordT _ row -> RecordTC $ fmap go row

    flattenPattern :: Pattern 'Fixity -> CorePattern
    flattenPattern = \case
        T.VarP name -> VarP name
        T.WildcardP _ name -> WildcardP name
        T.AnnotationP pat _ -> flattenPattern pat
        T.ConstructorP name pats -> ConstructorP name $ asVar <$> pats
        T.VariantP name pat -> VariantP name $ asVar pat
        T.RecordP{} -> error "todo: record pattern desugaring"
        T.ListP{} -> error "todo: list pattern desugaring"
        T.LiteralP (Located _ lit) -> LiteralP lit
    asVar (T.VarP name) = name
    asVar _ = error "todo: nested patterns"
-}

evalAll :: (Diagnose :> es, NameGen :> es) => [Declaration 'Fixity] -> Eff es ValueEnv
evalAll = modifyEnv HashMap.empty

modifyEnv
    :: forall es
     . (Diagnose :> es, NameGen :> es)
    => ValueEnv
    -> [Declaration 'Fixity]
    -> Eff es ValueEnv
modifyEnv env decls = do
    desugared <- (traverse . traverse) desugar . HashMap.fromList =<< foldMapM collectBindings decls
    let newEnv = fmap (either id (evalCore newEnv)) desugared <> env
    pure newEnv
  where
    collectBindings :: Declaration 'Fixity -> Eff es [(Name, Either Value (Term 'Fixity))]
    collectBindings = \case
        D.Value loc _ (_ : _) -> internalError loc "local bindings are not supported yet"
        D.Value _ (T.ValueB (T.VarP name) body) [] -> pure [(name, Right body)]
        D.Value loc (T.ValueB _ _) _ -> internalError loc "whoops, destructuring bindings are not supported yet"
        D.Value _ (T.FunctionB name args body) [] -> pure [(name, Right $ foldr (T.Lambda Blank) body args)]
        D.Type _ _ _ constrs -> traverse mkConstr constrs
        D.GADT _ _ _ constrs -> traverse mkGadtConstr constrs
        D.Signature{} -> pure mempty

    mkConstr con = (con.name,) . Left <$> mkConLambda (length con.args) con.name env
    mkGadtConstr con = (con.name,) . Left <$> mkConLambda (countArgs con.sig) con.name env
    countArgs = go 0
      where
        go acc = \case
            T.Function _ _ rhs -> go (succ acc) rhs
            T.Forall _ _ body -> go acc body
            T.Exists _ _ body -> go acc body
            _ -> acc

mkConLambda :: NameGen :> es => Int -> Name -> ValueEnv -> Eff es Value
mkConLambda num con env = do
    names <- replicateM num (freshName $ Located Blank $ Name' "x")
    pure $ foldr (\var body -> Lambda $ Closure{var, env, body = quote body}) (Con con (map Var names)) names

mkLambda' :: [Name] -> ([Value] -> Value) -> Value
mkLambda' [] f = f []
mkLambda' (name : names) f =
    PrimFunction name \x -> mkLambda' names \args -> f (x : args)
