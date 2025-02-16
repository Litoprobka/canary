{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedRecordDot #-}

module Interpreter (InterpreterBuiltins (..), eval, evalCore, evalAll, modifyEnv, Value (..), quote) where

import Common (Literal_ (..), Loc (..), Located (..), Name, Pass (..), SimpleName, SimpleName_ (Name'), getLoc, toSimpleName)
import Data.HashMap.Lazy qualified as HashMap -- note that we use the lazy functions here
import Diagnostic
import LangPrelude
import NameGen (NameGen, freshName, runNameGen)
import Prettyprinter (line, vsep)
import Syntax
import Syntax.Core qualified as C
import Syntax.Declaration qualified as D
import Syntax.Row (ExtRow (..), OpenName)
import Syntax.Term qualified as T

type Type' = Value

data Value
    = Var Name -- an unbound variable
    | Constructor Name [Value] -- a fully-applied counstructor
    | Lambda SimpleName (Value -> Value)
    | Record (Row Value)
    | Variant OpenName Value
    | -- | RecordLens (NonEmpty OpenName)
      Text Text
    | Char Text
    | Int Int
    | -- types
      Function Type' Type'
    | Forall SimpleName (Type' -> Type')
    | Exists SimpleName (Type' -> Type')
    | VariantT (ExtRow Type')
    | RecordT (ExtRow Type')
    | -- stuck computations
      App Value ~Value
    | Case Value [(CorePattern, Value)]

quote :: NameGen :> es => Value -> Eff es CoreTerm
quote = \case
    Var x -> pure $ C.Name x
    Constructor con args -> foldl' C.App (C.Name con) <$> traverse quote args
    Lambda name f -> do
        name' <- freshName name
        C.Lambda name' <$> quote (f (Var name')) -- ewww, we should probably use a skolem instead
    Record vals -> C.Record <$> traverse quote vals
    Variant name val -> C.App (C.Variant name) <$> quote val
    -- RecordLens path -> RecordLens path
    Text txt -> pure $ C.Literal $ TextLiteral txt
    Char txt -> pure $ C.Literal $ CharLiteral txt
    Int n -> pure $ C.Literal $ IntLiteral n
    Function l r -> C.Function <$> quote l <*> quote r
    Forall var f -> do
        var' <- freshName var
        C.Forall var' <$> quote (f (Var var'))
    Exists var f -> do
        var' <- freshName var
        C.Exists var' <$> quote (f (Var var'))
    VariantT row -> C.VariantT <$> traverse quote row
    RecordT row -> C.RecordT <$> traverse quote row
    App lhs rhs -> C.App <$> quote lhs <*> quote rhs
    Case arg cases -> C.Case <$> quote arg <*> (traverse . traverse) quote cases

instance Pretty Value where
    -- we don't *really* need NameGen for quotes, so it's fine
    pretty = pretty . runPureEff . runNameGen . quote

evalCore :: HashMap Name Value -> CoreTerm -> Value
evalCore !env = \case
    -- note that env is a lazy hashmap, so we only force the outer structure here
    C.Name name -> fromMaybe (Var name) $ HashMap.lookup name env
    C.Lambda name body -> Lambda (toSimpleName name) (\x -> evalCore (HashMap.insert name x env) body)
    C.App lhs rhs -> case (evalCore env lhs, evalCore env rhs) of
        (Lambda _ f, arg) -> f arg
        (other, arg) -> App other arg
    C.Case arg matches ->
        let val = evalCore env arg
         in fromMaybe
                (error $ show $ "pattern mismatch when matching " <+> pretty val <+> "with:" <> line <> vsep (map (pretty . fst) matches))
                . (<|> mbStuckCase val matches)
                . asum
                $ matches <&> \(pat, body) -> evalCore <$> matchCore env pat val <*> pure body
    C.Let name expr body -> evalCore (HashMap.insert name (evalCore env expr) env) body
    C.Literal lit -> case lit of
        TextLiteral txt -> Text txt
        CharLiteral txt -> Char txt
        IntLiteral n -> Int n
    C.Record row -> Record $ evalCore env <$> row
    C.Variant name -> Lambda (Located Blank $ Name' "x") $ Variant name
    C.Function lhs rhs -> Function (evalCore env lhs) (evalCore env rhs)
    C.Forall name body -> Forall (toSimpleName name) \a -> evalCore (HashMap.insert name a env) body
    C.Exists name body -> Exists (toSimpleName name) \a -> evalCore (HashMap.insert name a env) body
    C.VariantT row -> VariantT $ evalCore env <$> row
    C.RecordT row -> RecordT $ evalCore env <$> row
  where
    mbStuckCase (Var x) matches = Just $ Case (Var x) (map (second $ evalCore env) matches)
    mbStuckCase (App lhs rhs) matches = Just $ Case (App lhs rhs) (map (second $ evalCore env) matches)
    mbStuckCase _ _ = Nothing

matchCore :: HashMap Name Value -> CorePattern -> Value -> Maybe (HashMap Name Value)
matchCore env = \cases
    (C.VarP name) val -> Just $ HashMap.insert name val env
    C.WildcardP{} _ -> Just env
    (C.ConstructorP pname argNames) (Constructor name args)
        | pname == name && length argNames == length args ->
            Just $ foldr (uncurry HashMap.insert) env (zip argNames args)
    (C.VariantP pname argName) (Variant name val)
        | pname == name -> Just $ HashMap.insert argName val env
    (C.LiteralP lit) value -> case (lit, value) of
        (IntLiteral n, Int m) -> env <$ guard (n == m)
        (TextLiteral txt, Text txt') -> env <$ guard (txt == txt')
        (CharLiteral c, Char c') -> env <$ guard (c == c')
        _ -> Nothing
    _ _ -> Nothing

data InterpreterBuiltins a = InterpreterBuiltins
    { true :: a
    , cons :: a
    , nil :: a
    }
    deriving (Functor, Foldable, Traversable)

-- desugar *almost* could be pure, but unfortunately, we need name gen here
-- perhaps we should use something akin to locally nameless?
-- TODO: properly handle recursive bindings (that is, don't infinitely loop on them)
desugar :: forall es. (NameGen :> es, Diagnose :> es) => InterpreterBuiltins Name -> Term 'Fixity -> Eff es CoreTerm
desugar builtins = go
  where
    go :: Term 'Fixity -> Eff es CoreTerm
    go = \case
        T.Name name -> pure $ C.Name name
        T.Literal (Located _ lit) -> pure $ C.Literal lit
        T.Annotation expr _ -> go expr
        T.Application lhs rhs -> C.App <$> go lhs <*> go rhs
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
        T.TypeApplication expr _ -> go expr
        T.Case _ arg matches -> C.Case <$> go arg <*> traverse (bitraverse flattenPattern go) matches
        T.Match loc _ -> internalError loc "todo: match desugar"
        T.If _ cond true false -> do
            cond' <- go cond
            true' <- go true
            false' <- go false
            pure . C.Case cond' $
                [ (C.ConstructorP builtins.true [], true')
                , (C.WildcardP "", false')
                ]
        T.RecordLens loc _ -> internalError loc "todo: desugar RecordLens"
        T.Variant name -> pure $ C.Variant name
        T.Record _ fields -> C.Record <$> traverse go fields
        T.List _ xs -> foldr (C.App . C.App (C.Name builtins.cons)) (C.Name builtins.nil) <$> traverse go xs
        T.Do{} -> error "todo: desugar do blocks"
        T.Function _ from to -> C.Function <$> go from <*> go to
        T.Forall _ binder body -> C.Forall binder.var <$> go body
        T.Exists _ binder body -> C.Exists binder.var <$> go body
        T.VariantT _ row -> C.VariantT <$> traverse go row
        T.RecordT _ row -> C.RecordT <$> traverse go row

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

eval :: (Diagnose :> es, NameGen :> es) => InterpreterBuiltins Name -> HashMap Name Value -> Term 'Fixity -> Eff es Value
eval builtins env term = evalCore env <$> desugar builtins term

{- a pure version
desugar :: InterpreterBuiltins Name -> Term 'Fixity -> CoreTerm
desugar builtins = go
  where
    go :: Term 'Fixity -> CoreTerm
    go = \case
        T.Name name -> NameC name
        T.Literal (Located _ lit) -> LiteralC lit
        T.Annotation expr _ -> go expr
        T.Application lhs rhs -> AppC (go lhs) (go rhs)
        T.Lambda loc pat body ->
            let name = _fresh
            in LambdaC name $ go $ T.Case loc (T.Name name) [(pat, body)]
        T.WildcardLambda loc args body -> foldr LambdaC (go body) args
        T.Let loc binding expr -> case binding of
            T.ValueB (T.VarP name) body -> LetC name (go body) (go expr)
            T.ValueB _ _ -> error "todo: desugar pattern bindings"
            T.FunctionB name args body -> LetC name (go $ foldr (T.Lambda loc) body args) (go expr)
        T.LetRec _ _bindings _body -> error "todo: letrec desugar"
        T.TypeApplication expr _ -> go expr
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

evalAll :: (Diagnose :> es, NameGen :> es) => InterpreterBuiltins Name -> [Declaration 'Fixity] -> Eff es (HashMap Name Value)
evalAll builtins = modifyEnv builtins HashMap.empty

modifyEnv
    :: (Diagnose :> es, NameGen :> es)
    => InterpreterBuiltins Name
    -> HashMap Name Value
    -> [Declaration 'Fixity]
    -> Eff es (HashMap Name Value)
modifyEnv builtins env decls = do
    desugared <- (traverse . traverse) (desugar builtins) . HashMap.fromList $ foldMap collectBindings decls
    let newEnv = fmap (either id (evalCore newEnv)) desugared <> env
    pure newEnv
  where
    collectBindings :: Declaration 'Fixity -> [(Name, Either Value (Term 'Fixity))]
    collectBindings = \case
        D.Value _ _ (_ : _) -> error "local bindings are not supported yet"
        D.Value _ (T.ValueB (T.VarP name) body) [] -> [(name, Right body)]
        D.Value _ (T.ValueB _ _) _ -> error "whoops, destructuring bindings are not supported yet"
        D.Value _ (T.FunctionB name args body) [] -> [(name, Right $ foldr (T.Lambda Blank) body args)]
        D.Type _ _ _ constrs -> map mkConstr constrs
        D.GADT _ _ _ constrs -> map mkGadtConstr constrs
        D.Signature{} -> mempty

    mkConstr con = (con.name, Left $ mkLambda (length con.args) (Constructor con.name))
    mkGadtConstr con = (con.name, Left $ mkLambda (countArgs con.sig) (Constructor con.name))
    countArgs = go 0
      where
        go acc = \case
            T.Function _ _ rhs -> go (succ acc) rhs
            T.Forall _ _ body -> go acc body
            T.Exists _ _ body -> go acc body
            _ -> acc

mkLambda :: Int -> ([Value] -> Value) -> Value
mkLambda 0 f = f []
mkLambda n f = Lambda (Located Blank $ Name' $ "x" <> show n) \x -> mkLambda (pred n) \args -> f (x : args)
