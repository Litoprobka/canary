{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedRecordDot #-}

module Interpreter (InterpreterBuiltins (..), eval, evalAll, modifyEnv, Value (..)) where

import Common (Literal_ (..), Loc (..), Located (..), Name, Pass (..), getLoc)
import Data.HashMap.Lazy qualified as HashMap -- note that we use the lazy functions here
import GHC.IsList qualified as IsList
import LangPrelude
import Prettyprinter (braces, comma, line, parens, punctuate, sep, vsep)
import Syntax
import Syntax.Declaration qualified as D
import Syntax.Row (OpenName)
import Syntax.Row qualified as Row
import Syntax.Term (Pattern (..))
import Syntax.Term qualified as T

data Value
    = Constructor Name [Value] -- a fully-applied counstructor
    | Lambda (Value -> Value)
    | Record (Row Value)
    | Variant OpenName Value
    | RecordLens (NonEmpty OpenName)
    | Text Text
    | Char Text
    | Int Int

instance Pretty Value where
    pretty = \case
        Constructor name [] -> pretty name
        Constructor name args -> parens $ pretty name <+> sep (pretty <$> args)
        Lambda _ -> "<lambda>"
        Record row -> braces . sep . punctuate comma . map recordField $ Row.sortedRow row
        Variant name val -> parens $ pretty name <+> pretty val
        RecordLens lens -> foldMap (("." <>) . pretty) lens
        Text txt -> pretty txt
        Char c -> pretty c
        Int n -> pretty n
      where
        recordField (name, body) = pretty name <+> "=" <+> pretty body

data InterpreterBuiltins a = InterpreterBuiltins
    { true :: a
    , cons :: a
    , nil :: a
    }
    deriving (Functor, Foldable, Traversable)

evalAll :: InterpreterBuiltins Name -> [Declaration 'Fixity] -> HashMap Name Value
evalAll builtins = modifyEnv builtins HashMap.empty

modifyEnv :: InterpreterBuiltins Name -> HashMap Name Value -> [Declaration 'Fixity] -> HashMap Name Value
modifyEnv builtins env decls = newEnv
  where
    newEnv = (<> env) . HashMap.fromList $ foldMap collectBindings decls
    -- nameOfZ = Located Blank $ Name "Z" (Id 23)
    eval' = eval builtins newEnv

    collectBindings :: Declaration 'Fixity -> [(Name, Value)]
    collectBindings = \case
        D.Value _ _ (_ : _) -> error "local bindings are not supported yet"
        D.Value _ (T.ValueB (VarP name) body) [] -> [(name, eval' body)]
        D.Value _ (T.ValueB _ _) _ -> error "whoops, destructuring bindings are not supported yet"
        D.Value _ (T.FunctionB name args body) [] -> [(name, eval' $ foldr (T.Lambda Blank) body args)]
        D.Type _ _ _ constrs -> map mkConstr constrs
        D.GADT _ _ _ constrs -> map mkGadtConstr constrs
        D.Signature{} -> mempty

    mkConstr con = (con.name, mkLambda (length con.args) (Constructor con.name))
    mkGadtConstr con = (con.name, mkLambda (countArgs con.sig) (Constructor con.name))
    countArgs = go 0
      where
        go acc = \case
            T.Function _ _ rhs -> go (succ acc) rhs
            T.Forall _ _ body -> go acc body
            T.Exists _ _ body -> go acc body
            _ -> acc

eval :: InterpreterBuiltins Name -> HashMap Name Value -> Expr 'Fixity -> Value
eval builtins = go
  where
    -- note that env is a lazy hashmap, so we only force the outer structure here
    go !env = \case
        T.Lambda _ pat body -> Lambda \arg -> go (forceMatch builtins env pat arg) body
        T.WildcardLambda loc args body -> go env $ foldr (T.Lambda loc . VarP) body args
        T.Application f arg -> case go env f of
            Lambda closure -> closure (go env arg)
            other -> error . show $ "cannot apply" <+> pretty other
        T.TypeApplication f _ -> go env f
        T.Annotation x _ -> go env x
        T.Let _ binding body -> case binding of
            T.ValueB pat bindingBody -> go (forceMatch builtins env pat $ go env bindingBody) body
            T.FunctionB name args bindingBody ->
                go (HashMap.insert name (go env $ foldr (T.Lambda $ getLoc binding) bindingBody args) env) body
        T.LetRec _ _bindings _body -> error "letrecs are not supported yet. tough luck"
        T.Case _ arg matches ->
            let val = go env arg
             in fromMaybe
                    (error $ show $ "pattern mismatch when matching " <+> pretty val <+> "with:" <> line <> vsep (map (pretty . fst) matches))
                    . asum
                    $ matches <&> \(pat, body) -> go <$> match builtins env pat val <*> pure body
        T.Match _ matches@(m : _) -> mkLambda (length $ fst m) \args ->
            fromMaybe (error "pattern mismatch") $ asum $ uncurry (matchAllArgs env args) <$> matches
        T.Match _ [] -> error "empty match" -- shouldn't this be caught by type checking?
        T.If _ cond true false -> case go env cond of
            Constructor name [] | name == builtins.true -> go env true
            _ -> go env false
        T.Name name -> fromMaybe (error $ show $ pretty name <+> "not in scope") $ HashMap.lookup name env
        T.RecordLens _ path -> RecordLens path
        T.Variant name -> Lambda $ Variant name
        T.Record _ row -> Record $ fmap (go env) row
        T.List _ xs -> foldr (\h t -> Constructor builtins.cons [go env h, t]) (Constructor builtins.nil []) xs
        T.Literal (Located _ lit) -> case lit of
            IntLiteral n -> Int n
            TextLiteral txt -> Text txt
            CharLiteral c -> Char c
        T.Do{} -> error "do notation is not supported yet"
        -- T.Var{} -> error "type var in an expression"
        T.Function{} -> error "function type in an expression"
        T.Forall{} -> error "forall type in an expression"
        T.Exists{} -> error "exists type in an expression"
        T.VariantT{} -> error "variant type in an expression"
        T.RecordT{} -> error "record type in an expression"

    matchAllArgs :: HashMap Name Value -> [Value] -> [Pattern 'Fixity] -> Expr 'Fixity -> Maybe Value
    matchAllArgs env args pats body = do
        env' <- foldr (<>) env <$> zipWithM (match builtins env) pats args
        pure $ go env' body

forceMatch :: InterpreterBuiltins Name -> HashMap Name Value -> Pattern 'Fixity -> Value -> HashMap Name Value
forceMatch builtins env pat arg = fromMaybe (error "pattern mismatch") $ match builtins env pat arg

match :: InterpreterBuiltins Name -> HashMap Name Value -> Pattern 'Fixity -> Value -> Maybe (HashMap Name Value)
match builtins env = \cases
    (VarP var) val -> Just $ HashMap.insert var val env
    WildcardP{} _ -> Just env
    (AnnotationP pat _) val -> match builtins env pat val
    (VariantP name argPat) (Variant name' arg)
        | name == name' -> match builtins env argPat arg
        | otherwise -> Nothing
    (RecordP _ patRow) (Record valRow) -> do
        valPatPairs <- traverse (\(name, pat) -> (pat,) <$> Row.lookup name valRow) $ IsList.toList patRow
        foldr (<>) env <$> traverse (uncurry $ match builtins env) valPatPairs
    (ConstructorP name pats) (Constructor name' args) -> do
        guard (name == name')
        unless (length pats == length args) $ error "arg count mismatch"
        foldr (<>) env <$> zipWithM (match builtins env) pats args
    (ListP loc (pat : pats)) (Constructor name [h, t]) | name == builtins.cons -> do
        env' <- match builtins env pat h
        match builtins env' (ListP loc pats) t
    (ListP _ []) (Constructor name []) | name == builtins.nil -> Just env
    (LiteralP (Located _ lit)) value -> case (lit, value) of
        (IntLiteral n, Int m) -> env <$ guard (n == m)
        (TextLiteral txt, Text txt') -> env <$ guard (txt == txt')
        (CharLiteral c, Char c') -> env <$ guard (c == c')
        _ -> Nothing
    _ _ -> Nothing

mkLambda :: Int -> ([Value] -> Value) -> Value
mkLambda 0 f = f []
mkLambda n f = Lambda \x -> mkLambda (pred n) \args -> f (x : args)
