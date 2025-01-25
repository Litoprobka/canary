{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedRecordDot #-}

module Interpreter (InterpreterBuiltins (..), eval, evalAll, modifyEnv, Value, Env (..)) where

import Common (Literal_ (..), Loc (..), Located (..), Name, Pass (..), getLoc)
import Data.HashMap.Lazy qualified as HashMap -- note that we use the lazy functions here
import GHC.IsList qualified as IsList
import LangPrelude
import Prettyprinter (braces, comma, line, parens, punctuate, sep, vsep)
import Syntax
import Syntax.Declaration qualified as D
import Syntax.Expression qualified as E
import Syntax.Pattern qualified as P
import Syntax.Row (OpenName)
import Syntax.Row qualified as Row
import Syntax.Type qualified as T

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

data Env = Env
    { constructors :: HashMap Name Value
    , bindings :: HashMap Name Value
    }

evalAll :: InterpreterBuiltins Name -> [Declaration 'Fixity] -> HashMap Name Value
evalAll builtins = (.bindings) . modifyEnv builtins (Env HashMap.empty HashMap.empty)

modifyEnv :: InterpreterBuiltins Name -> Env -> [Declaration 'Fixity] -> Env
modifyEnv builtins env decls = newEnv
  where
    (newConstrs, newBindings) = bimap HashMap.fromList HashMap.fromList $ foldMap collectBindings decls
    newEnv = Env{constructors = newConstrs <> env.constructors, bindings = newBindings <> env.bindings}
    eval' = eval builtins newEnv

    collectBindings :: Declaration 'Fixity -> ([(Name, Value)], [(Name, Value)])
    collectBindings = \case
        D.Value _ _ (_ : _) -> error "local bindings are not supported yet"
        D.Value _ (E.ValueBinding (P.Var name) body) locals -> ([], [(name, eval' body)])
        D.Value _ (E.ValueBinding _ body) locals -> error "whoops, destructuring bindings are not supported yet"
        D.Value _ (E.FunctionBinding name args body) locals -> ([], [(name, eval' $ foldr (E.Lambda Blank) body args)])
        D.Type _ _ _ constrs -> (map mkConstr constrs, [])
        D.GADT _ _ _ constrs -> (map mkGadtConstr constrs, [])
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

eval :: InterpreterBuiltins Name -> Env -> Expression 'Fixity -> Value
eval builtins Env{constructors, bindings} = go bindings
  where
    go env = \case
        E.Lambda _ pat body -> Lambda \arg -> go (forceMatch builtins env pat arg) body
        E.WildcardLambda loc args body -> go env $ foldr (E.Lambda loc . P.Var) body args
        E.Application f arg -> case go env f of
            Lambda closure -> closure (go env arg)
            other -> error . show $ "cannot apply" <+> pretty other
        E.TypeApplication f _ -> go env f
        E.Annotation x _ -> go env x
        E.Let _ binding body -> case binding of
            E.ValueBinding pat bindingBody -> go (forceMatch builtins env pat $ go env bindingBody) body
            E.FunctionBinding name args bindingBody ->
                go (HashMap.insert name (go env $ foldr (E.Lambda $ getLoc binding) bindingBody args) env) body
        E.LetRec _ _bindings _body -> error "letrecs are not supported yet. tough luck"
        E.Case _ arg matches ->
            let val = go env arg
             in fromMaybe
                    (error $ show $ "pattern mismatch when matching " <+> pretty val <+> "with:" <> line <> vsep (map (pretty . fst) matches))
                    . asum
                    $ matches <&> \(pat, body) -> go <$> match builtins env pat val <*> pure body
        E.Match _ matches@(m : _) -> mkLambda (length $ fst m) \args ->
            fromMaybe (error "pattern mismatch") $ asum $ uncurry (matchAllArgs env args) <$> matches
        E.Match _ [] -> error "empty match" -- shouldn't this be caught by type checking?
        E.If _ cond true false -> case go env cond of
            Constructor name [] | name == builtins.true -> go env true
            _ -> go env false
        E.Name name -> fromMaybe (error $ show $ pretty name <+> "not in scope") $ HashMap.lookup name env
        E.Constructor name -> fromMaybe (error $ "unknown constructor " <> show name) $ HashMap.lookup name constructors
        E.RecordLens _ path -> RecordLens path
        E.Variant name -> Lambda $ Variant name
        E.Record _ row -> Record $ fmap (go env) row
        E.List _ xs -> foldr (\h t -> Constructor builtins.cons [go env h, t]) (Constructor builtins.nil []) xs
        E.Literal (Located _ lit) -> case lit of
            IntLiteral n -> Int n
            TextLiteral txt -> Text txt
            CharLiteral c -> Char c
        E.Do{} -> error "do notation is not supported yet"

    matchAllArgs :: HashMap Name Value -> [Value] -> [Pattern 'Fixity] -> Expression 'Fixity -> Maybe Value
    matchAllArgs env args pats body = do
        env' <- fold <$> zipWithM (match builtins env) pats args
        pure $ go env' body

forceMatch :: InterpreterBuiltins Name -> HashMap Name Value -> Pattern 'Fixity -> Value -> HashMap Name Value
forceMatch builtins env pat arg = fromMaybe (error "pattern mismatch") $ match builtins env pat arg

match :: InterpreterBuiltins Name -> HashMap Name Value -> Pattern 'Fixity -> Value -> Maybe (HashMap Name Value)
match builtins env = \cases
    (P.Var var) val -> Just $ HashMap.insert var val env
    P.Wildcard{} _ -> Just env
    (P.Annotation pat _) val -> match builtins env pat val
    (P.Variant name argPat) (Variant name' arg)
        | name == name' -> match builtins env argPat arg
        | otherwise -> Nothing
    (P.Record _ patRow) (Record valRow) -> do
        valPatPairs <- traverse (\(name, pat) -> (pat,) <$> Row.lookup name valRow) $ IsList.toList patRow
        fold <$> traverse (uncurry $ match builtins env) valPatPairs
    (P.Constructor name pats) (Constructor name' args) -> do
        guard (name == name')
        unless (length pats == length args) $ error "arg count mismatch"
        fold <$> zipWithM (match builtins env) pats args
    (P.List loc (pat : pats)) (Constructor name [h, t]) | name == builtins.cons -> do
        env' <- match builtins env pat h
        match builtins env' (P.List loc pats) t
    (P.List _ []) (Constructor name []) | name == builtins.nil -> Just env
    (P.Literal (Located _ lit)) value -> case (lit, value) of
        (IntLiteral n, Int m) -> env <$ guard (n == m)
        (TextLiteral txt, Text txt') -> env <$ guard (txt == txt')
        (CharLiteral c, Char c') -> env <$ guard (c == c')
        _ -> Nothing
    _ _ -> Nothing

mkLambda :: Int -> ([Value] -> Value) -> Value
mkLambda 0 f = f []
mkLambda n f = Lambda \x -> mkLambda (pred n) \args -> f (x : args)
