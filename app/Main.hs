module Main (main) where

import Relude

import Common
import Data.HashMap.Strict qualified as HashMap
import DependencyResolution (SimpleOutput (..), resolveDependenciesSimplified)
import Diagnostic
import Effectful
import Fixity
import Interpreter (InterpreterBuiltins (..), eval, evalAll)
import NameGen (runNameGen)
import NameResolution
import Parser (parseModule)
import Playground (mkDefaults)
import Prettyprinter
import Prettyprinter.Render.Text (putDoc)
import Syntax.Declaration qualified as D
import Syntax.Expression qualified as E
import TypeChecker (typecheck)

main :: IO ()
main = do
    args <- liftIO getArgs
    let (debug, otherArgs) = case args of
            ("debug" : rest) -> (True, rest)
            other -> (False, other)
    (fileName, input) <- case otherArgs of
        [] -> ("cli",) <$> getLine
        (path : _) -> (path,) . decodeUtf8 <$> readFileBS path
    eval' <- runEff . runDiagnose (fileName, input) $ runNameGen do
        decls <- parseModule (fileName, input)
        prettyAST debug decls
        (scope, builtins, env) <- mkDefaults
        (bindings, evalBuiltins, nameOfMain) <- runNameResolution scope do
            bindings <- resolveNames decls
            evalBuiltins <- traverse resolve InterpreterBuiltins{true = "True", cons = "Cons", nil = "Nil"}
            nameOfMain <- resolve $ Located Blank $ Name' "main"
            pure (bindings, evalBuiltins, nameOfMain)

        SimpleOutput{fixityMap, operatorPriorities, declarations} <- resolveDependenciesSimplified bindings
        fixityResolvedBindings <- resolveFixity fixityMap operatorPriorities declarations

        printDebug debug "resolved names:"
        prettyAST debug fixityResolvedBindings

        printDebug debug "typechecking:"
        types <- typecheck env builtins fixityResolvedBindings
        when debug do
            liftIO . putDoc $ (<> line) $ vsep $ pretty . uncurry (D.Signature Blank) <$> HashMap.toList types
        pure case HashMap.lookup nameOfMain (evalAll evalBuiltins fixityResolvedBindings) of
            Nothing -> putTextLn "there is no main function"
            Just mainExpr -> putDoc $ (<> line) $ pretty mainExpr
    sequence_ eval'

printDebug :: MonadIO m => Bool -> Text -> m ()
printDebug debug = when debug . putTextLn

prettyAST :: (Traversable t, Pretty a, MonadIO m) => Bool -> t a -> m ()
prettyAST debug = when debug . liftIO . traverse_ (putDoc . (<> line) . pretty)
