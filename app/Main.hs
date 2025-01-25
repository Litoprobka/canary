module Main (main) where

import LangPrelude

import Common
import Data.HashMap.Strict qualified as HashMap
import DependencyResolution (SimpleOutput (..), resolveDependenciesSimplified)
import Diagnostic
import Effectful.Reader.Static
import Fixity
import Interpreter (InterpreterBuiltins (..), evalAll)
import NameGen (runNameGen)
import NameResolution
import Parser (parseModule)
import Playground (mkDefaults, noLoc)
import Prettyprinter
import Prettyprinter.Render.Text (putDoc)
import Repl qualified
import Syntax.Declaration qualified as D
import TypeChecker (Builtins (..), typecheck)

main :: IO ()
main = do
    args <- liftIO getArgs
    let (debug, otherArgs) = case args of
            ("debug" : rest) -> (True, rest)
            other -> (False, other)
    case otherArgs of
        [] -> runRepl
        (path : _) -> runFile debug path . decodeUtf8 =<< readFileBS path

runFile :: Bool -> FilePath -> Text -> IO ()
runFile debug fileName input = do
    eval' <- runEff . runDiagnose (fileName, input) $ runNameGen do
        decls <- parseModule (fileName, input)
        prettyAST debug decls
        (scope, builtins, env) <- mkDefaults
        (bindings, evalBuiltins, nameOfMain) <- NameResolution.run scope do
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

runRepl :: IO ()
runRepl = void $ runEff $ runDiagnose ("", "") $ runNameGen do
    liftIO $ hSetBuffering stdout NoBuffering
    let replEnv = Repl.mkDefaultEnv
    let builtins = Builtins{subtypeRelations = [(noLoc NatName, noLoc IntName)]}
    evalBuiltins <-
        NameResolution.run replEnv.scope $
            traverse resolve InterpreterBuiltins{true = "True", cons = "Cons", nil = "Nil"}
    runReader evalBuiltins $ runReader builtins $ Repl.run replEnv

printDebug :: MonadIO m => Bool -> Text -> m ()
printDebug debug = when debug . putTextLn

prettyAST :: (Traversable t, Pretty a, MonadIO m) => Bool -> t a -> m ()
prettyAST debug = when debug . liftIO . traverse_ (putDoc . (<> line) . pretty)
