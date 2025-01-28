module Main (main) where

import LangPrelude

import Common
import Data.HashMap.Strict qualified as HashMap
import Data.Traversable (for)
import Diagnostic
import Effectful.Reader.Static
import NameGen (runNameGen)
import NameResolution
import Parser (parseModule)
import Prettyprinter
import Prettyprinter.Render.Text (putDoc)
import Repl (ReplEnv (..))
import Repl qualified

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
    eval' <- fmap join . runEff . runDiagnose (fileName, input) $ runNameGen do
        decls <- parseModule (fileName, input)
        prettyAST debug decls
        (evalBuiltins, builtins, env) <- Repl.mkDefaultEnv
        mbNewEnv <- runReader evalBuiltins $ runReader builtins $ Repl.replStep env $ Repl.Decls decls
        for mbNewEnv \newEnv -> do
            nameOfMain <- NameResolution.run newEnv.scope $ resolve $ Located Blank $ Name' "main"
            pure case HashMap.lookup nameOfMain newEnv.values of
                Nothing -> putTextLn "there is no main function"
                Just mainExpr -> putDoc $ (<> line) $ pretty mainExpr
    sequence_ eval'

runRepl :: IO ()
runRepl = void $ runEff $ runDiagnose ("", "") $ runNameGen do
    liftIO $ hSetBuffering stdout NoBuffering
    (evalBuiltins, builtins, replEnv) <- Repl.mkDefaultEnv
    runReader evalBuiltins $ runReader builtins $ Repl.run replEnv

prettyAST :: (Traversable t, Pretty a, MonadIO m) => Bool -> t a -> m ()
prettyAST debug = when debug . liftIO . traverse_ (putDoc . (<> line) . pretty)
