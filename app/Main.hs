module Main (main) where

import LangPrelude

import Common
import Data.EnumMap.Strict qualified as Map
import Data.Traversable (for)
import Diagnostic
import Eval (ValueEnv (..))
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
        (path : _) -> runFile debug path =<< readFileBS path

runFile :: Bool -> FilePath -> ByteString -> IO ()
runFile debug fileName input = do
    let inputText = decodeUtf8 input
    eval' <- fmap join . runEff . runDiagnose (fileName, inputText) $ runNameGen do
        decls <- parseModule (fileName, input)
        prettyAST debug decls
        env <- Repl.mkDefaultEnv
        mbNewEnv <- Repl.replStep env $ Repl.Decls decls
        for mbNewEnv \newEnv -> do
            nameOfMain <- NameResolution.run newEnv.scope $ resolve $ Located Blank $ Name' "main"
            pure case Map.lookup nameOfMain newEnv.values.values of
                Nothing -> putTextLn "there is no main function"
                Just mainExpr -> putDoc $ (<> line) $ pretty mainExpr
    sequence_ eval'

runRepl :: IO ()
runRepl = void $ runEff $ runDiagnose ("", "") $ runNameGen do
    liftIO $ hSetBuffering stdout NoBuffering
    replEnv <- Repl.mkDefaultEnv
    Repl.run replEnv

prettyAST :: (Traversable t, Pretty a, MonadIO m) => Bool -> t a -> m ()
prettyAST debug = when debug . liftIO . traverse_ (putDoc . (<> line) . pretty)
