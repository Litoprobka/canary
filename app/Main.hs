{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE DuplicateRecordFields #-}

module Main (main) where

import LangPrelude

import Common
import Data.IdMap qualified as Map
import Diagnostic
import Error.Diagnose (Position (..))
import NameGen (runNameGen)
import NameResolution
import Options.Applicative
import Parser (parseModule)
import Prettyprinter
import Prettyprinter.Render.Terminal (putDoc)
import Repl (ReplEnv (..))
import Repl qualified
import Syntax.Value (ValueEnv (..))
import System.Console.Isocline (setHistory)
import System.Directory
import Trace

data Args = Args
    { debug :: Bool
    , cmd :: Command
    }

data Command = Run FilePath | Check FilePath | Load FilePath | Repl

argParser :: Parser Args
argParser = do
    debug <- switch (short 'd' <> long "debug")
    cmd <-
        subparser
            ( command "run" (info (Run <$> fileP) (progDesc "evaluate the 'main' binding of a file"))
                <> command "check" (info (Check <$> fileP) (progDesc "typecheck bindings in a file"))
                <> command "load" (info (Load <$> fileP) (progDesc "start the REPL and load definitions from a file"))
                <> command "repl" (info (pure Repl) (progDesc "start the REPL"))
            )
            <|> Load
            <$> fileP
            <|> pure Repl
    pure Args{debug, cmd}
  where
    fileP = argument str (metavar "FILE")

main :: IO ()
main = do
    args <- execParser (info argParser mempty)
    case args.cmd of
        Repl -> runRepl args
        Run path -> runFile args path =<< readFileBS path
        Check path -> checkFile args path =<< readFileBS path
        Load path -> loadFile args path =<< readFileBS path

runFile :: Args -> FilePath -> ByteString -> IO ()
runFile args fileName input = do
    let inputText = decodeUtf8 input
    eval' <- fmap join . runEff . runDiagnose [(fileName, inputText)] $ runNameGen do
        decls <- parseModule (fileName, input)
        prettyAST args.debug decls
        env <- Repl.mkDefaultEnv
        mbNewEnv <- runTraceWhen args.debug $ Repl.replStep env $ Repl.Decls decls
        for mbNewEnv \newEnv -> do
            nameOfMain <-
                NameResolution.run newEnv.scope $ resolve $ Located (Loc Position{file = "<main>", begin = (0, 0), end = (0, 0)}) "main"
            pure case Map.lookup (unLoc nameOfMain) env.values.topLevel of
                Nothing -> putTextLn "there is no main function"
                Just mainExpr -> putDoc $ (<> line) $ pretty mainExpr
    sequence_ eval'

checkFile :: Args -> FilePath -> ByteString -> IO ()
checkFile args fileName input = do
    let inputText = decodeUtf8 input
    void $ runEff . runDiagnose [(fileName, inputText)] $ runNameGen do
        decls <- parseModule (fileName, input)
        prettyAST args.debug decls
        env <- Repl.mkDefaultEnv
        void $ runTraceWhen args.debug $ Repl.replStep env $ Repl.Decls decls

loadFile :: Args -> FilePath -> ByteString -> IO ()
loadFile args fileName input = do
    let inputText = decodeUtf8 input
    setupRepl
    void . runEff . runDiagnose [(fileName, inputText)] $ runNameGen do
        decls <- parseModule (fileName, input)
        prettyAST args.debug decls
        env <- Repl.mkDefaultEnv
        mbEnv <- runTraceWhen args.debug $ Repl.replStep env $ Repl.Decls decls
        traverse_ (Repl.run args.debug) mbEnv

runRepl :: Args -> IO ()
runRepl args = void $ runEff $ runDiagnose [] $ runNameGen do
    liftIO setupRepl
    Repl.run args.debug =<< Repl.mkDefaultEnv

-- | setup isocline settings and line buffering
setupRepl :: IO ()
setupRepl = do
    historyFile <- liftIO $ getXdgDirectory XdgCache "canary/history.txt"
    liftIO $ setHistory historyFile (-1)
    liftIO $ hSetBuffering stdout NoBuffering

runTraceWhen :: IOE :> es => Bool -> Eff (Trace : es) a -> Eff es a
runTraceWhen True = runTraceIO
runTraceWhen False = skipTrace

prettyAST :: (Traversable t, PrettyAnsi a, MonadIO m) => Bool -> t a -> m ()
prettyAST debug = when debug . liftIO . traverse_ (putDoc . (<> line) . prettyDef)
