{-# LANGUAGE LambdaCase #-}

module Main (main) where

import Relude

import NameResolution
import NameGen (runNameGen)
import Effectful
import Text.Megaparsec
import Parser (code)
import Data.Sequence qualified as Seq
import Prettyprinter.Render.Text (putDoc)
import Prettyprinter
import TypeChecker (typecheck, TypeError (..))
import Playground (mkDefaults)
import qualified Syntax.Declaration as D
import qualified Data.HashMap.Strict as HashMap

main :: IO ()
main = do
    args <- getArgs
    (fileName, input) <- case args of
        [] -> ("cli",) <$> getLine
        (path : _) -> (path,) <$> readFileText path
    input & parse (usingReaderT pos1 code) fileName & \case
        Left err -> putStrLn $ errorBundlePretty err
        Right decls -> runEff $ runNameGen do
            traverse_ (liftIO . putDoc . pretty) decls
            (scope, builtins, env) <- mkDefaults
            (bindings, ScopeErrors errors warnings) <- resolveNames scope decls
            unless (Seq.null errors) $ putTextLn $ "errors: " <> foldMap show errors
            unless (Seq.null warnings) $ putTextLn $ "warnings: " <> foldMap show warnings

            putTextLn "resolved names:"
            traverse_ (liftIO . putDoc . pretty) bindings

            putTextLn "typechecking:"
            typecheck env builtins bindings >>= \case
                Left (TypeError err) -> liftIO . putDoc $ err <> line
                Right checkedBindings -> liftIO . putDoc $ sep $ pretty . uncurry D.Signature <$> HashMap.toList checkedBindings
