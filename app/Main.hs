{-# LANGUAGE LambdaCase #-}

module Main (main) where

import Relude

import NameResolution
import Text.Megaparsec

import Data.These.Combinators
import Parser (code)

main :: IO ()
main = do
    args <- getArgs
    (fileName, input) <- case args of
        [] -> ("cli",) <$> getLine
        (path : _) -> (path,) <$> readFileText path
    input & parse (usingReaderT pos1 code) fileName & \case
        Left err -> putStrLn $ errorBundlePretty err
        Right decls -> do
            traverse_ print decls
            putTextLn "resolved names:"
            bindings <- case resolveNames decls of
                Clean bindings -> pure bindings
                Errors errs bindings -> do
                    case justHere errs of
                        Just errs' -> putTextLn $ "errors: " <> foldMap show errs'
                        Nothing -> pass
                    case justThere errs of
                        Just warnings -> putTextLn $ "warnings: " <> foldMap show warnings
                        Nothing -> pass
                    pure bindings
            traverse_ print bindings
