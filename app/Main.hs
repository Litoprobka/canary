{-# LANGUAGE LambdaCase #-}
module Main (main) where

import Relude
import Text.Megaparsec
import Parser (code)

main :: IO ()
main = do
    args <- getArgs
    input <- case args of
        [] -> getLine
        (path : _) -> readFileText path
    input & parse (usingReaderT pos1 code) "cli" & \case
        Left err -> putStrLn $ errorBundlePretty err
        Right decls -> traverse_ print decls
