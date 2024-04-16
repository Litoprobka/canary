{-# LANGUAGE LambdaCase #-}
module Main (main) where

import Relude
import Text.Megaparsec
import Parser (code)

main :: IO ()
main = do
    args <- getArgs
    (fileName, input) <- case args of
        [] -> ("cli", ) <$> getLine
        (path : _) -> (path, ) <$> readFileText path
    input & parse (usingReaderT pos1 code) fileName & \case
        Left err -> putStrLn $ errorBundlePretty err
        Right decls -> traverse_ print decls
