module Main (main) where

import Lang
import Relude
import Text.Megaparsec

main :: IO ()
main = do
    args <- getArgs
    input <- case args of
        [] -> getLine
        (path : _) -> readFileText path
    case parse lambdaCalc "cli" input of
        Left err -> putStrLn $ errorBundlePretty err
        Right ast -> putTextLn . either show pretty $ reduce ast
