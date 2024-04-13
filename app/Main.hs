module Main (main) where

import Lang
import Relude
import Text.Megaparsec
import Lexer (tokenise)

main :: IO ()
main = do
    args <- getArgs
    input <- case args of
        [] -> getLine
        (path : _) -> readFileText path
    input
        & parseMaybe tokenise >>= parseMaybe lambdaCalc
        & flip whenJust (putTextLn . either show pretty . reduce)
