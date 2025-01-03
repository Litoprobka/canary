module Main (main) where

import Relude

import Common
import Data.HashMap.Strict qualified as HashMap
import Diagnostic
import Effectful
import Fixity
import Interpreter (InterpreterBuiltins (..), eval)
import NameGen (runNameGen)
import NameResolution
import Parser (parseModule)
import Playground (mkDefaults)
import Prettyprinter
import Prettyprinter.Render.Text (putDoc)
import Syntax.Declaration qualified as D
import Syntax.Expression qualified as E
import TypeChecker (typecheck)

main :: IO ()
main = do
    args <- liftIO getArgs
    let (debug, otherArgs) = case args of
            ("debug" : rest) -> (True, rest)
            other -> (False, other)
    (fileName, input) <- case otherArgs of
        [] -> ("cli",) <$> getLine
        (path : _) -> (path,) . decodeUtf8 <$> readFileBS path
    eval' <- runEff . runDiagnose (fileName, input) $ runNameGen do
        decls <- parseModule (fileName, input)
        prettyAST debug decls
        (scope, builtins, env) <- mkDefaults
        (bindings, evalBuiltins) <- runNameResolution scope do
            bindings <- resolveNames decls
            evalBuiltins <- traverse resolve InterpreterBuiltins{true = "True", cons = "Cons", nil = "Nil"}
            pure (bindings, evalBuiltins)

        fixityResolvedBindings <- resolveFixity bindings
        printDebug debug "resolved names:"
        prettyAST debug fixityResolvedBindings

        printDebug debug "typechecking:"
        types <- typecheck env builtins fixityResolvedBindings
        when debug do
            liftIO . putDoc $ (<> line) $ vsep $ pretty . uncurry (D.Signature Blank) <$> HashMap.toList types
        -- the interpreter doesn't support multiple bindings yet, so we evaly the first encountered binding with no env
        pure $ sequence_ $ flip firstJust fixityResolvedBindings \case
            D.Value _ (E.ValueBinding _ body) _ ->
                Just $
                    putDoc $
                        (<> line) $
                            pretty $
                                eval evalBuiltins HashMap.empty HashMap.empty body
            _ -> Nothing
    sequence_ eval'

firstJust :: (t -> Maybe a) -> [t] -> Maybe a
firstJust _ [] = Nothing
firstJust f (x : xs) = f x <|> firstJust f xs

printDebug :: MonadIO m => Bool -> Text -> m ()
printDebug debug = when debug . putTextLn

prettyAST :: (Traversable t, Pretty a, MonadIO m) => Bool -> t a -> m ()
prettyAST debug = when debug . liftIO . traverse_ (putDoc . (<> line) . pretty)
