{-# LANGUAGE LambdaCase #-}

module Main (main) where

import Relude

import NameResolution
import NameGen (runNameGen)
import Effectful
import Parser (parseModule)
import Prettyprinter.Render.Text (putDoc)
import Prettyprinter
import TypeChecker (typecheck)
import Playground (mkDefaults)
import qualified Syntax.Declaration as D
import qualified Data.HashMap.Strict as HashMap
import qualified Syntax.Expression as E
import Interpreter (eval, InterpreterBuiltins (..))
import Fixity
import Diagnostic
import Common

main :: IO ()
main = do
    args <- liftIO getArgs
    (fileName, input) <- case args of
        [] -> ("cli",) <$> getLine
        (path : _) -> (path,) . decodeUtf8 <$> readFileBS path
    void . runEff . runDiagnose (fileName, input) $ runNameGen do
        decls <- parseModule (fileName, input)
        prettyAST decls
        (scope, builtins, env) <- mkDefaults
        (bindings, evalBuiltins, constrs) <- runNameResolution scope do
            bindings <- resolveNames decls
            evalBuiltins <- traverse resolve InterpreterBuiltins{true = "True", cons = "Cons", nil = "Nil"}
            let constrs = HashMap.empty
            pure (bindings, evalBuiltins, constrs)

        putTextLn "resolved names:"
        prettyAST bindings

        fixityResolvedBindings <- resolveFixity testOpMap testGraph bindings
        prettyAST fixityResolvedBindings

        putTextLn "typechecking:"
        types <- typecheck env builtins fixityResolvedBindings 
        liftIO . putDoc $ (<> line) $ vsep $ pretty . uncurry (D.Signature Blank) <$> HashMap.toList types
        case fixityResolvedBindings of
            (D.Value _ (E.ValueBinding _ body) _) : _ ->
                liftIO . putDoc $ (<> line) $ pretty $ eval evalBuiltins constrs HashMap.empty body
            _ -> putTextLn "Not a value"

prettyAST :: (Traversable t, Pretty a, MonadIO m) => t a -> m ()
prettyAST = liftIO . traverse_ (putDoc . (<> line) . pretty)