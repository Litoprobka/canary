{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE RecordWildCards #-}

module Repl where

import Common (Fixity (..), Name, Pass (..), cast)
import Control.Monad.Combinators (choice)
import Data.HashMap.Strict qualified as HashMap
import Data.Text qualified as Text
import Data.Text.Encoding (strictBuilderToText, textToStrictBuilder)
import DependencyResolution (FixityMap, Op, SimpleOutput (..), resolveDependenciesSimplified')
import Diagnostic (runDiagnose)
import Effectful
import Effectful.Reader.Static
import Fixity qualified (parse, resolveFixity, run)
import Interpreter (InterpreterBuiltins (..), Value, eval, modifyEnv)
import LangPrelude
import Lexer (Parser, keyword)
import NameGen (NameGen)
import NameResolution (Scope (..), resolveExpr, resolveNames)
import NameResolution qualified
import Parser qualified
import Poset (Poset)
import Poset qualified
import Syntax
import Text.Megaparsec (takeRest, try)
import TypeChecker (infer, normalise, typecheck)
import TypeChecker.Backend qualified as TC

data ReplCommand
    = Decls [Declaration 'Parse]
    | Expr (Expression 'Parse)
    | Type_ (Expression 'Parse)
    | Load FilePath
    | Quit

data ReplEnv = ReplEnv
    { values :: HashMap Name Value
    , fixityMap :: FixityMap
    , operatorPriorities :: Poset Op
    , scope :: Scope
    , types :: HashMap Name (Type' 'Fixity)
    }

type ReplCtx es =
    ( Reader (InterpreterBuiltins Name) :> es
    , Reader (TC.Builtins Name) :> es
    , NameGen :> es
    , IOE :> es
    )

mkDefaultEnv :: ReplEnv
mkDefaultEnv = ReplEnv{..}
  where
    values = HashMap.empty
    fixityMap = HashMap.singleton Nothing InfixL
    types = HashMap.empty
    scope = Scope HashMap.empty
    (_, operatorPriorities) = Poset.eqClass Nothing Poset.empty

run :: ReplCtx es => ReplEnv -> Eff es ()
run = replStep >=> traverse run >=> const pass

replStep :: ReplCtx es => ReplEnv -> Eff es (Maybe ReplEnv)
replStep env = do
    putText ">> "
    input <- liftIO takeInputChunk
    localDiagnose input do
        builtins <- ask
        command <- Parser.run ("<interactive>", input) parseCommand
        case command of
            Decls decls -> processDecls decls
            Expr expr -> do
                (checkedExpr, _) <- processExpr expr
                print $ pretty $ eval builtins env.values checkedExpr
                pure $ Just env
            Type_ expr -> do
                (_, ty) <- processExpr expr
                print ty
                pure $ Just env
            Load path -> do
                fileContents <- decodeUtf8 <$> readFileBS path
                decls <- Parser.parseModule (path, fileContents)
                processDecls decls
            Quit -> pure Nothing
  where
    processDecls decls = do
        builtins <- ask
        tcbuiltins <- ask
        (afterNameRes, newScope) <- NameResolution.runWithEnv env.scope $ resolveNames decls
        depResOutput <- resolveDependenciesSimplified' env.fixityMap env.operatorPriorities afterNameRes
        fixityDecls <- Fixity.resolveFixity env.fixityMap env.operatorPriorities depResOutput.declarations
        newTypes <- typecheck env.types tcbuiltins fixityDecls
        let newValEnv = modifyEnv builtins env.values fixityDecls
        pure . Just $
            ReplEnv
                { values = newValEnv
                , fixityMap = depResOutput.fixityMap -- todo: use previous fixity
                , operatorPriorities = depResOutput.operatorPriorities -- samn as abivn
                , scope = newScope
                , types = newTypes <> env.types
                }

    processExpr expr = do
        tcbuiltins <- ask
        afterNameRes <- NameResolution.run env.scope $ resolveExpr expr
        afterFixityRes <- Fixity.run env.fixityMap env.operatorPriorities $ Fixity.parse $ cast afterNameRes
        fmap (afterFixityRes,) $ TC.run (Right <$> env.types) tcbuiltins $ normalise $ infer afterFixityRes

    localDiagnose input action =
        runDiagnose ("<interactive>", input) action >>= \case
            Nothing -> pure $ Just env
            Just cmd -> pure cmd

-- takes a line of input, or a bunch of lines in :{ }:
takeInputChunk :: IO Text
takeInputChunk = do
    line <- getLine
    if line == ":{"
        then strictBuilderToText <$> go mempty
        else pure line
  where
    go acc = do
        line <- getLine
        if line == ":}"
            then pure acc
            else go $ acc <> textToStrictBuilder line <> textToStrictBuilder "\n"

parseCommand :: Parser ReplCommand
parseCommand =
    choice
        [ keyword ":t" *> fmap Type_ Parser.expression
        , keyword ":q" $> Quit
        , keyword ":load" *> fmap (Load . Text.unpack) takeRest
        , try $ fmap Decls Parser.code
        , fmap Expr Parser.expression
        ]
