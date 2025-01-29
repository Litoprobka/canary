{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE RecordWildCards #-}

module Repl where

import Common (Fixity (..), Loc (..), Name, Name_ (TypeName), Pass (..), SimpleName_ (Name'), cast)
import Common qualified as C
import Control.Monad.Combinators (choice)
import Data.HashMap.Strict qualified as HashMap
import Data.Text qualified as Text
import Data.Text.Encoding (strictBuilderToText, textToStrictBuilder)
import DependencyResolution (FixityMap, Op, SimpleOutput (..), resolveDependenciesSimplified')
import Diagnostic (Diagnose, guardNoErrors, runDiagnose)
import Effectful
import Effectful.Reader.Static
import Fixity qualified (parse, resolveFixity, run)
import Interpreter (InterpreterBuiltins (..), Value, eval, modifyEnv)
import LangPrelude
import Lexer (Parser, keyword)
import NameGen (NameGen, freshName)
import NameResolution (Scope (..), resolveNames, resolveTerm)
import NameResolution qualified
import Parser qualified
import Playground (noLoc)
import Poset (Poset)
import Poset qualified
import Syntax
import Syntax.Declaration qualified as D
import Syntax.Term
import Text.Megaparsec (takeRest, try)
import TypeChecker (infer, normalise, typecheck)
import TypeChecker.Backend qualified as TC

data ReplCommand
    = Decls [Declaration 'Parse]
    | Expr (Expr 'Parse)
    | Type_ (Expr 'Parse)
    | Load FilePath
    | Quit

data ReplEnv = ReplEnv
    { values :: HashMap Name Value
    , fixityMap :: FixityMap
    , operatorPriorities :: Poset Op
    , scope :: Scope
    , types :: HashMap Name (Type 'Fixity)
    }

type ReplCtx es =
    ( Reader (InterpreterBuiltins Name) :> es
    , Reader (TC.Builtins Name) :> es
    , NameGen :> es
    , IOE :> es
    )

emptyEnv :: ReplEnv
emptyEnv = ReplEnv{..}
  where
    values = HashMap.empty
    fixityMap = HashMap.singleton Nothing InfixL
    types = HashMap.singleton (noLoc TypeName) (Name $ noLoc TypeName)
    scope = Scope $ HashMap.singleton (Name' "Type") (noLoc TypeName)
    (_, operatorPriorities) = Poset.eqClass Nothing Poset.empty

mkDefaultEnv :: (Diagnose :> es, NameGen :> es) => Eff es (InterpreterBuiltins Name, TC.Builtins Name, ReplEnv)
mkDefaultEnv = do
    (preDecls, scope) <- mkPreprelude
    ((afterNameRes, builtins, tcbuiltins), newScope) <- NameResolution.runWithEnv scope do
        decls' <- resolveNames prelude
        builtins <- traverse NameResolution.resolve InterpreterBuiltins{true = "True", cons = "Cons", nil = "Nil"}
        let tcbuiltins = TC.Builtins{subtypeRelations = [(noLoc C.NatName, noLoc C.IntName)]}
        pure (decls', builtins, tcbuiltins)
    depResOutput@SimpleOutput{fixityMap, operatorPriorities} <-
        resolveDependenciesSimplified' emptyEnv.fixityMap emptyEnv.operatorPriorities $ preDecls <> afterNameRes
    fixityDecls <- Fixity.resolveFixity fixityMap operatorPriorities depResOutput.declarations
    newTypes <- typecheck emptyEnv.types tcbuiltins fixityDecls
    let newValEnv = modifyEnv builtins emptyEnv.values fixityDecls
    guardNoErrors
    let finalEnv =
            ReplEnv
                { values = newValEnv
                , fixityMap
                , operatorPriorities
                , scope = newScope
                , types = newTypes
                }
    pure (builtins, tcbuiltins, finalEnv)
  where
    mkPreprelude :: NameGen :> es => Eff es ([Declaration 'NameRes], Scope)
    mkPreprelude = do
        true <- freshName' "True"
        false <- freshName' "False"
        a <- freshName' "a"
        cons <- freshName' "Cons"
        nil <- freshName' "Nil"
        let builtinTypes = [C.TypeName, C.IntName, C.NatName, C.TextName]
            decls =
                [ D.Type Blank (noLoc C.BoolName) [] [D.Constructor Blank true [], D.Constructor Blank false []]
                , D.Type
                    Blank
                    (noLoc C.ListName)
                    [plainBinder a]
                    [D.Constructor Blank cons [Name a, Name (noLoc C.ListName) `Application` Name a], D.Constructor Blank nil []]
                ]
                    <> map (\name -> D.Type Blank (noLoc name) [] []) builtinTypes
            scope =
                Scope . HashMap.fromList . map (first C.Name') $
                    [ ("Type", noLoc C.TypeName)
                    , ("Bool", noLoc C.BoolName)
                    , ("True", true)
                    , ("False", false)
                    , ("List", noLoc C.ListName)
                    , ("Cons", cons)
                    , ("Nil", nil)
                    , ("Int", noLoc C.IntName)
                    , ("Nat", noLoc C.NatName)
                    , ("Text", noLoc C.TextName)
                    ]
        pure (decls, scope)
    freshName' :: NameGen :> es => Text -> Eff es C.Name
    freshName' = freshName . noLoc . C.Name'
    prelude =
        [ D.Type Blank "Unit" [] [D.Constructor Blank "MkUnit" []]
        , D.Value Blank (FunctionB "id" [VarP "x"] (Name "x")) []
        , D.Value Blank (FunctionB "const" [VarP "x", VarP "y"] (Name "x")) []
        , D.Fixity Blank C.InfixL "|>" (C.PriorityRelation [] [] [])
        , D.Fixity Blank C.InfixR "<|" (C.PriorityRelation [] ["|>"] [])
        , D.Fixity Blank C.InfixR "<<" (C.PriorityRelation [] [] [">>"]) -- this is bugged atm
        , D.Fixity Blank C.InfixL ">>" (C.PriorityRelation [Just "|>"] [] [])
        , D.Value Blank (FunctionB "|>" [VarP "x", VarP "f"] (Name "f" `Application` Name "x")) []
        , D.Value Blank (FunctionB "<|" [VarP "f", VarP "x"] (Name "f" `Application` Name "x")) []
        , D.Value Blank (FunctionB ">>" [VarP "f", VarP "g", VarP "x"] (Name "g" `Application` (Name "f" `Application` Name "x"))) []
        , D.Value Blank (FunctionB "<<" [VarP "f", VarP "g", VarP "x"] (Name "f" `Application` (Name "g" `Application` Name "x"))) []
        , D.Value
            Blank
            ( FunctionB
                "map"
                [VarP "f", VarP "xs"]
                ( Case
                    Blank
                    (Name "xs")
                    [ (ConstructorP "Nil" [], Name "Nil")
                    , (ConstructorP "Cons" [VarP "h", VarP "t"], app "Cons" [app "f" ["h"], app "map" ["f", "t"]])
                    ]
                )
            )
            []
        ]
    app :: Term p -> [Term p] -> Term p
    app = foldl' Application

run :: ReplCtx es => ReplEnv -> Eff es ()
run env = do
    putText ">> "
    input <- liftIO takeInputChunk
    newEnv <- localDiagnose env ("<interactive>", input) do
        replStep env =<< Parser.run ("<interactive>", input) parseCommand
    traverse_ run newEnv

replStep :: (ReplCtx es, Diagnose :> es) => ReplEnv -> ReplCommand -> Eff es (Maybe ReplEnv)
replStep env command = do
    builtins <- ask
    case command of
        Decls decls -> processDecls env decls
        Expr expr -> do
            (checkedExpr, _) <- processExpr expr
            guardNoErrors
            print $ pretty $ eval builtins env.values checkedExpr
            pure $ Just env
        Type_ expr -> do
            (_, ty) <- processExpr expr
            print ty
            pure $ Just env
        Load path -> do
            fileContents <- decodeUtf8 <$> readFileBS path
            localDiagnose env (path, fileContents) do
                decls <- Parser.parseModule (path, fileContents)
                processDecls env decls
        Quit -> pure Nothing
  where
    processExpr expr = do
        tcbuiltins <- ask
        afterNameRes <- NameResolution.run env.scope $ resolveTerm expr
        afterFixityRes <- Fixity.run env.fixityMap env.operatorPriorities $ Fixity.parse $ cast afterNameRes
        fmap (afterFixityRes,) $ TC.run (Right <$> env.types) tcbuiltins $ normalise $ infer afterFixityRes

localDiagnose :: IOE :> es => a -> (FilePath, Text) -> Eff (Diagnose : es) (Maybe a) -> Eff es (Maybe a)
localDiagnose env file action =
    runDiagnose file action >>= \case
        Nothing -> pure $ Just env
        Just cmd -> pure cmd

processDecls :: (Diagnose :> es, ReplCtx es) => ReplEnv -> [Declaration 'Parse] -> Eff es (Maybe ReplEnv)
processDecls env decls = do
    builtins <- ask
    tcbuiltins <- ask
    (afterNameRes, newScope) <- NameResolution.runWithEnv env.scope $ resolveNames decls
    depResOutput@SimpleOutput{fixityMap, operatorPriorities} <-
        resolveDependenciesSimplified' env.fixityMap env.operatorPriorities afterNameRes
    fixityDecls <- Fixity.resolveFixity fixityMap operatorPriorities depResOutput.declarations
    newTypes <- typecheck env.types tcbuiltins fixityDecls
    let newValEnv = modifyEnv builtins env.values fixityDecls
    guardNoErrors
    pure . Just $
        ReplEnv
            { values = newValEnv
            , fixityMap
            , operatorPriorities
            , scope = newScope
            , types = newTypes <> env.types
            }

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
    choice @[]
        [ keyword ":t" *> fmap Type_ Parser.expression
        , keyword ":q" $> Quit
        , keyword ":load" *> fmap (Load . Text.unpack) takeRest
        , try $ fmap Decls Parser.code
        , fmap Expr Parser.expression
        ]
