{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE RecordWildCards #-}

module Repl where

import Common (Fixity (..), Loc (..), Name, Name_ (TypeName), Pass (..), SimpleName_ (Name'), cast, noLoc)
import Common qualified as C
import Control.Exception qualified as Exception
import Control.Monad.Combinators (choice)
import Data.EnumMap.Lazy qualified as LMap
import Data.EnumMap.Strict qualified as Map
import Data.HashMap.Strict qualified as HashMap
import Data.Text qualified as Text
import Data.Text.Encoding (strictBuilderToText, textToStrictBuilder)
import DependencyResolution (FixityMap, Op (..), SimpleOutput (..), resolveDependenciesSimplified')
import Diagnostic (Diagnose, fatal, guardNoErrors, runDiagnose)
import Effectful
import Effectful.Labeled
import Effectful.State.Static.Local (evalState, execState, modifyM, runState)
import Error.Diagnose (Report (..))
import Fixity qualified (parse, resolveFixity, run)
import Interpreter (ValueEnv, eval, modifyEnv)
import Interpreter qualified as V
import LangPrelude
import Lexer (Parser, keyword, symbol)
import NameGen (NameGen, freshName)
import NameResolution (Scope (..), resolveNames, resolveTerm)
import NameResolution qualified
import Parser qualified
import Poset (Poset)
import Poset qualified
import Syntax
import Syntax.Declaration qualified as D
import Syntax.Term
import Text.Megaparsec (takeRest, try)
import TypeChecker (infer, inferDeclaration, normalise)
import TypeChecker.Backend (withValues)
import TypeChecker.Backend qualified as TC

data ReplCommand
    = Decls [Declaration 'Parse]
    | Expr (Expr 'Parse)
    | Type_ (Expr 'Parse)
    | Load FilePath
    | Quit
    | UnknownCommand Text

data ReplEnv = ReplEnv
    { values :: ValueEnv
    , fixityMap :: FixityMap
    , operatorPriorities :: Poset Op
    , scope :: Scope
    , types :: EnumMap Name TC.Type'
    -- , inputHistory :: Zipper Text? -- todo: remember previous commands
    }

type ReplCtx es =
    ( NameGen :> es
    , IOE :> es
    )

emptyEnv :: ReplEnv
emptyEnv = ReplEnv{..}
  where
    values = LMap.singleton (noLoc TypeName) (V.TyCon (noLoc TypeName))
    fixityMap = Map.singleton AppOp InfixL
    types = Map.singleton (noLoc TypeName) (V.TyCon (noLoc TypeName))
    scope = Scope $ HashMap.singleton (Name' "Type") (noLoc TypeName)
    (_, operatorPriorities) = Poset.eqClass AppOp Poset.empty

mkDefaultEnv :: (Diagnose :> es, NameGen :> es) => Eff es ReplEnv
mkDefaultEnv = do
    (preDecls, scope) <- mkPreprelude
    (afterNameRes, newScope) <- NameResolution.runWithEnv scope do
        resolveNames prelude
    depResOutput@SimpleOutput{fixityMap, operatorPriorities} <-
        resolveDependenciesSimplified' emptyEnv.fixityMap emptyEnv.operatorPriorities $ preDecls <> afterNameRes
    fixityDecls <- Fixity.resolveFixity fixityMap operatorPriorities depResOutput.declarations
    (types, values) <- runLabeled @"values" (runState emptyEnv.values) $ runLabeled @"types" (execState emptyEnv.types) $ TC.run do
        for_ fixityDecls \decl -> do
            inferDeclaration decl
            withValues $ modifyM $ flip modifyEnv [decl]
    guardNoErrors
    let finalEnv =
            ReplEnv
                { values
                , fixityMap
                , operatorPriorities
                , scope = newScope
                , types
                }
    pure finalEnv
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
                map
                    noLoc
                    [ D.Type (noLoc C.BoolName) [] [D.Constructor Blank true [], D.Constructor Blank false []]
                    , D.Type
                        (noLoc C.ListName)
                        [plainBinder a]
                        [ D.Constructor Blank cons $ map noLoc [Name a, noLoc (Name (noLoc C.ListName)) `App` noLoc (Name a)]
                        , D.Constructor Blank nil []
                        ]
                    ]
                    <> map (\name -> noLoc $ D.Type (noLoc name) [] []) builtinTypes
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
        []

{- D.Type Blank "Unit" [] [D.Constructor Blank "MkUnit" []]
-- , D.Value Blank (FunctionB "id" [VarP "x"] (Name "x")) []
-- , D.Value Blank (FunctionB "const" [VarP "x", VarP "y"] (Name "x")) []
-- , D.Fixity Blank C.InfixL "|>" (C.PriorityRelation [] [] [])
-- , D.Fixity Blank C.InfixR "<|" (C.PriorityRelation [] ["|>"] [])
-- , D.Fixity Blank C.InfixR "<<" (C.PriorityRelation [] [] [">>"]) -- this is bugged atm
-- , D.Fixity Blank C.InfixL ">>" (C.PriorityRelation [Just "|>"] [] [])
-- , D.Value Blank (FunctionB "|>" [VarP "x", VarP "f"] (Name "f" `App` Name "x")) []
-- , D.Value Blank (FunctionB "<|" [VarP "f", VarP "x"] (Name "f" `App` Name "x")) []
-- , D.Value Blank (FunctionB ">>" [VarP "f", VarP "g", VarP "x"] (Name "g" `App` (Name "f" `App` Name "x"))) []
-- , D.Value Blank (FunctionB "<<" [VarP "f", VarP "g", VarP "x"] (Name "f" `App` (Name "g" `App` Name "x"))) []
, D.Value
    Blank
    ( FunctionB
        "map"
        [VarP "f", VarP "xs"]
        ( Case
            Blank
            (Name "xs")
            [ (ConstructorP "Nil" [], Name "Nil")
            , (ConstructorP "Cons" [VarP "h", VarP "t"], app "Cons" [App "f" "h", app "map" ["f", "t"]])
            ]
        )
    )
    []

app :: Term p -> [Term p] -> Term p
app = foldl' App
-}

run :: ReplCtx es => ReplEnv -> Eff es ()
run env = do
    putText ">> "
    input <- liftIO takeInputChunk
    newEnv <- localDiagnose env ("<interactive>", input) do
        replStep env =<< Parser.run ("<interactive>", input) parseCommand
    traverse_ run newEnv

-- todo: locations of previous expressions get borked
replStep :: (ReplCtx es, Diagnose :> es) => ReplEnv -> ReplCommand -> Eff es (Maybe ReplEnv)
replStep env command = do
    case command of
        Decls decls -> processDecls env decls
        Expr expr -> do
            ((checkedExpr, _), values) <- runLabeled @"values" (runState env.values) $ processExpr expr
            guardNoErrors
            print . pretty =<< eval values checkedExpr
            pure $ Just env{values}
        Type_ expr -> do
            ((_, ty), values) <- runLabeled @"values" (runState env.values) $ processExpr expr
            print ty
            pure $ Just env{values}
        Load path -> do
            excOrFile <- liftIO $ Exception.try @SomeException (decodeUtf8 <$> readFileBS path)
            case excOrFile of
                Right fileContents -> localDiagnose env (path, fileContents) do
                    decls <- Parser.parseModule (path, fileContents)
                    processDecls env decls
                Left exc -> do
                    putStrLn $ "An exception has occured while reading the file: " <> displayException exc
                    pure $ Just env
        Quit -> pure Nothing
        UnknownCommand cmd -> fatal . one $ Err Nothing ("Unknown command:" <+> pretty cmd) [] []
  where
    processExpr expr = do
        afterNameRes <- NameResolution.run env.scope $ resolveTerm expr
        afterFixityRes <- Fixity.run env.fixityMap env.operatorPriorities $ Fixity.parse $ fmap cast afterNameRes
        fmap (afterFixityRes,) $ runLabeled @"types" (evalState env.types) $ TC.run $ normalise $ infer afterFixityRes

localDiagnose :: IOE :> es => a -> (FilePath, Text) -> Eff (Diagnose : es) (Maybe a) -> Eff es (Maybe a)
localDiagnose env file action =
    runDiagnose file action >>= \case
        Nothing -> pure $ Just env
        Just cmd -> pure cmd

processDecls :: (Diagnose :> es, ReplCtx es) => ReplEnv -> [Declaration 'Parse] -> Eff es (Maybe ReplEnv)
processDecls env decls = do
    (afterNameRes, newScope) <- NameResolution.runWithEnv env.scope $ resolveNames decls
    depResOutput@SimpleOutput{fixityMap, operatorPriorities} <-
        resolveDependenciesSimplified' env.fixityMap env.operatorPriorities afterNameRes
    fixityDecls <- Fixity.resolveFixity fixityMap operatorPriorities depResOutput.declarations
    (types, values) <- runLabeled @"values" (runState env.values) $ runLabeled @"types" (execState env.types) $ TC.run do
        for_ fixityDecls \decl -> do
            inferDeclaration decl
            withValues $ modifyM $ flip modifyEnv [decl]
    guardNoErrors
    pure . Just $
        ReplEnv
            { values
            , fixityMap
            , operatorPriorities
            , scope = newScope
            , types
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
        [ keyword ":t" *> fmap Type_ Parser.term
        , keyword ":q" $> Quit
        , keyword ":load" *> fmap (Load . Text.unpack) takeRest
        , symbol ":" *> (UnknownCommand <$> takeRest)
        , try $ fmap Decls Parser.code
        , fmap Expr Parser.term
        ]
