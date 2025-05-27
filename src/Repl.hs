{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}

module Repl where

import Common (Fixity (..), Loc (..), Name, Name_ (TypeName), Pass (..), SimpleName_ (Name'), cast, noLoc)
import Common qualified as C
import Data.EnumMap qualified as EnumMap
import Data.EnumMap.Lazy qualified as LMap
import Data.EnumMap.Strict qualified as Map
import Data.HashMap.Strict qualified as HashMap
import Data.Text.Encoding (strictBuilderToText, textToStrictBuilder)
import Data.Text.Encoding qualified as Text
import DependencyResolution (FixityMap, Op (..), SimpleOutput (..), resolveDependenciesSimplified')
import Diagnostic (Diagnose, fatal, guardNoErrors, reportExceptions, runDiagnose)
import Effectful
import Effectful.Labeled
import Effectful.Labeled.Reader (runReader)
import Effectful.Reader.Static (ask)
import Effectful.State.Static.Local (evalState, runState)
import Error.Diagnose (Report (..))
import Eval (ValueEnv (..), eval, modifyEnv)
import Eval qualified as V
import Fixity qualified (parse, resolveFixity, run)
import FlatParse.Stateful qualified as FP
import LangPrelude
import Lexer (Parser, space')
import NameGen (NameGen, freshName)
import NameResolution (Scope (..), resolveNames, resolveTerm)
import NameResolution qualified
import Parser qualified
import Poset (Poset)
import Poset qualified
import Syntax
import Syntax.Declaration qualified as D
import Syntax.Term
import System.Console.Isocline
import Text.Megaparsec (try)
import TypeChecker (infer, inferDeclaration, normalise)
import TypeChecker.Backend qualified as TC

data ReplCommand
    = Decls [Declaration 'Parse]
    | Expr (Expr 'Parse)
    | Type_ (Expr 'Parse)
    | Load FilePath
    | Reload
    | Env
    | Quit
    | UnknownCommand Text

data ReplEnv = ReplEnv
    { values :: ValueEnv
    , fixityMap :: FixityMap
    , operatorPriorities :: Poset Op
    , scope :: Scope
    , types :: EnumMap Name TC.Type'
    , lastLoadedFile :: Maybe FilePath
    }

type ReplCtx es =
    ( NameGen :> es
    , IOE :> es
    )

emptyEnv :: ReplEnv
emptyEnv = ReplEnv{..}
  where
    values = ValueEnv{values = LMap.singleton (noLoc TypeName) (V.TyCon (noLoc TypeName)), skolems = Map.empty}
    fixityMap = Map.singleton AppOp InfixL
    types = Map.singleton (noLoc TypeName) (noLoc $ V.TyCon (noLoc TypeName))
    scope = Scope $ HashMap.singleton (Name' "Type") (noLoc TypeName)
    (_, operatorPriorities) = Poset.eqClass AppOp Poset.empty
    lastLoadedFile = Nothing

-- this function uis 90% the same as `processDecls`
-- I don't see a clean way to factor out the repetition, though
mkDefaultEnv :: (Diagnose :> es, NameGen :> es) => Eff es ReplEnv
mkDefaultEnv = do
    (preDecls, scope) <- mkPreprelude
    (afterNameRes, newScope) <- NameResolution.runWithEnv scope do
        resolveNames prelude
    depResOutput@SimpleOutput{fixityMap, operatorPriorities} <-
        resolveDependenciesSimplified' emptyEnv.fixityMap emptyEnv.operatorPriorities $ preDecls <> afterNameRes
    fixityDecls <- Fixity.resolveFixity fixityMap operatorPriorities depResOutput.declarations
    (env, types) <- runState emptyEnv.types $ TC.run emptyEnv.values do
        env <- ask @TC.InfState
        foldlM addDecl env fixityDecls
    guardNoErrors
    pure $
        ReplEnv
            { values = env.values
            , fixityMap
            , operatorPriorities
            , scope = newScope
            , types
            , lastLoadedFile = Nothing
            }
  where
    addDecl env decl = TC.local' (const env) do
        envDiff <- inferDeclaration decl
        newValues <- modifyEnv (envDiff env.values) [decl]
        pure env{TC.values = newValues}

    mkPreprelude :: NameGen :> es => Eff es ([Declaration 'NameRes], Scope)
    mkPreprelude = do
        false <- freshName' "False"
        a <- freshName' "a"
        let builtinTypes = [C.TypeName, C.IntName, C.NatName, C.TextName]
            decls =
                map
                    noLoc
                    [ D.Type (noLoc C.BoolName) [] [D.Constructor Blank (noLoc C.TrueName) [], D.Constructor Blank false []]
                    , D.Type
                        (noLoc C.ListName)
                        [plainBinder a]
                        [ D.Constructor Blank (noLoc C.ConsName) $ map noLoc [Name a, noLoc (Name (noLoc C.ListName)) `App` noLoc (Name a)]
                        , D.Constructor Blank (noLoc C.NilName) []
                        ]
                    ]
                    <> map (\name -> noLoc $ D.Type (noLoc name) [] []) builtinTypes
            scope =
                Scope . HashMap.fromList . map (first C.Name') $
                    [ ("Type", noLoc C.TypeName)
                    , ("Bool", noLoc C.BoolName)
                    , ("True", noLoc C.TrueName)
                    , ("False", false)
                    , ("List", noLoc C.ListName)
                    , ("Cons", noLoc C.ConsName)
                    , ("Nil", noLoc C.NilName)
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
    input <- liftIO $ fromString <$> readlineEx ">>" (Just $ completer env) Nothing
    let inputBS = Text.encodeUtf8 input
    newEnv <- localDiagnose env ("<interactive>", input) do
        cmd <- case parseCommand inputBS of
            Right cmd -> pure cmd
            Left (remainingInput, parser) -> Parser.run ("<interactive>", remainingInput) parser
        replStep env cmd
    traverse_ run newEnv

-- todo: locations of previous expressions get borked
replStep :: (ReplCtx es, Diagnose :> es) => ReplEnv -> ReplCommand -> Eff es (Maybe ReplEnv)
replStep env command = do
    case command of
        Decls decls -> processDecls env decls
        Expr expr -> do
            (checkedExpr, _) <- runReader @"values" env.values $ processExpr env.types expr
            guardNoErrors
            print . pretty =<< eval env.values checkedExpr
            pure $ Just env
        Type_ expr -> do
            (_, ty) <- runReader @"values" env.values $ processExpr env.types expr
            print $ pretty ty
            pure $ Just env
        Load path -> do
            fileContents <- reportExceptions @SomeException (readFileBS path)
            localDiagnose env (path, decodeUtf8 fileContents) do
                decls <- Parser.parseModule (path, fileContents)
                processDecls (env{lastLoadedFile = Just path}) decls
        Reload -> do
            defaultEnv <- mkDefaultEnv
            case env.lastLoadedFile of
                Nothing -> pure $ Just defaultEnv
                Just path -> replStep defaultEnv (Load path)
        Env -> do
            -- since the to/from enum conversion is lossy, only ids are available here
            -- perhaps I should write a custom wrapper for IntMap?..
            for_ (Map.toList env.types) \(name, ty) ->
                print $ pretty name <+> ":" <+> pretty ty
            for_ (Map.toList env.values.values) \(name, value) ->
                print $ pretty name <+> "=" <+> pretty value
            pure $ Just env
        Quit -> pure Nothing
        UnknownCommand cmd -> fatal . one $ Err Nothing ("Unknown command:" <+> pretty cmd) [] []
  where
    processExpr types expr = evalState types do
        afterNameRes <- NameResolution.run env.scope $ resolveTerm expr
        afterFixityRes <- Fixity.run env.fixityMap env.operatorPriorities $ Fixity.parse $ fmap cast afterNameRes
        fmap (afterFixityRes,) $ runLabeled @"types" (evalState env.types) $ TC.run env.values $ normalise $ infer afterFixityRes

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
    (newEnv, types) <- runState env.types $ TC.run env.values do
        tenv <- ask @TC.InfState
        foldlM addDecl tenv fixityDecls
    guardNoErrors
    pure . Just $
        ReplEnv
            { values = newEnv.values
            , fixityMap
            , operatorPriorities
            , scope = newScope
            , types
            , lastLoadedFile = env.lastLoadedFile
            }
  where
    addDecl tenv decl = TC.local' (const tenv) do
        envDiff <- inferDeclaration decl
        newValues <- modifyEnv (envDiff tenv.values) [decl]
        pure tenv{TC.values = newValues}

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

parseCommand :: ByteString -> Either (ByteString, Parser ReplCommand) ReplCommand
parseCommand input = case FP.runParser cmdParser 0 0 input of
    FP.OK (Right cmd) _ _ -> Right cmd
    FP.OK (Left parser) _ remainingInput -> Left (remainingInput, parser)
    _ -> Left (input, try (fmap Decls Parser.code) <|> fmap Expr Parser.term)
  where
    cmdParser =
        $( FP.switchWithPost
            (Just [|Lexer.space'|])
            [|
                case _ of
                    ":t" -> pure $ Left (Type_ <$> Parser.term)
                    ":q" -> pure $ Right Quit
                    ":r" -> pure $ Right Reload
                    ":env" -> pure $ Right Env
                    ":load" -> Right . Load <$> FP.takeRestString
                    ":" -> Right . UnknownCommand . decodeUtf8 <$> FP.takeRest
                |]
         )

completer :: ReplEnv -> CompletionEnv -> String -> IO ()
completer env cenv input = completeWord cenv input Nothing wordCompletion
  where
    wordCompletion word =
        filter (isPrefix word) . fmap toCompletion $ HashMap.keys env.scope.table
    toCompletion name = Completion prettyName (prettyName <> maybe "" (" : " <>) mbSig) ""
      where
        prettyName = show $ pretty name
        mbSig = do
            id' <- HashMap.lookup name env.scope.table
            ty <- EnumMap.lookup id' env.types
            pure $ show $ pretty ty

{-
-- perhaps we *should* have a separate lexer pass after all?..
keywordHighlighter :: String -> Fmt
keywordHighlighter "" = ""
keywordHighlighter str@(c : _)
    | isSpace c =
        let (space, rest) = span isSpace str
         in space <> keywordHighlighter rest
    | otherwise =
        let (word, rest) = break isSpace str
         in highlight word <> keywordHighlighter rest
  where
    highlight word
        | fromString word `HashSet.member` keywords = style "purple" word
        | fromString word `HashSet.member` specialSymbols = style "green" word
        | otherwise = word
-}
