{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}

module Repl where

import Common (
    Fixity (..),
    Loc (..),
    Located (..),
    Name_ (TypeName),
    Pass (..),
    PrettyOptions (..),
    prettyAnsi,
    prettyDef,
    unLoc,
 )
import Common qualified as C
import Data.ByteString qualified as BS
import Data.EnumMap.Strict qualified as EMap
import Data.HashMap.Strict qualified as HashMap
import Data.IdMap qualified as Map
import Data.Poset (Poset)
import Data.Poset qualified as Poset
import Data.Text qualified as Text
import Data.Text.Encoding (strictBuilderToText, textToStrictBuilder)
import Data.Text.Encoding qualified as Text
import DependencyResolution (FixityMap, Op (..), SimpleOutput (..), cast, resolveDependenciesSimplified')
import Diagnostic (Diagnose, fatal, guardNoErrors, reportExceptions, runDiagnoseWith)
import Effectful
import Error.Diagnose (Diagnostic, Position (..), Report (..), addFile)
import Eval (eval, modifyEnv)
import Eval qualified as V
import Fixity qualified (parse, resolveFixity, run)
import FlatParse.Stateful qualified as FP
import LangPrelude
import Lexer (space1)
import NameGen (NameGen, freshName)
import NameResolution (Scope (..), resolveNames, resolveTerm)
import NameResolution qualified
import Parser (Parser')
import Parser qualified
import Prettyprinter qualified as Pretty
import Prettyprinter.Render.Terminal (putDoc)
import Syntax
import Syntax.AstTraversal
import Syntax.Declaration qualified as D
import Syntax.Term
import Syntax.Value (ValueEnv (..))
import Syntax.Value qualified as V
import System.Console.Isocline
import Trace
import TypeChecker qualified as TC
import TypeChecker.Backend (emptyContext)
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
    , types :: IdMap Name_ VType
    , -- , constructorTable :: TC.ConstructorTable
      lastLoadedFile :: Maybe FilePath
    , loadedFiles :: forall msg. Diagnostic msg -- an empty diagnostic with files
    , input :: Text
    , inputBS :: ByteString
    }

type ReplCtx es =
    ( NameGen :> es
    , IOE :> es
    )

-- | a location placeholder for builtin definitions
builtin :: Loc
builtin = C.Loc Position{file = "<builtin>", begin = (0, 0), end = (0, 0)}

noLoc :: a -> Located a
noLoc = C.Located builtin

emptyEnv :: ReplEnv
emptyEnv = ReplEnv{loadedFiles = mempty, ..}
  where
    values = ValueEnv{topLevel = Map.one TypeName (V.Type (noLoc TypeName)), locals = []}
    fixityMap = Map.one AppOp InfixL
    types = Map.one TypeName (V.Type (noLoc TypeName))
    scope = Scope $ HashMap.singleton "Type" (noLoc TypeName)
    (_, operatorPriorities) = Poset.eqClass AppOp Poset.empty
    lastLoadedFile = Nothing
    -- constructorTable = TC.ConstructorTable Map.empty
    inputBS = BS.empty
    input = Text.empty

-- this function is 90% the same as `processDecls`
-- I don't see a clean way to factor out the repetition, though
mkDefaultEnv :: (Diagnose :> es, NameGen :> es) => Eff es ReplEnv
mkDefaultEnv = do
    (preDecls, scope) <- mkPreprelude
    (afterNameRes, newScope) <- NameResolution.runWithEnv scope do
        resolveNames prelude
    depResOutput@SimpleOutput{fixityMap, operatorPriorities} <-
        resolveDependenciesSimplified' emptyEnv.fixityMap emptyEnv.operatorPriorities $ preDecls <> afterNameRes
    fixityDecls <- Fixity.resolveFixity fixityMap operatorPriorities depResOutput.declarations
    (types, values) <- (\f -> foldlM f (emptyEnv.types, emptyEnv.values) fixityDecls) \(topLevel, values) decl -> do
        (eDecl, newTypes, newValues) <- skipTrace $ TC.processDeclaration' topLevel values decl
        newNewValues <- modifyEnv newValues [eDecl]
        pure (newTypes, newNewValues)
    guardNoErrors
    let newEnv =
            ReplEnv
                { values
                , fixityMap
                , operatorPriorities
                , scope = newScope
                , types
                , lastLoadedFile = Nothing
                , loadedFiles = mempty
                , inputBS = BS.empty
                , input = Text.empty
                -- , constructorTable
                }
    pure newEnv -- foldlM (flip mkBuiltin) newEnv builtins
  where
    mkPreprelude :: NameGen :> es => Eff es ([Declaration 'NameRes], Scope)
    mkPreprelude = do
        false <- freshName' "False"
        a <- freshName' "a"
        let builtinTypes = [C.TypeName, C.IntName, C.NatName, C.TextName, C.CharName]
            decls =
                map (\name -> noLoc $ D.Type (noLoc name) [] []) builtinTypes
                    <> map
                        noLoc
                        [ D.Type (noLoc C.BoolName) [] [D.Constructor builtin (noLoc C.TrueName) [], D.Constructor builtin false []]
                        , D.Type
                            (noLoc C.ListName)
                            [plainBinder a]
                            [ D.Constructor builtin (noLoc C.ConsName) $
                                map noLoc [Name a, App Visible (noLoc (Name (noLoc C.ListName))) (noLoc (Name a))]
                            , D.Constructor builtin (noLoc C.NilName) []
                            ]
                        ]
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
                    , ("Char", noLoc C.CharName)
                    ]
        pure (decls, scope)
    freshName' :: NameGen :> es => Text -> Eff es C.Name
    freshName' = freshName . noLoc . C.Name'

    prelude :: [Declaration 'Parse]
    prelude = []

run :: ReplCtx es => Bool -> ReplEnv -> Eff es ()
run debug env = do
    nextLine <- liftIO $ fromString <$> readlineEx "λ" (Just $ completer env) Nothing
    let nextLineBS = Text.encodeUtf8 nextLine
        input = env.input <> nextLine
        inputBS = env.inputBS <> nextLineBS
        envWithInput = env{input = input <> "\n", inputBS = inputBS <> "\n"}
    newEnv <- runTrace' $ localDiagnose envWithInput [] do
        cmd <- case parseCommand nextLineBS of
            Right cmd -> pure cmd
            Left (newOffset, parser) -> Parser.runWithOffset (BS.length env.inputBS + newOffset) ("<interactive>", inputBS) parser
        replStep envWithInput cmd
    traverse_ (run debug) newEnv
  where
    runTrace'
        | debug = runTraceIO
        | otherwise = skipTrace

replStep :: forall es. (ReplCtx es, Diagnose :> es, Trace :> es) => ReplEnv -> ReplCommand -> Eff es (Maybe ReplEnv)
replStep env@ReplEnv{loadedFiles} command = do
    case command of
        Decls decls -> processDecls env decls
        Expr expr -> do
            (checkedExpr, _) <- processExpr expr
            guardNoErrors
            prettyVal $ eval V.ExtendedEnv{locals = [], topLevel = env.values.topLevel, univars = EMap.empty} checkedExpr
            pure $ Just env
        Type_ expr -> do
            (_, ty) <- processExpr expr
            prettyVal ty
            pure $ Just env
        Load path -> do
            fileContents <- reportExceptions @SomeException (readFileBS path)
            let fileText = decodeUtf8 fileContents
            localDiagnose env [(path, fileText)] do
                decls <- Parser.parseModule (path, fileContents)
                newEnv <- processDecls (env{lastLoadedFile = Just path, loadedFiles = addFile loadedFiles path (toString fileText)}) decls
                newEnv <$ print (pretty path <+> "loaded.")
        Reload -> do
            defaultEnv <- mkDefaultEnv
            case env.lastLoadedFile of
                Nothing -> pure $ Just defaultEnv
                Just path -> replStep defaultEnv (Load path)
        Env -> do
            let mergedEnv = Map.merge (\ty val -> (Just ty, Just val)) ((,Nothing) . Just) ((Nothing,) . Just) env.types env.values.topLevel
            for_ (Map.toList mergedEnv) \(name, (mbTy, mbVal)) -> do
                for_ mbTy \ty -> print $ prettyDef name <+> ":" <+> prettyDef ty
                for_ mbVal \value -> print $ prettyDef name <+> "=" <+> prettyDef value
            pure $ Just env
        Quit -> pure Nothing
        UnknownCommand cmd -> fatal . one $ Err Nothing ("Unknown command:" <+> pretty cmd) [] []
  where
    processExpr :: Term 'Parse -> Eff es (ETerm, VType)
    processExpr expr = do
        afterNameRes <- NameResolution.run env.scope $ resolveTerm expr
        skippedDepRes <- cast.term afterNameRes
        afterFixityRes <- Fixity.run env.fixityMap env.operatorPriorities $ Fixity.parse skippedDepRes
        TC.run env.types do
            let ctx = emptyContext env.values
            (eExpr, vTy) <- TC.generaliseTerm ctx =<< TC.infer ctx afterFixityRes
            pure (eExpr, vTy)

    prettyVal val = do
        let ?opts = PrettyOptions{printIds = False}
        liftIO $ putDoc $ prettyAnsi val <> Pretty.line

localDiagnose :: IOE :> es => ReplEnv -> [(FilePath, Text)] -> Eff (Diagnose : es) (Maybe ReplEnv) -> Eff es (Maybe ReplEnv)
localDiagnose env@ReplEnv{input, loadedFiles} files action =
    runDiagnoseWith newFiles action >>= \case
        Nothing -> pure $ Just env
        Just cmd -> pure cmd
  where
    oldFilesWithInteractive = addFile loadedFiles "<interactive>" (toString input)
    newFiles = foldr (\(path, contents) acc -> addFile acc path (toString contents)) oldFilesWithInteractive files

processDecls :: (Diagnose :> es, Trace :> es, ReplCtx es) => ReplEnv -> [Declaration 'Parse] -> Eff es (Maybe ReplEnv)
processDecls env@ReplEnv{loadedFiles} decls = do
    (afterNameRes, newScope) <- NameResolution.runWithEnv env.scope $ resolveNames decls
    depResOutput@SimpleOutput{fixityMap, operatorPriorities} <-
        resolveDependenciesSimplified' env.fixityMap env.operatorPriorities afterNameRes
    fixityDecls <- Fixity.resolveFixity fixityMap operatorPriorities depResOutput.declarations
    (types, values) <- (\f -> foldlM f (env.types, env.values) fixityDecls) \(topLevel, values) decl -> do
        (eDecl, newTypes, newValues) <- TC.processDeclaration' topLevel values decl
        newNewValues <- modifyEnv newValues [eDecl]
        pure (newTypes, newNewValues)
    guardNoErrors
    pure . Just $
        ReplEnv
            { values
            , fixityMap
            , operatorPriorities
            , scope = newScope
            , types
            , lastLoadedFile = env.lastLoadedFile
            , loadedFiles = loadedFiles
            , input = env.input
            , inputBS = env.inputBS
            -- , constructorTable
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

parseCommand :: ByteString -> Either (Int, Parser' ReplCommand) ReplCommand
parseCommand input = case FP.runParser cmdParser 0 0 input of
    FP.OK (Right cmd) _ _ -> Right cmd
    FP.OK (Left parser) _ remainingInput -> Left (BS.length input - BS.length remainingInput, parser)
    _ -> Left (0, fmap Decls Parser.code <|> fmap Expr Parser.term)
  where
    cmdParser =
        FP.optional_ Lexer.space1
            *> $( FP.switchWithPost
                    (Just [|FP.optional_ Lexer.space1|])
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
        prettyName = show $ prettyDef name
        mbSig = do
            id' <- HashMap.lookup name env.scope.table
            ty <- Map.lookup (unLoc id') env.types
            pure $ show $ prettyDef ty

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
