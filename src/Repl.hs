{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}

module Repl where

import Common (
    Fixity (..),
    Literal (..),
    Loc (..),
    Located (..),
    Name,
    Name_ (TypeName),
    Pass (..),
    PrettyOptions (..),
    SimpleName_ (Name'),
    prettyAnsi,
    prettyDef,
 )
import Common qualified as C
import Data.ByteString qualified as BS
import Data.HashMap.Strict qualified as HashMap
import Data.Text qualified as Text
import Data.Text.Encoding (strictBuilderToText, textToStrictBuilder)
import Data.Text.Encoding qualified as Text
import DependencyResolution (FixityMap, Op (..), SimpleOutput (..), cast, resolveDependenciesSimplified')
import Diagnostic (Diagnose, fatal, guardNoErrors, reportExceptions, runDiagnoseWith)
import Effectful
import Effectful.Labeled
import Effectful.Labeled.Reader (Reader, runReader)
import Effectful.Reader.Static (ask)
import Effectful.State.Static.Local (evalState, runState)
import Error.Diagnose (Diagnostic, Position (..), Report (..), addFile)
import Eval (ValueEnv (..), eval, modifyEnv)
import Eval qualified as V
import Fixity qualified (parse, resolveFixity, run)
import FlatParse.Stateful qualified as FP
import IdMap qualified as Map
import LangPrelude
import Lexer (space1)
import NameGen (NameGen, freshName)
import NameResolution (Scope (..), resolveNames, resolveTerm)
import NameResolution qualified
import Parser (Parser')
import Parser qualified
import Poset (Poset)
import Poset qualified
import Prettyprinter qualified as Pretty
import Prettyprinter.Render.Terminal (putDoc)
import Syntax
import Syntax.AstTraversal
import Syntax.Declaration qualified as D
import Syntax.Elaborated (ETerm, Typed (..))
import Syntax.Row (ExtRow (..))
import Syntax.Term
import Syntax.Term qualified as T
import System.Console.Isocline
import TypeChecker (infer, inferDeclaration, normaliseAll)
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
    , types :: IdMap Name TC.Type'_
    , constructorTable :: TC.ConstructorTable
    , lastLoadedFile :: Maybe FilePath
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
    values = ValueEnv{values = Map.one (noLoc TypeName) (V.TyCon (noLoc TypeName) [])}
    fixityMap = Map.one AppOp InfixL
    types = Map.one (noLoc TypeName) (V.TyCon (noLoc TypeName) [])
    scope = Scope $ HashMap.singleton (Name' "Type") (noLoc TypeName)
    (_, operatorPriorities) = Poset.eqClass AppOp Poset.empty
    lastLoadedFile = Nothing
    constructorTable = TC.ConstructorTable Map.empty
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
    ((env, constructorTable), types) <- runState emptyEnv.types $ runState emptyEnv.constructorTable $ TC.run emptyEnv.values do
        env <- ask @TC.Env
        foldlM addDecl env fixityDecls
    guardNoErrors
    let newEnv =
            ReplEnv
                { values = env.values
                , fixityMap
                , operatorPriorities
                , scope = newScope
                , types
                , lastLoadedFile = Nothing
                , loadedFiles = mempty
                , inputBS = BS.empty
                , input = Text.empty
                , constructorTable
                }
    foldlM (flip mkBuiltin) newEnv builtins
  where
    addDecl env decl = TC.local' (const env) do
        (typedDecl, envDiff) <- inferDeclaration decl
        newValues <- modifyEnv (envDiff env.values) [typedDecl]
        pure env{TC.values = newValues}

    -- \| add a built-in function definition to the ReplEnv
    mkBuiltin (rawName, argCount, rawTy, resolveF) env@ReplEnv{..} = do
        ((name, ty, f), newScope) <- NameResolution.runWithEnv env.scope do
            name <- NameResolution.declare $ Name' rawName :@ builtin
            ty <- NameResolution.resolveTerm rawTy
            f <- resolveF
            pure (name, ty, f)
        let val = V.PrimFunction V.PrimFunc{name, remaining = argCount, captured = [], f}
        tyWithoutDepRes <- cast.term ty
        afterFixityRes <- Fixity.run env.fixityMap env.operatorPriorities $ Fixity.parse tyWithoutDepRes
        -- this is really janky
        elaboratedTy <-
            runReader @"values" env.values
                . runLabeled @"types" (evalState env.types)
                . evalState env.types
                . evalState env.constructorTable
                . TC.run env.values
                $ do
                    (expr, tyty) <- normaliseAll do
                        expr' :@ loc ::: tyty <- infer afterFixityRes
                        pure (expr' :@ loc, tyty :@ loc)
                    pure $ expr ::: tyty
        tyAsVal <- V.eval env.values elaboratedTy
        pure
            ReplEnv
                { types = Map.insert name tyAsVal env.types
                , values = ValueEnv $ Map.insert name val env.values.values
                , scope = newScope
                , ..
                }

    mkPreprelude :: NameGen :> es => Eff es ([Declaration 'NameRes], Scope)
    mkPreprelude = do
        false <- freshName' "False"
        a <- freshName' "a"
        let builtinTypes = [C.TypeName, C.IntName, C.NatName, C.TextName, C.CharName]
            decls =
                map
                    noLoc
                    [ D.Type (noLoc C.BoolName) [] [D.Constructor builtin (noLoc C.TrueName) [], D.Constructor builtin false []]
                    , D.Type
                        (noLoc C.ListName)
                        [plainBinder a]
                        [ D.Constructor builtin (noLoc C.ConsName) $ map noLoc [Name a, noLoc (Name (noLoc C.ListName)) `App` noLoc (Name a)]
                        , D.Constructor builtin (noLoc C.NilName) []
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
                    , ("Char", noLoc C.CharName)
                    ]
        pure (decls, scope)
    freshName' :: NameGen :> es => Text -> Eff es C.Name
    freshName' = freshName . noLoc . C.Name'
    builtins =
        [
            ( "reverse"
            , 1
            , T.Function (nameTerm "Text") (nameTerm "Text") :@ builtin
            , pure \case
                V.PrimValue (TextLiteral txt) :| _ -> V.PrimValue $ TextLiteral (Text.reverse txt)
                _ -> error "reverse applied to a non-text value"
            )
        ,
            ( "uncons"
            , 1
            , T.Function
                (nameTerm "Text")
                (T.RecordT (NoExtRow $ fromList [(name' "head", nameTerm "Char"), (name' "tail", nameTerm "Text")]) :@ builtin)
                :@ builtin
            , do
                just <- NameResolution.resolve $ name' "Just"
                nothing <- NameResolution.resolve $ name' "Nothing"
                pure \case
                    V.PrimValue (TextLiteral txt) :| _ -> case Text.uncons txt of
                        Nothing -> V.Con nothing []
                        Just (h, t) ->
                            V.Con
                                just
                                [V.Record $ fromList [(name' "head", V.PrimValue $ CharLiteral (one h)), (name' "tail", V.PrimValue $ TextLiteral t)]]
                    _ -> error "uncons applied to a non-text value"
            )
        ,
            ( "add"
            , 2
            , T.Function (nameTerm "Int") (T.Function (nameTerm "Int") (nameTerm "Int") :@ builtin) :@ builtin
            , pure \case
                V.PrimValue (IntLiteral rhs) :| V.PrimValue (IntLiteral lhs) : _ -> V.PrimValue $ IntLiteral (lhs + rhs)
                _ -> error "invalid arguments to add"
            )
        ,
            ( "sub"
            , 2
            , T.Function (nameTerm "Int") (T.Function (nameTerm "Int") (nameTerm "Int") :@ builtin) :@ builtin
            , pure \case
                V.PrimValue (IntLiteral rhs) :| V.PrimValue (IntLiteral lhs) : _ -> V.PrimValue $ IntLiteral (lhs - rhs)
                _ -> error "invalid arguments to sub"
            )
        ]
    prelude :: [Declaration 'Parse]
    prelude =
        [ D.Type
            (name' "Maybe")
            [VarBinder{var = name' "a", kind = Nothing}]
            [D.Constructor builtin (name' "Just") [nameTerm "a"], D.Constructor builtin (name' "Nothing") []]
            :@ builtin
        ]
    name' txt = Name' txt :@ builtin
    nameTerm txt = T.Name (name' txt) :@ builtin

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
    nextLine <- liftIO $ fromString <$> readlineEx "λ" (Just $ completer env) Nothing
    let nextLineBS = Text.encodeUtf8 nextLine
        input = env.input <> nextLine
        inputBS = env.inputBS <> nextLineBS
        envWithInput = env{input = input <> "\n", inputBS = inputBS <> "\n"}
    newEnv <- localDiagnose envWithInput [] do
        cmd <- case parseCommand nextLineBS of
            Right cmd -> pure cmd
            Left (newOffset, parser) -> Parser.runWithOffset (BS.length env.inputBS + newOffset) ("<interactive>", inputBS) parser
        replStep envWithInput cmd
    traverse_ run newEnv

-- todo: locations of previous expressions get borked
replStep :: forall es. (ReplCtx es, Diagnose :> es) => ReplEnv -> ReplCommand -> Eff es (Maybe ReplEnv)
replStep env@ReplEnv{loadedFiles} command = do
    case command of
        Decls decls -> processDecls env decls
        Expr expr -> do
            checkedExpr <- runReader @"values" env.values $ processExpr env.types expr
            guardNoErrors
            prettyVal =<< eval env.values checkedExpr
            pure $ Just env
        Type_ expr -> do
            (_ ::: ty) <- runReader @"values" env.values $ processExpr env.types expr
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
            let mergedEnv = Map.merge (\ty val -> (Just ty, Just val)) ((,Nothing) . Just) ((Nothing,) . Just) env.types env.values.values
            for_ (Map.toList mergedEnv) \(name, (mbTy, mbVal)) -> do
                for_ mbTy \ty -> print $ prettyDef name <+> ":" <+> prettyDef ty
                for_ mbVal \value -> print $ prettyDef name <+> "=" <+> prettyDef value
            pure $ Just env
        Quit -> pure Nothing
        UnknownCommand cmd -> fatal . one $ Err Nothing ("Unknown command:" <+> pretty cmd) [] []
  where
    processExpr :: IdMap Name TC.Type'_ -> Term 'Parse -> Eff (Labeled "values" (Reader ValueEnv) ': es) ETerm
    processExpr types expr = evalState types do
        afterNameRes <- NameResolution.run env.scope $ resolveTerm expr
        skippedDepRes <- cast.term afterNameRes
        afterFixityRes <- Fixity.run env.fixityMap env.operatorPriorities $ Fixity.parse skippedDepRes
        runLabeled @"types" (evalState env.types)
            . evalState env.constructorTable
            . TC.run env.values
            $ do
                (expr', ty) <- normaliseAll do
                    expr' :@ loc ::: ty <- infer afterFixityRes
                    pure (expr' :@ loc, ty :@ loc)
                pure $ expr' ::: ty

    prettyVal val = do
        liftIO $ putDoc $ prettyAnsi PrettyOptions{printIds = False} val <> Pretty.line

localDiagnose :: IOE :> es => ReplEnv -> [(FilePath, Text)] -> Eff (Diagnose : es) (Maybe ReplEnv) -> Eff es (Maybe ReplEnv)
localDiagnose env@ReplEnv{input, loadedFiles} files action =
    runDiagnoseWith newFiles action >>= \case
        Nothing -> pure $ Just env
        Just cmd -> pure cmd
  where
    oldFilesWithInteractive = addFile loadedFiles "<interactive>" (toString input)
    newFiles = foldr (\(path, contents) acc -> addFile acc path (toString contents)) oldFilesWithInteractive files

processDecls :: (Diagnose :> es, ReplCtx es) => ReplEnv -> [Declaration 'Parse] -> Eff es (Maybe ReplEnv)
processDecls env@ReplEnv{loadedFiles} decls = do
    (afterNameRes, newScope) <- NameResolution.runWithEnv env.scope $ resolveNames decls
    depResOutput@SimpleOutput{fixityMap, operatorPriorities} <-
        resolveDependenciesSimplified' env.fixityMap env.operatorPriorities afterNameRes
    fixityDecls <- Fixity.resolveFixity fixityMap operatorPriorities depResOutput.declarations
    ((newEnv, constructorTable), types) <- runState env.types $ runState env.constructorTable $ TC.run env.values do
        tenv <- ask @TC.Env
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
            , loadedFiles = loadedFiles
            , input = env.input
            , inputBS = env.inputBS
            , constructorTable
            }
  where
    addDecl tcenv decl = TC.local' (const tcenv) do
        (typedDecl, envDiff) <- inferDeclaration decl
        newValues <- modifyEnv (envDiff tcenv.values) [typedDecl]
        pure tcenv{TC.values = newValues}

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
            ty <- Map.lookup id' env.types
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
