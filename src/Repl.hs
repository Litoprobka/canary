{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE RecordWildCards #-}

module Repl where

import Common (Fixity (..), Loc (..), Name, Name_ (TypeName), Pass (..), SimpleName_ (Name'), cast, noLoc)
import Common qualified as C
import Control.Monad.Combinators (choice)
import Data.EnumMap.Lazy qualified as LMap
import Data.EnumMap.Strict qualified as Map
import Data.HashMap.Strict qualified as HashMap
import Data.Text qualified as Text
import Data.Text.Encoding (strictBuilderToText, textToStrictBuilder)
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
import TypeChecker.Backend qualified as TC

data ReplCommand
    = Decls [Declaration 'Parse]
    | Expr (Expr 'Parse)
    | Type_ (Expr 'Parse)
    | Load FilePath
    | Env
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
    values = ValueEnv{values = LMap.singleton (noLoc TypeName) (V.TyCon (noLoc TypeName)), skolems = Map.empty}
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
            }
  where
    addDecl env decl = TC.local' (const env) do
        envDiff <- inferDeclaration decl
        newValues <- modifyEnv (envDiff env.values) [decl]
        pure env{TC.values = newValues}

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
            (checkedExpr, _) <- runReader @"values" env.values $ processExpr env.types expr
            guardNoErrors
            print . pretty =<< eval env.values checkedExpr
            pure $ Just env
        Type_ expr -> do
            (_, ty) <- runReader @"values" env.values $ processExpr env.types expr
            print ty
            pure $ Just env
        Load path -> do
            fileContents <- reportExceptions @SomeException (decodeUtf8 <$> readFileBS path)
            localDiagnose env (path, fileContents) do
                decls <- Parser.parseModule (path, fileContents)
                processDecls env decls
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
    (newEnv, types) <- runState emptyEnv.types $ TC.run emptyEnv.values do
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
            }
  where
    addDecl tenv decl = TC.local' (const tenv) do
        envDiff <- inferDeclaration decl
        newValues <- modifyEnv (envDiff tenv.values) [decl]
        pure tenv{TC.values = newValues}

{-
(env, types) <- runState emptyEnv.types $ TC.run emptyEnv.values \env -> do
        foldlM addDecl env fixityDecls
    guardNoErrors
    pure $
        ReplEnv
            { values = env.values
            , fixityMap
            , operatorPriorities
            , scope = newScope
            , types
            }
-}

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
        , keyword ":env" $> Env
        , symbol ":" *> (UnknownCommand <$> takeRest)
        , try $ fmap Decls Parser.code
        , fmap Expr Parser.term
        ]
