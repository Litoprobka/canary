{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-missing-export-lists #-}
{-# OPTIONS_GHC -Wno-missing-methods #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}

module Playground where

-- :load this module into a repl

import Relude hiding (Reader, State, bool)

import CheckerTypes
import Data.Char (isUpperCase)
import Data.HashMap.Strict qualified as HashMap
import Effectful
import Effectful.Error.Static (Error)
import Effectful.Reader.Static (Reader)
import Effectful.State.Static.Local (State)
import NameGen (NameGen, freshName, runNameGen)
import NameResolution (resolveNames)
import Parser
import Prettyprinter hiding (list)
import Prettyprinter.Render.Text (putDoc)
import Syntax
import Syntax.Declaration qualified as D
import Syntax.Expression qualified as E
import Syntax.Pattern qualified as P
import Syntax.Row
import Syntax.Type qualified as T
import Text.Megaparsec (errorBundlePretty, parse, pos1)
import TypeChecker

-- a lot of what is used here is only reasonable for interactive use

infixr 2 -->
(-->) :: Type' n -> Type' n -> Type' n
(-->) = T.Function

infixl 1 #
(#) :: Expression n -> Expression n -> Expression n
(#) = E.Application

binApp :: Expression Text -> Expression Text -> Expression Text -> Expression Text
binApp f arg1 arg2 = f # arg1 # arg2

infixl 3 $:
($:) :: Type' n -> Type' n -> Type' n
($:) = T.Application

λ :: Pattern n -> Expression n -> Expression n
λ = E.Lambda

lam :: Pattern n -> Expression n -> Expression n
lam = E.Lambda

(∃) :: n -> Type' n -> Type' n
(∃) = T.Exists

con :: n -> [Pattern n] -> Pattern n
con = P.Constructor

runDefault :: Eff '[Error TypeError, Reader (Builtins Name), State InfState, NameGen] a -> Either TypeError a
runDefault action = runPureEff $ runNameGen do
    (scope, builtins) <- mkDefaultScope
    defaultEnv <- mkDefaultEnv scope
    run defaultEnv builtins action

mkDefaultScope :: NameGen :> es => Eff es (HashMap Text Name, Builtins Name)
mkDefaultScope = do
    builtins <-
        traverse
            freshName
            Builtins
                { bool = "Bool"
                , list = "List"
                , int = "Int"
                , nat = "Nat"
                , text = "Text"
                , char = "Char"
                , lens = "Lens"
                , subtypeRelations = [("Nat", "Int")]
                }
    scope <-
        traverse freshName $
            HashMap.fromList $
                (\x -> (x, x))
                    <$> [ "Unit"
                        , "Maybe"
                        -- "List"
                        -- "Bool"
                        , "()"
                        , "Nothing"
                        , "Just"
                        , "True"
                        , "False"
                        , "id"
                        , "cons"
                        , "reverse"
                        ]

    pure (HashMap.insert "List" builtins.list $ HashMap.insert "Bool" builtins.bool scope, builtins)

mkDefaultEnv :: NameGen :> es => HashMap Text Name -> Eff es (HashMap Name (Type' Name))
mkDefaultEnv scope =
    HashMap.fromList . mapMaybe sig . fst
        <$> resolveNames
            scope
            ( fmap
                (uncurry D.Signature)
                [ ("()", "Unit")
                , ("Nothing", T.Forall "'a" $ "Maybe" $: "'a")
                , ("Just", T.Forall "'a" $ "'a" --> "Maybe" $: "'a")
                , ("True", "Bool")
                , ("False", "Bool")
                , ("id", T.Forall "'a" $ "'a" --> "'a")
                , ("cons", T.Forall "'a" $ "'a" --> list "'a" --> list "'a")
                , ("reverse", T.Forall "'a" $ list "'a" --> list "'a")
                ]
            )
  where
    list var = "List" $: var
    sig (D.Signature name ty) = Just (name, ty)
    sig _ = Nothing

inferIO :: Expression Name -> IO ()
inferIO = inferIO' do
    (scope, builtins) <- mkDefaultScope
    env <- mkDefaultEnv scope
    pure (env, builtins)

inferIO' :: Eff '[NameGen] (HashMap Name (Type' Name), Builtins Name) -> Expression Name -> IO ()
inferIO' mkEnv expr = case typeOrError of
    Left (TypeError err) -> putDoc $ err <> line
    Right ty -> putDoc $ pretty ty <> line
  where
    typeOrError = runPureEff $ runNameGen do
        (env, builtins) <- mkEnv
        run env builtins $ normalise =<< infer expr

parseInfer :: Text -> IO ()
parseInfer input = runEff $ runNameGen
    case input & parse (usingReaderT pos1 code) "cli" of
        Left err -> putStrLn $ errorBundlePretty err
        Right decls -> do
            (scope, builtins) <- mkDefaultScope
            defaultEnv <- mkDefaultEnv scope
            resolvedDecls <- fst <$> resolveNames scope decls
            typesOrErrors <- typecheck defaultEnv builtins resolvedDecls
            case typesOrErrors of
                Left (TypeError err) -> liftIO $ putDoc $ err <> line
                Right types -> liftIO $ for_ types \ty -> putDoc $ pretty ty <> line

parseInferIO :: IO ()
parseInferIO = getLine >>= parseInfer

matchCase :: (Text -> a) -> (Text -> a) -> String -> a
matchCase whenUpper whenLower str@(h : _)
    | isUpperCase h = whenUpper $ fromString str
    | otherwise = whenLower $ fromString str

instance IsString (Expression Text) where
    fromString ('\'' : rest) = rest & matchCase (E.Variant . ("'" <>)) (error $ "type variable " <> fromString rest <> " at value level")
    fromString str = str & matchCase E.Constructor E.Name

instance IsString (Pattern Text) where
    fromString = matchCase (`P.Constructor` []) P.Var

instance IsString (Type' Text) where
    fromString ('\'' : str) = T.Var $ ("'" <>) $ fromString str
    fromString str = str & matchCase T.Name (error $ "type name " <> fromString str <> " shouldn't start with a lowercase letter")
