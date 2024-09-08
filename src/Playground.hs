{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-missing-methods #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
{-# OPTIONS_GHC -Wno-missing-export-lists #-}

module Playground where

-- :load this module into a repl

import Relude

import CheckerTypes
import Data.Char (isUpperCase)
import Prettyprinter hiding (list)
import TypeChecker
import Syntax hiding (Name)
import Syntax.Expression qualified as E
import Syntax.Pattern qualified as P
import Syntax.Type qualified as T
import Syntax.Row
import Parser
import Text.Megaparsec (errorBundlePretty, pos1, parse)
import Prettyprinter.Render.Text (putDoc)
import qualified Data.HashMap.Strict as HashMap

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

runDefault :: InfMonad a -> Either TypeError a
runDefault = run defaultEnv

defaultEnv :: HashMap Name (Type' Name)
defaultEnv =
    HashMap.fromList
        [ ("()", "Unit")
        , ("Nothing", T.Forall "'a" $ "Maybe" $: "'a")
        , ("Just", T.Forall "'a" $ "'a" --> "Maybe" $: "'a")
        , ("True", "Bool")
        , ("False", "Bool")
        , ("id", T.Forall "'a" $ "'a" --> "'a")
        , ("cons", T.Forall "'a" $ "'a" --> list "'a" --> list "'a")
        , ("reverse", T.Forall "'a" $ list "'a" --> list "'a")
        ]
  where
    list var = T.Name (Name "List" 0) `T.Application` var

inferIO :: Expression Name -> IO ()
inferIO = inferIO' defaultEnv

inferIO' :: HashMap Name (Type' Name) -> Expression Name -> IO ()
inferIO' env expr = case run env $ fmap pretty . normalise =<< infer expr of
    Left (TypeError err) -> putDoc $ err <> line
    Right txt -> putDoc $ txt <> line

parseInfer :: Text -> IO ()
parseInfer input = do
    case input & parse (usingReaderT pos1 expression) "cli" of
        Left err -> putStrLn $ errorBundlePretty err
        Right expr -> inferIO $ (`Name` 0) <$> expr

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
    fromString ('\'' : str) = T.Var $ fromString str -- I'm not sure whether the quote should be a part of a type var
    fromString str = str & matchCase T.Name (error $ "type name " <> fromString str <> " shouldn't start with a lowercase letter")

instance IsString Name where
    fromString ('\'' : rest) = flip Name 0 $ fromString rest
    fromString str = Name (fromString str) 0

instance IsString (Expression Name) where
    fromString ('\'' : rest) = rest & matchCase (E.Variant . ("'" <>)) (error $ "type variable " <> fromString rest <> " at value level")
    fromString str = str & matchCase (E.Constructor . flip Name 0) (E.Name . flip Name 0)

instance IsString (Pattern Name) where
    fromString = matchCase (flip P.Constructor [] . flip Name 0) (P.Var . flip Name 0)

instance IsString (Type' Name) where
    fromString ('\'' : str) = T.Var . flip Name 0 $ fromString str
    fromString str = str & matchCase (T.Name . flip Name 0) (error $ "type name " <> fromString str <> " shouldn't start with a lowercase letter")