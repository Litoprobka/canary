{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-missing-export-lists #-}
{-# OPTIONS_GHC -Wno-missing-methods #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
{-# LANGUAGE LambdaCase #-}

module Playground where

-- :load this module into a repl

import Relude hiding (Reader, State, bool, runState)

import CheckerTypes hiding (Scope)
import Data.Char (isUpperCase)
import Data.HashMap.Strict qualified as HashMap
import Effectful
import Effectful.Error.Static (Error)
import Effectful.Reader.Static (Reader)
import Effectful.State.Static.Local (State, runState)
import NameGen (NameGen, freshName, runNameGen)
import NameResolution (declare, resolveNames, resolveType, runNameResolution, Scope (..), runScopeErrors)
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
    (_, builtins, defaultEnv) <- mkDefaults
    run defaultEnv builtins action

mkDefaults :: NameGen :> es => Eff es (HashMap Text Name, Builtins Name, HashMap Name (Type' Name))
mkDefaults = do
    let builtins = Builtins { subtypeRelations = [(NatName, IntName)]}
    types <-
        traverse freshName $
            HashMap.fromList $
                (\x -> (x, x))
                    <$> [ "Unit"
                        , "Maybe"
                        ]
    let initScope = types <> HashMap.fromList
            [ ("Bool", BoolName)
            , ("List", ListName)
            , ("Int", IntName)
            , ("Nat", NatName)
            , ("Text", TextName)
            , ("Char", CharName)
            , ("Lens", LensName)
            ]
    (env, Scope scope) <-
        (runState (Scope initScope) . fmap (HashMap.fromList . fst) . runScopeErrors)
            ( traverse
                (\(name, ty) -> liftA2 (,) (declare name) (resolveType ty))
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
    pure (scope, builtins, env)
  where
    list var = "List" $: var

inferIO :: Expression Name -> IO ()
inferIO = inferIO' do
    (_, builtins, env) <- mkDefaults
    pure (env, builtins)

inferIO' :: Eff '[NameGen] (HashMap Name (Type' Name), Builtins Name) -> Expression Name -> IO ()
inferIO' mkEnv expr = do
    case typeOrError of
        Left (TypeError err) -> putDoc $ err <> line
        Right ty -> putDoc $ pretty ty <> line
    for_ (HashMap.toList finalEnv.vars) \case
        (name, Left _) -> putDoc $ pretty name <> line
        (name, Right ty) -> putDoc $ pretty name <> ":" <+> pretty ty <> line
  where
    (typeOrError, finalEnv) = runPureEff $ runNameGen do
        (env, builtins) <- mkEnv
        runWithFinalEnv env builtins $ normalise =<< infer expr

parseInfer :: Text -> IO ()
parseInfer input = runEff $ runNameGen
    case input & parse (usingReaderT pos1 code) "cli" of
        Left err -> putStrLn $ errorBundlePretty err
        Right decls -> do
            (scope, builtins, defaultEnv) <- mkDefaults
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
    fromString str@('\'' : _) = T.Var $ fromString str
    fromString str = str & matchCase T.Name (error $ "type name " <> fromString str <> " shouldn't start with a lowercase letter")

instance IsString Name where
    fromString = nameFromText . fromString

nameFromText :: Text -> Name
nameFromText txt = Name txt (Id $ hashWithSalt 0 txt)

instance IsString (Expression Name) where
    fromString ('\'' : rest) = rest & matchCase (E.Variant . ("'" <>)) (error $ "type variable " <> fromString rest <> " at value level")
    fromString str = str & matchCase (E.Constructor . nameFromText) (E.Name . nameFromText)

instance IsString (Pattern Name) where
    fromString = matchCase (\txt -> nameFromText txt `P.Constructor` []) (P.Var . nameFromText)

instance IsString (Type' Name) where
    fromString str@('\'' : _) = T.Var $ nameFromText $ fromString str
    fromString str = str & matchCase (T.Name . nameFromText) (error $ "type name " <> fromString str <> " shouldn't start with a lowercase letter")
