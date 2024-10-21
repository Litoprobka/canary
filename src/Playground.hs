{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-missing-export-lists #-}
{-# OPTIONS_GHC -Wno-missing-methods #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}

module Playground where

-- :load this module into a repl

import Relude hiding (Reader, State, bool, runState)

import Common hiding (Scope)
import Data.Char (isUpperCase)
import Data.HashMap.Strict qualified as HashMap
import Data.HashSet qualified as HashSet
import Effectful
import Effectful.Error.Static (Error)
import Effectful.Reader.Static (Reader)
import Effectful.State.Static.Local (State, runState)
import NameGen (NameGen, freshName, runNameGen)
import NameResolution (Scope (..), declare, resolveNames, resolveType, runDeclare, runNameResolution)
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
import Diagnostic (runDiagnose, Diagnose, runDiagnose')
import Error.Diagnose (Diagnostic)
import Prettyprinter.Render.Terminal (AnsiStyle)
import Fixity (resolveFixity, testGraph, testOpMap)

-- a lot of what is used here is only reasonable for interactive use

infixr 2 -->
(-->) :: Type' p -> Type' p -> Type' p
(-->) = T.Function Blank

infixl 1 #
(#) :: Expression p -> Expression p -> Expression p
(#) = E.Application

binApp :: Expression 'Parse -> Expression 'Parse -> Expression 'Parse -> Expression 'Parse
binApp f arg1 arg2 = f # arg1 # arg2

infixl 3 $:
($:) :: Type' p -> Type' p -> Type' p
($:) = T.Application

λ :: Pattern p -> Expression p -> Expression p
λ = E.Lambda Blank

lam :: Pattern p -> Expression p -> Expression p
lam = E.Lambda Blank

(∃) :: NameAt p -> Type' p -> Type' p
(∃) = T.Exists Blank

con :: NameAt p -> [Pattern p] -> Pattern p
con = P.Constructor

runDefault :: Eff '[Declare, Reader (Builtins Name), State InfState, NameGen, Diagnose] a -> (Maybe a, Diagnostic (Doc AnsiStyle))
runDefault action = runPureEff . runDiagnose' ("<none>", "") $ runNameGen do
    (_, builtins, defaultEnv) <- mkDefaults
    run (Right <$> defaultEnv) builtins action

mkDefaults :: (NameGen :> es, Diagnose :> es) => Eff es (HashMap Text Name, Builtins Name, HashMap Name (Type' 'Fixity))
mkDefaults = do
    let builtins = Builtins{subtypeRelations = [(NatName Blank, IntName Blank)]}
    types <-
        traverse (freshName Blank) $
            HashMap.fromList $
                (\x -> (x, x))
                    <$> [ "Unit"
                        , "Maybe"
                        , "Tuple"
                        ]
    let initScope =
            types
                <> HashMap.fromList
                    [ ("Bool", BoolName Blank)
                    , ("List", ListName Blank)
                    , ("Int", IntName Blank)
                    , ("Nat", NatName Blank)
                    , ("Text", TextName Blank)
                    , ("Char", CharName Blank)
                    , ("Lens", LensName Blank)
                    ]
    (env, Scope scope) <-
        (runState (Scope initScope) . fmap HashMap.fromList . NameResolution.runDeclare)
            ( traverse
                (\(name, ty) -> liftA2 (,) (declare $ SimpleName Blank name) (resolveType ty))
                [ ("()", "Unit")
                , ("Nothing", T.Forall Blank "'a" $ "Maybe" $: "'a")
                , ("Just", T.Forall Blank "'a" $ "'a" --> "Maybe" $: "'a")
                , ("True", "Bool")
                , ("False", "Bool")
                , ("id", T.Forall Blank "'a" $ "'a" --> "'a")
                , ("Cons", T.Forall Blank "'a" $ "'a" --> list "'a" --> list "'a")
                , ("Nil", T.Forall Blank "'a" $ list "'a")
                , ("reverse", T.Forall Blank "'a" $ list "'a" --> list "'a")
                ]
            )
    pure (scope, builtins, T.cast id <$> env)
  where
    list var = "List" $: var

inferIO :: Expression 'Fixity -> IO ()
inferIO = inferIO' do
    (_, builtins, env) <- mkDefaults
    pure (env, builtins)

inferIO' :: Eff '[NameGen, Diagnose, IOE] (HashMap Name (Type' 'Fixity), Builtins Name) -> Expression 'Fixity -> IO ()
inferIO' mkEnv expr = do
    getTy >>= \case
        Nothing -> pass
        Just (ty, finalEnv) -> do
            putDoc $ pretty ty <> line
            for_ (HashMap.toList finalEnv.vars) \case
                (name, Left _) -> putDoc $ pretty name <> line
                (name, Right ty') -> putDoc $ pretty name <> ":" <+> pretty ty' <> line
  where
    getTy = runEff $ runDiagnose ("<none>", "") $ runNameGen do
        (env, builtins) <- mkEnv
        runWithFinalEnv (Right <$> env) builtins $ normalise =<< infer expr

parseInfer :: Text -> IO ()
parseInfer input = void . runEff . runDiagnose ("cli", input) $ runNameGen
    case input & parse (usingReaderT pos1 code) "cli" of
        Left err -> putStrLn $ errorBundlePretty err
        Right decls -> do
            (scope, builtins, defaultEnv) <- mkDefaults
            resolvedDecls <- resolveFixity testOpMap testGraph =<< runNameResolution scope (resolveNames decls)
            types <- typecheck defaultEnv builtins resolvedDecls
            liftIO $ for_ types \ty -> putDoc $ pretty ty <> line

parseInferIO :: IO ()
parseInferIO = getLine >>= parseInfer

matchCase :: (Text -> a) -> (Text -> a) -> String -> a
matchCase whenUpper whenLower str@(h : _)
    | isUpperCase h = whenUpper $ fromString str
    | otherwise = whenLower $ fromString str

mkName :: Text -> SimpleName
mkName = SimpleName Blank

instance IsString (Expression 'Parse) where
    fromString ('\'' : rest) = rest & matchCase (E.Variant . SimpleName Blank . ("'" <>)) (error $ "type variable " <> fromString rest <> " at value level")
    fromString str = str & matchCase (E.Constructor . mkName) (E.Name . mkName)

instance IsString (Pattern 'Parse) where
    fromString = matchCase (\name -> P.Constructor (mkName name) []) (P.Var . mkName)

instance IsString (Type' 'Parse) where
    fromString str@('\'' : _) = T.Var . mkName $ fromString str
    fromString str = str & matchCase (T.Name . mkName) (error $ "type name " <> fromString str <> " shouldn't start with a lowercase letter")

instance IsString SimpleName where
    fromString = mkName . fromString

instance IsString Name where
    fromString = nameFromText . fromString

nameFromText :: Text -> Name
nameFromText txt = Name Blank txt (Id $ hashWithSalt 0 txt)

instance {-# OVERLAPPABLE #-} NameAt p ~ Name => IsString (Expression p) where
    fromString ('\'' : rest) = rest & matchCase (E.Variant . SimpleName Blank . ("'" <>)) (error $ "type variable " <> fromString rest <> " at value level")
    fromString str = str & matchCase (E.Constructor . nameFromText) (E.Name . nameFromText)

instance {-# OVERLAPPABLE #-} NameAt p ~ Name => IsString (Pattern p) where
    fromString = matchCase (\txt -> P.Constructor (nameFromText txt) []) (P.Var . nameFromText)

instance {-# OVERLAPPABLE #-} NameAt p ~ Name => IsString (Type' p) where
    fromString str@('\'' : _) = T.Var $ nameFromText $ fromString str
    fromString str =
        str & matchCase (T.Name . nameFromText) (error $ "type name " <> fromString str <> " shouldn't start with a lowercase letter")
