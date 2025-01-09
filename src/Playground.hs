{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-missing-export-lists #-}
{-# OPTIONS_GHC -Wno-missing-methods #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}

module Playground where

-- :load this module into a repl

import Common hiding (Scope)
import Data.Char (isUpperCase)
import Data.HashMap.Strict qualified as HashMap
import Data.HashSet qualified as HashSet
import Data.Type.Ord (type (<))
import Diagnostic (Diagnose, runDiagnose, runDiagnose')
import Effectful.Error.Static (Error)
import Effectful.Reader.Static (Reader, runReader)
import Effectful.State.Static.Local (State, runState)
import Error.Diagnose (Diagnostic)
import Fixity (resolveFixity)
import Fixity qualified (parse)
import LangPrelude
import LensyUniplate (UniplateCast (uniplateCast), cast)
import NameGen (NameGen, freshName, runNameGen)
import NameResolution (Scope (..), declare, resolveNames, resolveType, runDeclare, runNameResolution)
import NameResolution qualified (Declare)
import Parser
import Prettyprinter hiding (list)
import Prettyprinter.Render.Terminal (AnsiStyle)
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

runDefault
    :: Eff '[Declare, Reader (Builtins Name), State InfState, NameGen, Diagnose] a -> (Maybe a, Diagnostic (Doc AnsiStyle))
runDefault action = runPureEff . runDiagnose' ("<none>", "") $ runNameGen do
    (_, builtins, defaultEnv) <- mkDefaults
    run (Right <$> defaultEnv) builtins action

mkDefaults :: (NameGen :> es, Diagnose :> es) => Eff es (HashMap SimpleName_ Name, Builtins Name, HashMap Name (Type' 'Fixity))
mkDefaults = do
    let builtins = Builtins{subtypeRelations = [(noLoc NatName, noLoc IntName)]}
    types <-
        traverse (freshName . noLoc . Name') $
            HashMap.fromList $
                (\x -> (Name' x, x))
                    <$> [ "Unit"
                        , "Maybe"
                        , "Tuple"
                        ]
    let initScope =
            types
                <> HashMap.fromList
                    ( fmap
                        (bimap Name' noLoc)
                        [ ("Bool", BoolName)
                        , ("List", ListName)
                        , ("Int", IntName)
                        , ("Nat", NatName)
                        , ("Text", TextName)
                        , ("Char", CharName)
                        , ("Lens", LensName)
                        ]
                    )
    (env, Scope scope) <-
        (runState (Scope initScope) . fmap HashMap.fromList . NameResolution.runDeclare)
            ( traverse
                (\(name, ty) -> liftA2 (,) (declare $ noLoc $ Name' name) (resolveType ty))
                [ ("()", "Unit")
                , ("Nothing", T.Forall Blank "'a" $ "Maybe" $: "'a")
                , ("Just", T.Forall Blank "'a" $ "'a" --> "Maybe" $: "'a")
                , ("True", "Bool")
                , ("False", "Bool")
                , ("id", T.Forall Blank "'a" $ "'a" --> "'a")
                , ("Cons", T.Forall Blank "'a" $ "'a" --> listT "'a" --> listT "'a")
                , ("Nil", T.Forall Blank "'a" $ listT "'a")
                , ("reverse", T.Forall Blank "'a" $ listT "'a" --> listT "'a")
                ]
            )
    pure (scope, builtins, cast uniplateCast <$> env)
  where
    listT var = "List" $: var

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
        runWithFinalEnv (Right <$> env) builtins $ normalise $ infer expr

parseInfer :: Text -> IO ()
parseInfer input = void . runEff . runDiagnose ("cli", input) $ runNameGen
    case input & parse (usingReaderT pos1 code) "cli" of
        Left err -> putStrLn $ errorBundlePretty err
        Right decls -> do
            (scope, builtins, defaultEnv) <- mkDefaults
            resolvedDecls <- resolveFixity =<< runNameResolution scope (resolveNames decls)
            types <- typecheck defaultEnv builtins resolvedDecls
            liftIO $ for_ types \ty -> putDoc $ pretty ty <> line

parseInferIO :: IO ()
parseInferIO = getLine >>= parseInfer

testCheck
    :: Eff [NameResolution.Declare, State Scope, Diagnose, NameGen] resolved
    -> (resolved -> Eff '[Declare, Reader (Builtins Name), State InfState, Diagnose, NameGen] a)
    -> Maybe a
testCheck toResolve action = fst $ runPureEff $ runNameGen $ runDiagnose' ("<none>", "") do
    (scope, builtins, env) <- mkDefaults
    resolved <- runNameResolution scope toResolve
    run (Right <$> env) builtins $ action resolved

{-
dummyFixity :: Diagnose :> es => Expression 'NameRes -> Eff es (Expression 'Fixity)
dummyFixity expr = runReader testGraph $ Fixity.parse expr
-}

-- convenient definitions for testing

matchCase :: (Text -> a) -> (Text -> a) -> String -> a
matchCase whenUpper whenLower str@(h : _)
    | isUpperCase h = whenUpper $ fromString str
    | otherwise = whenLower $ fromString str

mkName :: Text -> SimpleName
mkName = noLoc . Name'

noLoc :: a -> Located a
noLoc = Located Blank

instance IsString (Expression 'Parse) where
    fromString ('\'' : rest) = rest & matchCase (E.Variant . mkName . ("'" <>)) (error $ "type variable " <> fromString rest <> " at value level")
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
nameFromText txt = noLoc $ Name txt (Id $ hashWithSalt 0 txt)

instance {-# OVERLAPPABLE #-} NameAt p ~ Name => IsString (Expression p) where
    fromString ('\'' : rest) = rest & matchCase (E.Variant . mkName . ("'" <>)) (error $ "type variable " <> fromString rest <> " at value level")
    fromString str = str & matchCase (E.Constructor . nameFromText) (E.Name . nameFromText)

instance {-# OVERLAPPABLE #-} NameAt p ~ Name => IsString (Pattern p) where
    fromString = matchCase (\txt -> P.Constructor (nameFromText txt) []) (P.Var . nameFromText)

instance {-# OVERLAPPABLE #-} NameAt p ~ Name => IsString (Type' p) where
    fromString str@('\'' : _) = T.Var $ nameFromText $ fromString str
    fromString str =
        str & matchCase (T.Name . nameFromText) (error $ "type name " <> fromString str <> " shouldn't start with a lowercase letter")

-- Type

infixr 2 -->
(-->) :: HasLoc (NameAt p) => Type' p -> Type' p -> Type' p
from --> to = T.Function (zipLocOf from to) from to

infixl 3 $:
($:) :: Type' p -> Type' p -> Type' p
($:) = T.Application

(∃) :: HasLoc (NameAt p) => NameAt p -> Type' p -> Type' p
(∃) var body = T.Exists (zipLocOf var body) var body

recordT :: ExtRow (Type' p) -> Type' p
recordT = T.Record Blank

variantT :: ExtRow (Type' p) -> Type' p
variantT = T.Variant Blank

-- Pattern

recordP :: Row (Pattern p) -> Pattern p
recordP = P.Record Blank

listP :: [Pattern p] -> Pattern p
listP = P.List Blank

con :: NameAt p -> [Pattern p] -> Pattern p
con = P.Constructor

-- Expression

infixl 1 #
(#) :: Expression p -> Expression p -> Expression p
(#) = E.Application

binApp :: Expression 'Parse -> Expression 'Parse -> Expression 'Parse -> Expression 'Parse
binApp f arg1 arg2 = f # arg1 # arg2

λ :: HasLoc (NameAt p) => Pattern p -> Expression p -> Expression p
λ pat expr = E.Lambda (zipLocOf pat expr) pat expr

lam :: HasLoc (NameAt p) => Pattern p -> Expression p -> Expression p
lam = λ

let_ :: HasLoc (NameAt p) => Binding p -> Expression p -> Expression p
let_ binding body = E.Let (zipLocOf binding body) binding body

recordExpr :: Row (Expression p) -> Expression p
recordExpr = E.Record Blank

list :: HasLoc (NameAt p) => [Expression p] -> Expression p
list xs = E.List loc xs
  where
    loc = case (xs, reverse xs) of
        (first' : _, last' : _) -> zipLocOf first' last'
        _ -> Blank

match :: [([Pattern p], Expression p)] -> Expression p
match = E.Match Blank

case_ :: Expression p -> [(Pattern p, Expression p)] -> Expression p
case_ = E.Case Blank

if_ :: Expression p -> Expression p -> Expression p -> Expression p
if_ = E.If Blank

-- Declaration

valueDec :: HasLoc (NameAt p) => Binding p -> [Declaration p] -> Declaration p
valueDec binding decls = D.Value loc binding decls
  where
    loc = case reverse decls of
        [] -> getLoc binding
        (lastDecl : _) -> zipLocOf binding lastDecl

typeDec :: HasLoc (NameAt p) => NameAt p -> [NameAt p] -> [D.Constructor p] -> Declaration p
typeDec typeName vars constrs = D.Type loc typeName vars constrs
  where
    loc = case (reverse vars, reverse constrs) of
        ([], []) -> getLoc typeName
        (x : _, []) -> zipLocOf typeName x
        (_, x : _) -> zipLocOf typeName x

sigDec :: (HasLoc (NameAt p), p < DependencyRes) => NameAt p -> Type' p -> Declaration p
sigDec name ty = D.Signature (zipLocOf name ty) name ty

conDec :: HasLoc (NameAt p) => NameAt p -> [Type' p] -> D.Constructor p
conDec name args = D.Constructor loc name args
  where
    loc = case reverse args of
        [] -> getLoc name
        (last' : _) -> zipLocOf name last'

intLit :: Int -> Literal
intLit = noLoc . IntLiteral
textLit :: Text -> Literal
textLit = noLoc . TextLiteral
charLit :: Text -> Literal
charLit = noLoc . CharLiteral
