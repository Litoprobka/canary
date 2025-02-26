{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE UndecidableInstances #-}
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
import DependencyResolution (SimpleOutput (..), resolveDependenciesSimplified)
import Diagnostic (Diagnose, runDiagnose, runDiagnose')
import Effectful.Error.Static (Error)
import Effectful.Reader.Static (Reader, runReader)
import Effectful.State.Static.Local (State, evalState, execState, runState)
import Error.Diagnose (Diagnostic)
import Fixity (resolveFixity)
import Fixity qualified (parse)
import Interpreter (ValueEnv)
import LangPrelude
import LensyUniplate (unicast)
import NameGen (NameGen, freshName, runNameGen)
import NameResolution (Scope (..), declare, resolveNames, resolveTerm, runDeclare)
import NameResolution qualified (Declare, run)
import Parser hiding (run)
import Prettyprinter hiding (list)
import Prettyprinter.Render.Terminal (AnsiStyle)
import Prettyprinter.Render.Text (putDoc)
import Syntax
import Syntax.Declaration qualified as D
import Syntax.Row
import Syntax.Term (Pattern (..))
import Syntax.Term qualified as E
import Syntax.Term qualified as T
import Text.Megaparsec (errorBundlePretty, parse, pos1)
import TypeChecker
import TypeChecker.Backend (Type')

-- a lot of what is used here is only reasonable for interactive use

runDefault
    :: Eff '[Declare, State InfState, NameGen, Diagnose] a -> (Maybe a, Diagnostic (Doc AnsiStyle))
runDefault action = runPureEff . runDiagnose' ("<none>", "") $ runNameGen do
    (_, defaultEnv) <- mkDefaults
    run defaultEnv action

mkDefaults :: NameGen :> es => Eff es (Scope, HashMap Name Type')
mkDefaults = do
    types <-
        traverse (freshName . noLoc . Name') $
            HashMap.fromList $
                (\x -> (Name' x, x))
                    <$> [ "Unit"
                        , "Maybe"
                        , "Tuple"
                        ]
    let scope =
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
                        , ("Type", TypeName)
                        ]
                    )
    -- this is a messy way to declare built-in stuff, I should do better
    {-scope <-
        (execState (Scope initScope) . fmap HashMap.fromList . NameResolution.runDeclare)
            ( traverse
                (\(name, ty) -> liftA2 (,) (declare $ noLoc $ Name' name) (resolveTerm ty))
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
            )-}
    pure (Scope scope, HashMap.empty)

-- where
-- listT var = "List" $: var

inferIO :: Expr 'Fixity -> IO ()
inferIO = inferIO' $ snd <$> mkDefaults

inferIO' :: Eff '[NameGen, Diagnose, IOE] (HashMap Name Type') -> Expr 'Fixity -> IO ()
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
        env <- mkEnv
        evalState @ValueEnv HashMap.empty $ runWithFinalEnv env $ normalise $ infer expr

parseInfer :: Text -> IO ()
parseInfer input = void . runEff . runDiagnose ("cli", input) $ runNameGen
    case input & parse (usingReaderT pos1 code) "cli" of
        Left err -> putStrLn $ errorBundlePretty err
        Right decls -> do
            (scope, defaultEnv) <- mkDefaults
            nameResolved <- NameResolution.run scope (resolveNames decls)
            SimpleOutput{fixityMap, operatorPriorities, declarations} <- resolveDependenciesSimplified nameResolved
            resolvedDecls <- resolveFixity fixityMap operatorPriorities declarations
            types <- evalState @ValueEnv HashMap.empty $ typecheck defaultEnv resolvedDecls
            liftIO $ for_ types \ty -> putDoc $ pretty ty <> line

parseInferIO :: IO ()
parseInferIO = getLine >>= parseInfer

testCheck
    :: Eff [NameResolution.Declare, State Scope, Diagnose, NameGen] resolved
    -> (resolved -> Eff '[Declare, State InfState, Diagnose, NameGen] a)
    -> Maybe a
testCheck toResolve action = fst $ runPureEff $ runNameGen $ runDiagnose' ("<none>", "") do
    (scope, env) <- mkDefaults
    resolved <- NameResolution.run scope toResolve
    run env $ action resolved

{-
dummyFixity :: Diagnose :> es => Expr 'NameRes -> Eff es (Expr 'Fixity)
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

instance IsString (Pattern 'Parse) where
    fromString = matchCase (\name -> ConstructorP (mkName name) []) (VarP . mkName)

instance IsString (Term 'Parse) where
    fromString ('\'' : rest) = rest & matchCase (noLoc . E.Variant . mkName . ("'" <>)) (noLoc . T.Name . mkName . ("'" <>))
    fromString str = noLoc . E.Name . mkName $ fromString str

instance IsString SimpleName where
    fromString = mkName . fromString

instance IsString Name where
    fromString = nameFromText . fromString

nameFromText :: Text -> Name
nameFromText txt = noLoc $ Name txt (Id $ hashWithSalt 0 txt)

instance {-# OVERLAPPABLE #-} NameAt p ~ Name => IsString (Pattern p) where
    fromString = matchCase (\txt -> ConstructorP (nameFromText txt) []) (VarP . nameFromText)

instance {-# OVERLAPPABLE #-} NameAt p ~ Name => IsString (Term p) where
    fromString ('\'' : rest) = rest & noLoc . matchCase (E.Variant . mkName . ("'" <>)) (T.Name . nameFromText . ("'" <>))
    fromString str = noLoc . E.Name . nameFromText $ fromString str

instance {-# OVERLAPPABLE #-} (NameAt p ~ name, IsString name) => IsString (VarBinder p) where
    fromString = T.plainBinder . fromString @name

-- Type

infixr 2 -->
(-->) :: Type p -> Type p -> Type p
from --> to = Located (zipLocOf from to) $ T.Function from to

infixl 3 $:
($:) :: Type p -> Type p -> Type p
($:) lhs = noLoc . T.App lhs

(∃) :: HasLoc (NameAt p) => NameAt p -> Type p -> Type p
(∃) var body = Located (zipLocOf var body) $ T.Exists (T.plainBinder var) body

recordT :: ExtRow (Type p) -> Type p
recordT = noLoc . T.RecordT

variantT :: ExtRow (Type p) -> Type p
variantT = noLoc . T.VariantT

-- Pattern

recordP :: Row (Pattern p) -> Pattern p
recordP = RecordP Blank

listP :: [Pattern p] -> Pattern p
listP = ListP Blank

con :: NameAt p -> [Pattern p] -> Pattern p
con = ConstructorP

-- Expression

infixl 1 #
(#) :: Expr p -> Expr p -> Expr p
(#) = ($:)

binApp :: Expr 'Parse -> Expr 'Parse -> Expr 'Parse -> Expr 'Parse
binApp f arg1 arg2 = f # arg1 # arg2

λ :: HasLoc (NameAt p) => Pattern p -> Expr p -> Expr p
λ pat expr = Located (zipLocOf pat expr) $ E.Lambda pat expr

lam :: HasLoc (NameAt p) => Pattern p -> Expr p -> Expr p
lam = λ

let_ :: HasLoc (NameAt p) => Binding p -> Expr p -> Expr p
let_ binding body = Located (zipLocOf binding body) $ E.Let binding body

recordExpr :: Row (Expr p) -> Expr p
recordExpr = noLoc . E.Record

list :: [Expr p] -> Expr p
list xs = Located loc $ E.List xs
  where
    loc = case (xs, reverse xs) of
        (first' : _, last' : _) -> zipLocOf first' last'
        _ -> Blank

match :: [([Pattern p], Expr p)] -> Expr p
match = noLoc . E.Match

case_ :: Expr p -> [(Pattern p, Expr p)] -> Expr p
case_ m = noLoc . E.Case m

if_ :: Expr p -> Expr p -> Expr p -> Expr p
if_ c t = noLoc . E.If c t

-- Declaration

valueDec :: HasLoc (NameAt p) => Binding p -> [Declaration p] -> Declaration p
valueDec binding decls = Located loc $ D.Value binding decls
  where
    loc = case reverse decls of
        [] -> getLoc binding
        (lastDecl : _) -> zipLocOf binding lastDecl

typeDec :: HasLoc (NameAt p) => NameAt p -> [NameAt p] -> [D.Constructor p] -> Declaration p
typeDec typeName vars constrs = Located loc $ D.Type typeName (map T.plainBinder vars) constrs
  where
    loc = case (reverse vars, reverse constrs) of
        ([], []) -> getLoc typeName
        (x : _, []) -> zipLocOf typeName x
        (_, x : _) -> zipLocOf typeName x

sigDec :: HasLoc (NameAt p) => NameAt p -> Type p -> Declaration p
sigDec name ty = Located (zipLocOf name ty) $ D.Signature name ty

conDec :: HasLoc (NameAt p) => NameAt p -> [Type p] -> D.Constructor p
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
