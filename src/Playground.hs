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
import Syntax.Term (Pattern_ (..), Quantifier (..), Erased (..), Visibility (..))
import Syntax.Term qualified as E
import Syntax.Term qualified as T
import Text.Megaparsec (errorBundlePretty, parse, pos1)
import TypeChecker
import TypeChecker.Backend (Type', TopLevel)
import qualified Data.EnumMap.Lazy as LMap
import qualified Data.EnumMap as Map
import qualified Repl
import Repl (ReplEnv(..))

-- some wrappers and syntactic niceties for testing

testCheck
    :: Eff [NameResolution.Declare, State Scope, Diagnose, NameGen] resolved
    -> (resolved -> Eff '[Declare, State InfState, State TopLevel, Diagnose, NameGen] a)
    -> Maybe a
testCheck toResolve action = fst $ runPureEff $ runNameGen $ runDiagnose' ("<none>", "") do
    ReplEnv{scope, types} <- Repl.mkDefaultEnv
    resolved <- NameResolution.run scope toResolve
    evalState types $ run $ action resolved

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

instance IsString (Pattern 'Parse) where
    fromString = noLoc . matchCase (\name -> ConstructorP (mkName name) []) (VarP . mkName)

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
    fromString = noLoc . matchCase (\txt -> ConstructorP (nameFromText txt) []) (VarP . nameFromText)

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
(∃) var body = Located (zipLocOf var body) $ T.Q Exists Implicit Erased (T.plainBinder var) body

recordT :: ExtRow (Type p) -> Type p
recordT = noLoc . T.RecordT

variantT :: ExtRow (Type p) -> Type p
variantT = noLoc . T.VariantT

-- Pattern

recordP :: Row (Pattern p) -> Pattern p
recordP = noLoc . RecordP

listP :: [Pattern p] -> Pattern p
listP = noLoc . ListP

con :: NameAt p -> [Pattern p] -> Pattern p
con name = noLoc . ConstructorP name

-- Expression

infixl 1 #
(#) :: Expr p -> Expr p -> Expr p
(#) = ($:)

binApp :: Expr 'Parse -> Expr 'Parse -> Expr 'Parse -> Expr 'Parse
binApp f arg1 arg2 = f # arg1 # arg2

λ :: Pattern p -> Expr p -> Expr p
λ pat expr = Located (zipLocOf pat expr) $ E.Lambda pat expr

lam :: Pattern p -> Expr p -> Expr p
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
