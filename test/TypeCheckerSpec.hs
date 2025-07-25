{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}

module TypeCheckerSpec (spec) where

import Common
import Data.Text qualified as Text
import DependencyResolution (SimpleOutput (..), cast, resolveDependenciesSimplified')
import Diagnostic (Diagnose, ShowDiagnostic (..), runDiagnose')
import Effectful (Eff, runPureEff)
import Eval (modifyEnv)
import Fixity qualified
import FlatParse.Stateful qualified as FP
import Lexer (lex', mkTokenStream)
import NameGen
import NameResolution
import NameResolution qualified as NameRes
import Parser
import Prettyprinter hiding (list)
import Proto (eof, parse)
import Relude hiding (State)
import Repl qualified
import Syntax
import Syntax.AstTraversal
import Syntax.Elaborated qualified as E
import Syntax.Term qualified as T
import Test.Hspec
import TypeChecker qualified as TC
import TypeChecker.Backend qualified as TC

toSanityCheck :: [Text]
toSanityCheck =
    [ "\\x -> x"
    , "\\f x -> f x"
    , "\\x f -> f x"
    , "\\x f -> f (f x)"
    , "\\f x -> f x x"
    , "\\x _ -> x"
    , "\\f g x -> f (g x)"
    , "match x _ -> x"
    , "match Int -> True; _ -> False"
    ]

-- these cases do not seem to work with pattern unification.
-- generally, it fails on non-variables in meta spines. That could be worked around by postponing and aggerssively pruning later on
unificationShenanigans :: [Text]
unificationShenanigans =
    [ "\\x y -> x (\\a -> x (y a a))"
    , "\\a b c -> c (b a) (c a a)"
    , "\\a b -> a (\\x -> b x) (\\z -> a b b) {}"
    ]

toTypecheck :: [(Text, Text)]
toTypecheck =
    [ ("map", "map f xs = case xs of Nil -> Nil; Cons x xs -> Cons (f x) (map f xs)")
    , ("len", "type Peano = S Peano | Z\nlen xs = case xs of Nil -> Z; Cons _ xs -> S (len xs)")
    ]

spec :: Spec
spec = do
    describe "sanity check" do
        for_ toSanityCheck \input -> it ("infers a consistent type for " <> toString input) $ sanityCheck input
    describe "typecheck" do
        for_ toTypecheck \(name, input) -> it ("typechecks " <> toString name) $ typecheckDecls input
    describe "unification shenanigans" do
        for_ unificationShenanigans \input -> xit ("infers a consistent type for " <> toString input) $ sanityCheck input

-- verify that an expression typechecks with the type inferred for it
sanityCheck :: Text -> Expectation
sanityCheck input =
    let Right parsed = parsePretty Parser.term input
        (mbResult, diagnostic) = runPureEff $ runNameGen do
            env <- skipDiagnose Repl.mkDefaultEnv
            afterFixityRes <- skipDiagnose do
                afterNameRes <- NameRes.run env.scope (resolveTerm parsed)
                afterDepRes <- skipDiagnose $ cast.term afterNameRes
                Fixity.run env.fixityMap env.operatorPriorities $ Fixity.parse afterDepRes
            runDiagnose' [("test", input)] $ TC.run env.types do
                let ctx = TC.emptyContext env.values
                (_, vTy) <- TC.generaliseTerm ctx =<< TC.infer ctx afterFixityRes
                TC.check ctx afterFixityRes vTy
     in case mbResult of
            Nothing -> expectationFailure . show $ ShowDiagnostic diagnostic
            Just{} -> pass

typecheckDecls :: Text -> Expectation
typecheckDecls input =
    let Right parsed = parsePretty Parser.code input
        (mbResult, diagnostic) = runPureEff $ runNameGen do
            env <- skipDiagnose Repl.mkDefaultEnv
            fixityDecls <- skipDiagnose do
                afterNameRes <- NameRes.run env.scope (NameRes.resolveNames parsed)
                depResOutput <- skipDiagnose $ resolveDependenciesSimplified' env.fixityMap env.operatorPriorities afterNameRes
                Fixity.resolveFixity depResOutput.fixityMap depResOutput.operatorPriorities depResOutput.declarations
            runDiagnose' [("test", input)] $ (\f -> foldlM f (env.types, env.values) fixityDecls) \(topLevel, values) decl -> do
                (eDecl, newTypes, newValues) <- TC.processDeclaration' topLevel values decl
                newNewValues <- modifyEnv newValues [eDecl]
                pure (newTypes, newNewValues)
     in case mbResult of
            Nothing -> expectationFailure . show $ ShowDiagnostic diagnostic
            Just{} -> pass

skipDiagnose :: Eff (Diagnose : es) a -> Eff es a
skipDiagnose = fmap (fromMaybe (error "got a fatal error diagnostic") . fst) . runDiagnose' []

parsePretty :: Parser' a -> Text -> Either String a
parsePretty parser input =
    lexedInput
        & parse (parser <* eof)
        & first show
  where
    inputBS = encodeUtf8 input
    lexedInput =
        let tokens = case lex' 0 inputBS of
                FP.OK result _ _ -> result
                _ -> []
         in mkTokenStream ("test", inputBS) tokens
