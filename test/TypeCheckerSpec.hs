{-# LANGUAGE QuasiQuotes #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module TypeCheckerSpec (spec) where

import Data.Traversable (for)
import DependencyResolution (cast)
import Diagnostic (Diagnose, ShowDiagnostic (..), runDiagnose')
import Effectful (Eff, runPureEff)
import Error.Diagnose (Diagnostic)
import Fixity qualified
import FlatParse.Stateful qualified as FP
import Lexer (lex', mkTokenStream)
import NameGen
import NameResolution
import NameResolution qualified as NameRes
import Parser
import Prettyprinter hiding (list)
import Prettyprinter.Render.Terminal (AnsiStyle)
import Proto (eof, parse)
import Relude hiding (State, readFile)
import Repl qualified
import Syntax.AstTraversal
import System.Directory.OsPath (listDirectory)
import System.File.OsPath (readFile)
import System.OsPath (osp, takeFileName, (</>))
import Test.Hspec
import Trace
import TypeChecker qualified as TC
import TypeChecker.Backend qualified as TC
import TypeChecker.Generalisation

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
    , "\\r -> r.x"
    , "match {x, y, z} -> [x, y, z]"
    , "\\r -> [(case r of {x} -> x), case r of {y} -> y]"
    , "\\f r -> case r of {x, y} -> f x y"
    , "\\r f -> case r of {x, y} -> f x y"
    ]

-- these tests require unification postponing to work
postponing :: [Text]
postponing =
    [ "\\a b c -> c (b a) (c a a)"
    , "\\a b -> a (\\x -> b x) (\\z -> a b b) {}"
    , "\\f r -> f r.x r.y"
    , "[\\f r -> f r.x r.y, \\f r -> f r.x r.y]"
    ]

toInfer :: [(String, Text)]
toInfer =
    [ ("null", "null = match Nil -> True; (Cons _ _) -> False")
    , ("map", "map f xs = case xs of Nil -> Nil; Cons x xs -> Cons (f x) (map f xs)")
    , ("map (match)", "map f = match Nil -> Nil; Cons x xs -> Cons (f x) (map f xs)")
    , ("len", "type Peano = S Peano | Z\nlen xs = case xs of Nil -> Z; Cons _ xs -> S (len xs)")
    ]

toReject :: [(String, Text)]
toReject =
    [ ("pattern matching on existentials", "type Any where MkAny : 'a -> Any\ninvalid (MkAny 11) = True")
    ]

spec :: Spec
spec = do
    describe "sanity check" do
        for_ toSanityCheck \input -> it ("infers a consistent type for " <> toString input) $ sanityCheck input
    describe "typecheck" do
        for_ toInfer \(name, input) -> it ("infers " <> name) $ knownFailingDecls input
    describe "unification shenanigans" do
        for_ postponing \input -> it ("infers a consistent type for " <> toString input) $ sanityCheck input
    describe "should reject some invalid programs" do
        for_ toReject \(name, input) -> it ("rejects " <> name) $ rejectsDecls input

    describe "full programs" do
        sequenceA_ =<< runIO do
            let testDir = [osp|./test/typecheck|]
            fileNames <- listDirectory testDir
            for fileNames \file -> do
                fileContents <- decodeUtf8 <$> readFile (testDir </> file)
                pure $ it ("typechecks " <> show (takeFileName file)) (acceptsDecls fileContents)

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
            skipTrace $ runDiagnose' [("test", input)] $ TC.run env.types env.conMetadata do
                let ctx = TC.emptyContext env.values
                (_, vTy) <- generaliseTerm ctx =<< TC.infer ctx afterFixityRes
                zonkTerm ctx =<< TC.check ctx afterFixityRes vTy
     in case mbResult of
            Nothing -> expectationFailure . show $ ShowDiagnostic diagnostic
            Just{} -> pass

typecheckDecls :: Text -> (Maybe Repl.ReplEnv, Diagnostic (Doc AnsiStyle))
typecheckDecls input =
    let Right decls = parsePretty Parser.code input
     in runPureEff $ runNameGen do
            env <- skipDiagnose Repl.mkDefaultEnv
            runDiagnose' [("test", input)] $ skipTrace $ Repl.processDecls env decls

acceptsDecls :: Text -> Expectation
acceptsDecls input = case typecheckDecls input of
    (Nothing, diagnostic) -> expectationFailure . show $ ShowDiagnostic diagnostic
    (Just{}, _) -> pass

rejectsDecls :: Text -> Expectation
rejectsDecls input = case fst $ typecheckDecls input of
    Nothing -> pass
    Just{} -> expectationFailure "expected to reject program"

knownFailingDecls :: Text -> Expectation
knownFailingDecls input = case fst $ typecheckDecls input of
    Nothing -> pendingWith "known failure"
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
