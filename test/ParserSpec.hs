module ParserSpec (spec) where

import Parser
import Syntax.Declaration qualified as D
import Syntax.Term qualified as T
import Syntax.Pattern qualified as P
import Lexer
import Relude
import Text.Megaparsec (parse, errorBundlePretty, pos1)
import Test.Hspec
import Data.Text qualified as Text

parsePretty :: Parser a -> Text -> Either String a
parsePretty parser input = input & parse (usingReaderT pos1 parser) "test" & first errorBundlePretty

spec :: Spec
spec = do
    describe "parser" do
        it "parses a simple binding" do
            parsePretty code "x = 15" `shouldBe` Right [D.Value "x" [] (T.IntLiteral 15) []]
        it "parses a function definition" do
            parsePretty code "f x = y" `shouldBe` Right [D.Value "f" [P.Var "x"] (T.Name "y") []]
        it "parses an application" do
            parsePretty code "f = g x y" `shouldBe` Right [D.Value "f" [] (T.Application (T.Name "g") (T.Name "x" :| [T.Name "y"])) []]
        it "parses a declaration with a where clause" do
            let program = Text.unlines
                    [ "f = x where"
                    , "  x = 2"
                    ]
            let result = Right 
                    [D.Value "f" [] (T.Name "x") [
                        D.Value "x" [] (T.IntLiteral 2) []
                    ]]
            parsePretty code program `shouldBe` result
        it "parses a declaration with a where clause and multiple bindings" do
            let program = Text.unlines
                    [ "f = g x where g y = y"
                    ,  "g y = y"
                    ,  "x = 111"
                    ]
            parsePretty code program `shouldSatisfy` isRight 
        it "parses if-then-else" do
            parsePretty term "if True then \"yes\" else \"huh???\"" `shouldBe` Right (T.If (T.Constructor "True") (T.TextLiteral "yes") (T.TextLiteral "huh???"))
        it "parses a pattern" do
            parsePretty pattern' "Cons x (Cons y (Cons z xs))" `shouldBe` Right (P.Constructor "Cons" [P.Var "x", P.Constructor "Cons" [P.Var "y", P.Constructor "Cons" [P.Var "z", P.Var "xs"]]])
        it "parses a pattern match" do
            let expr = Text.unlines
                    [ "case list of"
                    , "  Cons x xs -> Yes"
                    , "  Nil -> No"
                    ]
            parsePretty term expr `shouldBe` Right (T.Case (T.Name "list") [(P.Constructor "Cons" [P.Var "x", P.Var "xs"], T.Constructor "Yes"), (P.Constructor "Nil" [], T.Constructor "No")])

        it "parses the old lambdaTest (with tabs)" do
            let program = Text.unlines 
                    [ "main = testt (λx y -> y) where"
                    , " test z = z z"
                    , " f y = y"
                    , ""
                    , "testt = λx y -> id x"
                    , " (λx -> id x) "
                    , " 2 y"
                    , ""
                    , "id x = x"
                    , "ap = λf x -> f x"
                    , "const x y = x"
                    , ""
                    , ""
                    , "list = λc n -> c 1 (c 2 (c 3 n))"
                    , "map = λf xs cons -> xs (b cons f)"
                    , "b f g x = f (g x)"
                    ]
            parsePretty code program `shouldSatisfy` isRight