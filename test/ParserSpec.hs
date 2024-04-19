{-# LANGUAGE OverloadedLists #-}
module ParserSpec (spec) where

import Parser
import TestPrelude ()
import Syntax.Declaration qualified as D
import Syntax.Term qualified as E
import Syntax.Pattern qualified as P
import Syntax.Type qualified as T
import Lexer
import Relude
import Text.Megaparsec (parse, errorBundlePretty, pos1)
import Test.Hspec
import Data.Text qualified as Text

parsePretty :: Parser a -> Text -> Either String a
parsePretty parser input = input & parse (usingReaderT pos1 parser) "test" & first errorBundlePretty

spec :: Spec
spec = do
    describe "small definitions" do
        it "simple binding" do
            parsePretty code "x = 15" `shouldBe` Right [D.Value "x" [] (E.IntLiteral 15) []]
        it "function definition" do
            parsePretty code "f x = y" `shouldBe` Right [D.Value "f" ["x"] "y" []]
        it "application" do
            parsePretty code "f = g x y" `shouldBe` Right [D.Value "f" [] (E.Application "g" ["x", "y"]) []]

    describe "where clauses" do
        it "one local binding" do
            let program = Text.unlines
                    [ "f = x where"
                    , "  x = 2"
                    ]
            let result = Right
                    [D.Value "f" [] "x" [
                        D.Value "x" [] (E.IntLiteral 2) []
                    ]]
            parsePretty code program `shouldBe` result
        it "multiple bindings" do
            let program = Text.unlines
                    [ "f = g x where g y = y"
                    ,  "g y = y"
                    ,  "x = 111"
                    ]
            parsePretty code program `shouldSatisfy` isRight
    describe "line wrapping" do
        it "simple" do
            let expr = Text.unlines
                    [ "f"
                    , "  x"
                    , "  y"
                    , "  z"
                    ]
            parsePretty term expr `shouldBe` Right (E.Application "f" ["x", "y", "z"])

    describe "if-then-else" do
        it "simple" do
            parsePretty term "if True then \"yes\" else \"huh???\"" `shouldBe` Right (E.If "True" (E.TextLiteral "yes") (E.TextLiteral "huh???"))
        it "nested" do
            parsePretty term "if if True then False else True then 1 else 0" `shouldBe` Right (E.If (E.If "True" "False" "True") (E.IntLiteral 1) (E.IntLiteral 0))

    describe "pattern matching" do
        it "pattern" do
            parsePretty pattern' "Cons x (Cons y (Cons z xs))" `shouldBe` Right (P.Constructor "Cons" ["x", P.Constructor "Cons" ["y", P.Constructor "Cons" ["z", "xs"]]])
        it "int literal" do
            parsePretty pattern' "123" `shouldBe` Right (P.IntLiteral 123)
        it "many patterns" do
            parsePretty (some pattern') "(Cons x xs) y ('Hmmm z)" `shouldBe` Right [P.Constructor "Cons" ["x", "xs"], "y", P.Variant "'Hmmm" ["z"]]
        it "record" do
            parsePretty pattern' "{ x = x, y = y, z = z }" `shouldBe` Right (P.Record [("x", "x"), ("y", "y"), ("z", "z")])
        it "list" do
            parsePretty pattern' "[1, 'a', Just x]" `shouldBe` Right (P.List [P.IntLiteral 1, P.CharLiteral "a", P.Constructor "Just" ["x"]])
        it "nested lists" do
            parsePretty pattern' "[x, [y, z], [[w], []]]" `shouldBe` Right (P.List ["x", P.List ["y", "z"], P.List [P.List ["w"], P.List []]])
        it "case expression" do
            let expr = Text.unlines
                    [ "case list of"
                    , "  Cons x xs -> Yes"
                    , "  Nil -> No"
                    ]
            parsePretty term expr `shouldBe` Right (E.Case "list" [(P.Constructor "Cons" ["x", "xs"], "Yes"), (P.Constructor "Nil" [], "No")])
        it "match expression" do
            let expr = Text.unlines
                    [ "match"
                    , "  Nothing -> Nothing"
                    , "  Just x -> Just (f x)"
                    ]
            parsePretty term expr `shouldBe` Right (E.Match [([P.Constructor "Nothing" []], "Nothing"), ([P.Constructor "Just" ["x"]], E.Application "Just" [E.Application "f" ["x"]])])

    describe "types" do
        it "simple" do
            parsePretty type' "ThisIsAType" `shouldBe` Right "ThisIsAType"
        it "type application" do
            parsePretty type' "Either (List Int) Text" `shouldBe` Right (T.Application "Either" [T.Application "List" ["Int"], "Text"])
        it "record" do
            parsePretty type' "{ x : Int, y : Int, z : Int }" `shouldBe` Right (T.Record [("x", "Int"), ("y", "Int"), ("z", "Int")])
        it "variant" do
            parsePretty type' "['A Int, 'B, 'C Double Unit]" `shouldBe` Right (T.Variant [("'A", ["Int"]), ("'B", []), ("'C", ["Double", "Unit"])])
        it "type variable" do
            parsePretty type' "'var" `shouldBe` Right (T.Var "'var")
        it "forall" do
            parsePretty type' "forall 'a. Maybe 'a" `shouldBe` Right (T.Forall ["'a"] $ T.Application "Maybe" [T.Var "'a"])

    describe "full programs" do
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