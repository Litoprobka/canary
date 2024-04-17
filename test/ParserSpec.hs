module ParserSpec (spec) where

import Parser
import Syntax.Declaration qualified as D
import Syntax.Term qualified as E
import Syntax.Pattern qualified as P
import Syntax.Type qualified as T
import Lexer
import Relude
import Text.Megaparsec (parse, errorBundlePretty, pos1)
import Test.Hspec
import Data.Text qualified as Text
import qualified Data.HashMap.Strict as Map

parsePretty :: Parser a -> Text -> Either String a
parsePretty parser input = input & parse (usingReaderT pos1 parser) "test" & first errorBundlePretty

spec :: Spec
spec = do
    describe "small definitions" do
        it "simple binding" do
            parsePretty code "x = 15" `shouldBe` Right [D.Value "x" [] (E.IntLiteral 15) []]
        it "function definition" do
            parsePretty code "f x = y" `shouldBe` Right [D.Value "f" [P.Var "x"] (E.Name "y") []]
        it "application" do
            parsePretty code "f = g x y" `shouldBe` Right [D.Value "f" [] (E.Application (E.Name "g") (E.Name "x" :| [E.Name "y"])) []]

    describe "where clauses" do
        it "one local binding" do
            let program = Text.unlines
                    [ "f = x where"
                    , "  x = 2"
                    ]
            let result = Right
                    [D.Value "f" [] (E.Name "x") [
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
            parsePretty term expr `shouldBe` Right (E.Application (E.Name "f") (E.Name "x" :| [E.Name "y", E.Name "z"]))
    
    describe "if-then-else" do
        it "simple" do
            parsePretty term "if True then \"yes\" else \"huh???\"" `shouldBe` Right (E.If (E.Constructor "True") (E.TextLiteral "yes") (E.TextLiteral "huh???"))
        it "nested" do
            parsePretty term "if if True then False else True then 1 else 0" `shouldBe` Right (E.If (E.If (E.Constructor "True") (E.Constructor "False") (E.Constructor "True")) (E.IntLiteral 1) (E.IntLiteral 0))

    describe "pattern matching" do
        it "pattern" do
            parsePretty pattern' "Cons x (Cons y (Cons z xs))" `shouldBe` Right (P.Constructor "Cons" [P.Var "x", P.Constructor "Cons" [P.Var "y", P.Constructor "Cons" [P.Var "z", P.Var "xs"]]])
        it "int literal (todo)" do
            parsePretty pattern' "123" `shouldBe` Right (P.Variant "todo" [])
        it "many patterns" do
            parsePretty (some pattern') "(Cons x xs) y ('Hmmm z)" `shouldBe` Right [P.Constructor "Cons" [P.Var "x", P.Var "xs"], P.Var "y", P.Variant "'Hmmm" [P.Var "z"]]
        it "record" do
            parsePretty pattern' "{ x = x, y = y, z = z }" `shouldBe` Right (P.Record $ Map.fromList [("x", P.Var "x"), ("y", P.Var "y"), ("z", P.Var "z")])
        it "pattern match" do
            let expr = Text.unlines
                    [ "case list of"
                    , "  Cons x xs -> Yes"
                    , "  Nil -> No"
                    ]
            parsePretty term expr `shouldBe` Right (E.Case (E.Name "list") [(P.Constructor "Cons" [P.Var "x", P.Var "xs"], E.Constructor "Yes"), (P.Constructor "Nil" [], E.Constructor "No")])

    describe "types" do
        it "simple" do
            parsePretty type' "ThisIsAType" `shouldBe` Right (T.Name "ThisIsAType")
        it "type application" do
            parsePretty type' "Either (List Int) Text" `shouldBe` Right (T.Application (T.Name "Either") $ T.Application (T.Name "List") (one $ T.Name "Int") :| [T.Name "Text"])
        it "record" do
            parsePretty type' "{ x : Int, y : Int, z : Int }" `shouldBe` Right (T.Record $ Map.fromList [("x", T.Name "Int"), ("y", T.Name "Int"), ("z", T.Name "Int")])
        it "variant" do
            parsePretty type' "['A Int, 'B, 'C Double Unit]" `shouldBe` Right (T.Variant $ Map.fromList [("'A", [T.Name "Int"]), ("'B", []), ("'C", [T.Name "Double", T.Name "Unit"])])
        it "type variable (todo)" do
            parsePretty type' "'var" `shouldBe` Right (T.Name "todo")
        it "forall" do
            parsePretty type' "forall 'a. Maybe Text" `shouldBe` Right (T.Forall ["'a"] $ T.Application (T.Name "Maybe") (T.Name "Text" :| []))

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