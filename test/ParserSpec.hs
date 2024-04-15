module ParserSpec (spec) where

import Parser
import Syntax.All
import Syntax.Declaration qualified as D
import Syntax.Term qualified as T
import Syntax.Pattern qualified as P
import Lexer
import Relude
import Text.Megaparsec (parseMaybe)
import Test.Hspec
import Data.Text qualified as Text

tokeniseThenParse :: Parser a -> Text -> Maybe a
tokeniseThenParse parser input = input & parseMaybe tokenise >>= parseMaybe parser

parse :: Text -> Maybe [Declaration]
parse = tokeniseThenParse code

parseTerm :: Text -> Maybe Term
parseTerm = tokeniseThenParse term

spec :: Spec
spec = do
    describe "parser" do
        it "parses a simple binding" do
            parse "x = 15" `shouldBe` Just [D.Value "x" [] (T.IntLiteral 15) []]
        it "parses a function definition" do
            parse "f x = y" `shouldBe` Just [D.Value "f" [P.Var "x"] (T.Name "y") []]
        it "parses an application" do
            parse "f = g x y" `shouldBe` Just [D.Value "f" [] (T.Application (T.Name "g") (T.Name "x" :| [T.Name "y"])) []]
        it "parses a declaration with a where clause" do
            let program = Text.unlines
                    [ "f = x where"
                    , "  x = 2"
                    ]
            let result = Just 
                    [D.Value "f" [] (T.Name "x") [
                        D.Value "x" [] (T.IntLiteral 2) []
                    ]]
            parse program `shouldBe` result

        it "parses if-then-else" do
            parseTerm "if True then \"yes\" else \"huh???\"" `shouldBe` Just (T.If (T.Constructor "True") (T.TextLiteral "yes") (T.TextLiteral "huh???"))
        it "parses a pattern" do
            tokeniseThenParse pattern' "Cons x (Cons y (Cons z xs))" `shouldBe` Just (P.Constructor "Cons" [P.Var "x", P.Constructor "Cons" [P.Var "y", P.Constructor "Cons" [P.Var "z", P.Var "xs"]]])
        it "parses a pattern match" do
            let expr = Text.unlines
                    [ "case list of"
                    , "  Cons x xs -> Yes"
                    , "  Nil -> No"
                    ]
            parseTerm expr `shouldBe` Just (T.Case (T.Name "list") [(P.Constructor "Cons" [P.Var "x", P.Var "y"], T.Constructor "'Yes"), (P.Constructor "Nil" [], T.Constructor "'No")])