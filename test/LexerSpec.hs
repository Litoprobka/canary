{-# LANGUAGE QuasiQuotes #-}

module LexerSpec (spec) where

import Common (Literal_ (..))
import FlatParse.Stateful
import LangPrelude
import Lexer
import NeatInterpolation
import Syntax.Token
import Test.Hspec

infix 1 `shouldLex`

testLexer :: Text -> ([Token], ByteString)
testLexer fileText = case lex' 0 (encodeUtf8 fileText) of
    OK tokens _ remaining -> (map snd tokens, remaining)
    _ -> ([], encodeUtf8 fileText)

shouldLex :: ([Token], ByteString) -> [Token] -> Expectation
shouldLex lexerOutput expected = lexerOutput `shouldBe` (expected, "")

spec :: Spec
spec = do
    describe "simple examples" do
        it "names and keywords" do
            testLexer "type test Toast 'var infix"
                `shouldLex` [Keyword Type, LowerName "test", UpperName "Toast", ImplicitName "'var", Keyword Infix]
        it "type definition" do
            testLexer "type Peano = S Peano | Z"
                `shouldLex` [Keyword Type, UpperName "Peano", SpecialSymbol Eq, UpperName "S", UpperName "Peano", SpecialSymbol Bar, UpperName "Z"]
        it "literals" do
            testLexer "123 'a' \"huh\"" `shouldLex` Literal <$> [IntLiteral 123, CharLiteral "a", TextLiteral "huh"]
        it "operators" do
            testLexer "|> <| + - %% a>b>c :: :+"
                `shouldLex` [ Op "|>"
                            , Op "<|"
                            , Op "+"
                            , Op "-"
                            , Op "%%"
                            , LowerName "a"
                            , Op ">"
                            , LowerName "b"
                            , Op ">"
                            , LowerName "c"
                            , ColonOp "::"
                            , ColonOp ":+"
                            ]
        it "comment" do
            testLexer
                [text|
                -- don't mind the comment
                hello
                |]
                `shouldLex` [LowerName "hello"]
        it "definitions with comments" do
            testLexer
                [text|
                -- h1 : Unit -> Bool -> c
                h1 _ x = h2 x Unit
                -- h2 : Bool -> Unit -> c
                h2 _ x = h1 x False
                |]
                `shouldLex` [ LowerName "h1"
                            , Wildcard "_"
                            , LowerName "x"
                            , SpecialSymbol Eq
                            , LowerName "h2"
                            , LowerName "x"
                            , UpperName "Unit"
                            , Newline
                            , LowerName "h2"
                            , Wildcard "_"
                            , LowerName "x"
                            , SpecialSymbol Eq
                            , LowerName "h1"
                            , LowerName "x"
                            , UpperName "False"
                            ]
    describe "scope rules" do
        it "newlines" do
            testLexer "a = b\nc = d\ne = f"
                `shouldLex` [ LowerName "a"
                            , SpecialSymbol Eq
                            , LowerName "b"
                            , Newline
                            , LowerName "c"
                            , SpecialSymbol Eq
                            , LowerName "d"
                            , Newline
                            , LowerName "e"
                            , SpecialSymbol Eq
                            , LowerName "f"
                            ]
        it "block scopes" do
            testLexer "do this; that; other"
                `shouldLex` [BlockStart Do, LowerName "this", Semicolon, LowerName "that", Semicolon, LowerName "other", BlockEnd]
        it "line wrap" do
            testLexer "a\nb\n  c\n  d\n    e"
                `shouldLex` [LowerName "a", Newline, LowerName "b", LowerName "c", LowerName "d", LowerName "e"]
        it "let scope" do
            testLexer "f =\n  let test = expr\n  body"
                `shouldLex` [LowerName "f", SpecialSymbol Eq, Keyword Let, LowerName "test", SpecialSymbol Eq, LowerName "expr", Newline, LowerName "body"]
        it "nested scope" do
            testLexer "let test = do this; that\nbody"
                `shouldLex` [ Keyword Let
                            , LowerName "test"
                            , SpecialSymbol Eq
                            , BlockStart Do
                            , LowerName "this"
                            , Semicolon
                            , LowerName "that"
                            , BlockEnd
                            , Newline
                            , LowerName "body"
                            ]
        it "nested scope 2" do
            testLexer "let test = do\n  this\n  that\nbody"
                `shouldLex` [ Keyword Let
                            , LowerName "test"
                            , SpecialSymbol Eq
                            , BlockStart Do
                            , LowerName "this"
                            , Newline
                            , LowerName "that"
                            , BlockEnd
                            , Newline
                            , LowerName "body"
                            ]
        it "line wrap in blocks" do
            testLexer "test = 3 where\n  f x =\n    x"
                `shouldLex` [ LowerName "test"
                            , SpecialSymbol Eq
                            , Literal (IntLiteral 3)
                            , BlockStart Where
                            , LowerName "f"
                            , LowerName "x"
                            , SpecialSymbol Eq
                            , LowerName "x"
                            , BlockEnd
                            ]
        it "let chains" do
            testLexer "f =\n  let a = b\n  let c = d\n  body"
                `shouldLex` [ LowerName "f"
                            , SpecialSymbol Eq
                            , Keyword Let
                            , LowerName "a"
                            , SpecialSymbol Eq
                            , LowerName "b"
                            , Newline
                            , Keyword Let
                            , LowerName "c"
                            , SpecialSymbol Eq
                            , LowerName "d"
                            , Newline
                            , LowerName "body"
                            ]
        it "match block" do
            let expr =
                    [text|
                    match
                        Nothing -> Nothing
                        (Just x) -> Just (f x)
                    |]
            testLexer expr
                `shouldLex` [ BlockStart Match
                            , UpperName "Nothing"
                            , SpecialSymbol Arrow
                            , UpperName "Nothing"
                            , Newline
                            , LParen
                            , UpperName "Just"
                            , LowerName "x"
                            , RParen
                            , SpecialSymbol Arrow
                            , UpperName "Just"
                            , LParen
                            , LowerName "f"
                            , LowerName "x"
                            , RParen
                            , BlockEnd
                            ]
        it "relaxed block rules in parens" do
            let expr =
                    [text|
                    thing = [
                        a,
                        b,
                    c,
                    d
                    ]
                    |]
            testLexer expr
                `shouldLex` [ LowerName "thing"
                            , SpecialSymbol Eq
                            , LBracket
                            , LowerName "a"
                            , Comma
                            , LowerName "b"
                            , Comma
                            , LowerName "c"
                            , Comma
                            , LowerName "d"
                            , RBracket
                            ]
        it "another match example" do
            let program =
                    [text|
                    type Peano = Z | S Peano

                    f = match
                        Z -> id
                        (S n) -> \_ -> n
                    |]
            testLexer program
                `shouldLex` [ Keyword Type
                            , UpperName "Peano"
                            , SpecialSymbol Eq
                            , UpperName "Z"
                            , SpecialSymbol Bar
                            , UpperName "S"
                            , UpperName "Peano"
                            , Newline
                            , LowerName "f"
                            , SpecialSymbol Eq
                            , BlockStart Match
                            , UpperName "Z"
                            , SpecialSymbol Arrow
                            , LowerName "id"
                            , Newline
                            , LParen
                            , UpperName "S"
                            , LowerName "n"
                            , RParen
                            , SpecialSymbol Arrow
                            , SpecialSymbol Lambda
                            , Wildcard "_"
                            , SpecialSymbol Arrow
                            , LowerName "n"
                            , BlockEnd
                            ]
        it "let rec" do
            let program =
                    [text|
                    test = let rec
                             a = b
                             b = c
                             c = 123
                           b
                    |]
            testLexer program
                `shouldLex` [ LowerName "test"
                            , SpecialSymbol Eq
                            , Keyword Let
                            , BlockStart Rec
                            , LowerName "a"
                            , SpecialSymbol Eq
                            , LowerName "b"
                            , Newline
                            , LowerName "b"
                            , SpecialSymbol Eq
                            , LowerName "c"
                            , Newline
                            , LowerName "c"
                            , SpecialSymbol Eq
                            , Literal (IntLiteral 123)
                            , BlockEnd
                            , Newline
                            , LowerName "b"
                            ]
