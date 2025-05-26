module LexerSpec (spec) where

import Common (Literal_ (..))
import Data.List.NonEmpty qualified as NE
import FlatParse.Stateful
import LangPrelude
import Lexer
import Syntax.Token
import Test.Hspec

testLexer :: Text -> [Token]
testLexer fileText = case runParser (concatMap NE.toList <$> many token') 0 startPos fileBS of
    OK tokens _ _ -> map snd tokens
    _ -> []
  where
    fileBS = encodeUtf8 fileText
    startPos = unPos (mkPos fileBS (0, 0)) + 1

spec :: Spec
spec = do
    describe "simple examples" do
        it "names and keywords" do
            testLexer "type test Toast 'var infix"
                `shouldBe` [Keyword Type, LowerName "test", UpperName "Toast", ImplicitName "'var", Keyword Infix]
        it "type definition" do
            testLexer "type Peano = S Peano | Z"
                `shouldBe` [Keyword Type, UpperName "Peano", SpecialSymbol Eq, UpperName "S", UpperName "Peano", SpecialSymbol Bar, UpperName "Z"]
        it "literals" do
            testLexer "123 'a' \"huh\"" `shouldBe` Literal <$> [IntLiteral 123, CharLiteral "a", TextLiteral "huh"]
        it "operators" do
            testLexer "|> <| + - %% a>b>c"
                `shouldBe` [Op "|>", Op "<|", Op "+", Op "-", Op "%%", LowerName "a", Op ">", LowerName "b", Op ">", LowerName "c"]
    describe "scope rules" do
        it "newlines" do
            testLexer "a = b\nc = d\ne = f"
                `shouldBe` [ LowerName "a"
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
                `shouldBe` [BlockStart Do, LowerName "this", Semicolon, LowerName "that", Semicolon, LowerName "other", BlockEnd]
        it "line wrap" do
            testLexer "a\nb\n  c\n  d\n    e"
                `shouldBe` [LowerName "a", Newline, LowerName "b", LowerName "c", LowerName "d", LowerName "e"]
        it "let scope" do
            testLexer "f =\n  let test = expr\n  body"
                `shouldBe` [LowerName "f", SpecialSymbol Eq, Keyword Let, LowerName "test", SpecialSymbol Eq, LowerName "expr", Newline, LowerName "body"]
        it "nested scope" do
            testLexer "let test = do this; that\nbody"
                `shouldBe` [ Keyword Let
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
                `shouldBe` [ Keyword Let
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
                `shouldBe` [ LowerName "test"
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
                `shouldBe` [ LowerName "f"
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
