module LexerSpec (spec) where

import Lexer
import Relude
import Text.Megaparsec (parse, errorBundlePretty)
import Test.Hspec
import Data.Text qualified as Text

lex :: Text -> Either String [Token]
lex program = parse tokenise "test" program & first errorBundlePretty

spec :: Spec
spec = do
    describe "lexer" do
        it "parses a non-nested where block" do
            let program = Text.unlines 
                    [ "test = someExpr where"
                    , "  localDefWithTwoSpaces ="
                    , ""
                    , "    notADefinition"
                    ]
            lex program `shouldBe` Right 
                [ LowerIdentifier "test", SpecialSymbol "=", LowerIdentifier "someExpr", BlockKeyword "where"
                , LowerIdentifier "localDefWithTwoSpaces", SpecialSymbol "="
                , LowerIdentifier "notADefinition"
                , BlockEnd, Newline
                ]

        it "parses '+' correctly" do
            let program = Text.unlines 
                    [ "f1 x = x + 1"
                    , "f2 = 1 + 3"
                    ]
            lex program `shouldBe` Right 
                [ LowerIdentifier "f1", LowerIdentifier "x", SpecialSymbol "=", LowerIdentifier "x", Operator "+", IntLiteral 1, Newline
                , LowerIdentifier "f2", SpecialSymbol "=", IntLiteral 1, Operator "+", IntLiteral 3, Newline
                ]

        it "parses multiple definitions with where blocks" do
            let program = Text.unlines 
                    [ "f1 x = x"
                    , "f2 y = expr where"
                    , "  g = <!>"
                    , "  h = 1 + 2 + 3"
                    , "f3 = hmmm where"
                    , " oneSpaceWorks = 13"
                    , " // a line of whitespace should be skipped"
                    , " anotherDef = 111"
                    , "  "
                    , "main = pass"
                    ]

            lex program `shouldBe` Right 
                [ LowerIdentifier "f1", LowerIdentifier "x", SpecialSymbol "=", LowerIdentifier "x", Newline
                , LowerIdentifier "f2", LowerIdentifier "y", SpecialSymbol "=", LowerIdentifier "expr", BlockKeyword "where"
                ,    LowerIdentifier "g", SpecialSymbol "=", Operator "<!>", Newline
                ,    LowerIdentifier "h", SpecialSymbol "=", IntLiteral 1, Operator "+", IntLiteral 2, Operator "+", IntLiteral 3
                , BlockEnd, Newline
                , LowerIdentifier "f3", SpecialSymbol "=", LowerIdentifier "hmmm", BlockKeyword "where"
                ,    LowerIdentifier "oneSpaceWorks", SpecialSymbol "=", IntLiteral 13, Newline
                ,    LowerIdentifier "anotherDef", SpecialSymbol "=", IntLiteral 111
                , BlockEnd, Newline
                , LowerIdentifier "main", SpecialSymbol "=", LowerIdentifier "pass", Newline
                ]

        it "parses nested where blocks" do
            let program = Text.unlines
                    [ "f = expr where"
                    , "  g = expr where"
                    , "      h = expr where"
                    , "              expr = 42"
                    ]
            lex program `shouldBe` Right 
                [ LowerIdentifier "f", SpecialSymbol "=", LowerIdentifier "expr", BlockKeyword "where"
                ,    LowerIdentifier "g", SpecialSymbol "=", LowerIdentifier "expr", BlockKeyword "where"
                ,        LowerIdentifier "h", SpecialSymbol "=", LowerIdentifier "expr", BlockKeyword "where"
                ,            LowerIdentifier "expr", SpecialSymbol "=", IntLiteral 42
                ,        BlockEnd
                ,    BlockEnd
                , BlockEnd, Newline
                ]

        it "parses line wrapping" do
            let program = Text.unlines
                    [ "f x y"
                    , "  |> g z"
                    , "  |> h w"
                    ]
            lex program `shouldBe` Right
                [ LowerIdentifier "f", LowerIdentifier "x", LowerIdentifier "y"
                , Operator "|>", LowerIdentifier "g", LowerIdentifier "z"
                , Operator "|>", LowerIdentifier "h", LowerIdentifier "w",
                Newline
                ]
        it "parses char literals without escape sequences" do
            forM_ [' '..'~'] \sym -> lex ("'" <> one sym <> "'") `shouldBe` Right [CharLiteral $ one sym]

        it "parses text literals" do
            lex "\"this is a string with arbitrary symbols. 123\"" `shouldBe` Right [TextLiteral "this is a string with arbitrary symbols. 123"]

        it "parses semicolons as newlines with correct indent" do
            lex "test = f x where f y = y + y; x = 777\n" `shouldBe` Right 
                [ LowerIdentifier "test", SpecialSymbol "=", LowerIdentifier "f", LowerIdentifier "x", BlockKeyword "where"
                ,     LowerIdentifier "f", LowerIdentifier "y", SpecialSymbol "=", LowerIdentifier "y", Operator "+", LowerIdentifier "y", Newline
                ,     LowerIdentifier "x", SpecialSymbol "=", IntLiteral 777
                , BlockEnd, Newline
                ]

        it "parses where on a separate line" do
            let program = Text.unlines
                    [ "example = expr"
                    , "  where"
                    , "    f x = x"
                    , "    g y = y y"
                    ]
            lex program `shouldBe` Right 
                [ LowerIdentifier "example", SpecialSymbol "=", LowerIdentifier "expr", BlockKeyword "where"
                , LowerIdentifier "f", LowerIdentifier "x", SpecialSymbol "=", LowerIdentifier "x", Newline
                , LowerIdentifier "g", LowerIdentifier "y", SpecialSymbol "=", LowerIdentifier "y", LowerIdentifier "y"
                , BlockEnd, Newline
                ]
        it "parses a pattern match" do
            let program = Text.unlines
                    [ "case list of"
                    , "  Cons x xs -> Yes"
                    , "  Nil -> No"
                    ]
            lex program `shouldBe` Right
                [ Keyword "case", LowerIdentifier "list", BlockKeyword "of"
                , UpperIdentifier "Cons", LowerIdentifier "x", LowerIdentifier "xs", SpecialSymbol "->", UpperIdentifier "Yes", Newline
                , UpperIdentifier "Nil", SpecialSymbol "->", UpperIdentifier "No"
                , BlockEnd, Newline
                ]
        it "parses type variables and variant constructors" do
            lex "'a 'b 'c 'Yes 'No" `shouldBe` Right [LowerQuoted "a", LowerQuoted "b", LowerQuoted "c", UpperQuoted "Yes", UpperQuoted "No"]