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
                [ Identifier "test", SpecialSymbol "=", Identifier "someExpr", BlockKeyword "where"
                , Identifier "localDefWithTwoSpaces", SpecialSymbol "="
                , Identifier "notADefinition"
                , BlockEnd, Newline
                ]

        it "parses '+' correctly" do
            let program = Text.unlines 
                    [ "f1 x = x + 1"
                    , "f2 = 1 + 3"
                    ]
            lex program `shouldBe` Right 
                [ Identifier "f1", Identifier "x", SpecialSymbol "=", Identifier "x", Operator "+", IntLiteral 1, Newline
                , Identifier "f2", SpecialSymbol "=", IntLiteral 1, Operator "+", IntLiteral 3, Newline
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
                [ Identifier "f1", Identifier "x", SpecialSymbol "=", Identifier "x", Newline
                , Identifier "f2", Identifier "y", SpecialSymbol "=", Identifier "expr", BlockKeyword "where"
                ,    Identifier "g", SpecialSymbol "=", Operator "<!>", Newline
                ,    Identifier "h", SpecialSymbol "=", IntLiteral 1, Operator "+", IntLiteral 2, Operator "+", IntLiteral 3
                , BlockEnd, Newline
                , Identifier "f3", SpecialSymbol "=", Identifier "hmmm", BlockKeyword "where"
                ,    Identifier "oneSpaceWorks", SpecialSymbol "=", IntLiteral 13, Newline
                ,    Identifier "anotherDef", SpecialSymbol "=", IntLiteral 111
                , BlockEnd, Newline
                , Identifier "main", SpecialSymbol "=", Identifier "pass", Newline
                ]

        it "parses nested where blocks" do
            let program = Text.unlines
                    [ "f = expr where"
                    , "  g = expr where"
                    , "      h = expr where"
                    , "              expr = 42"
                    ]
            lex program `shouldBe` Right 
                [ Identifier "f", SpecialSymbol "=", Identifier "expr", BlockKeyword "where"
                ,    Identifier "g", SpecialSymbol "=", Identifier "expr", BlockKeyword "where"
                ,        Identifier "h", SpecialSymbol "=", Identifier "expr", BlockKeyword "where"
                ,            Identifier "expr", SpecialSymbol "=", IntLiteral 42
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
                [ Identifier "f", Identifier "x", Identifier "y"
                , Operator "|>", Identifier "g", Identifier "z"
                , Operator "|>", Identifier "h", Identifier "w",
                Newline
                ]
        it "parses char literals without escape sequences" do
            forM_ [' '..'~'] \sym -> lex ("'" <> one sym <> "'") `shouldBe` Right [CharLiteral $ one sym]

        it "parses text literals" do
            lex "\"this is a string with arbitrary symbols. 123\"" `shouldBe` Right [TextLiteral "this is a string with arbitrary symbols. 123"]

        it "parses semicolons as newlines with correct indent" do
            lex "test = f x where f y = y + y; x = 777\n" `shouldBe` Right 
                [ Identifier "test", SpecialSymbol "=", Identifier "f", Identifier "x", BlockKeyword "where"
                ,     Identifier "f", Identifier "y", SpecialSymbol "=", Identifier "y", Operator "+", Identifier "y", Newline
                ,     Identifier "x", SpecialSymbol "=", IntLiteral 777
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
                [ Identifier "example", SpecialSymbol "=", Identifier "expr", BlockKeyword "where"
                , Identifier "f", Identifier "x", SpecialSymbol "=", Identifier "x", Newline
                , Identifier "g", Identifier "y", SpecialSymbol "=", Identifier "y", Identifier "y"
                , BlockEnd, Newline
                ]