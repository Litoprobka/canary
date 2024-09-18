{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE QuasiQuotes #-}

module ParserSpec (spec) where

import Lexer
import NeatInterpolation
import Parser
import Playground
import Relude
import Syntax.Declaration qualified as D
import Syntax.Expression qualified as E
import Syntax.Pattern qualified as P
import Syntax.Type qualified as T
import Test.Hspec
import Text.Megaparsec (errorBundlePretty, parse, pos1, eof)
import Syntax.Row (ExtRow(..))

parsePretty :: Parser a -> Text -> Either String a
parsePretty parser input = input & parse (usingReaderT pos1 parser <* eof) "test" & first errorBundlePretty

spec :: Spec
spec = do
    describe "small definitions" do
        it "simple binding" do
            parsePretty code "x = 15" `shouldBe` Right [D.Value (E.ValueBinding "x" (E.IntLiteral 15)) []]
        it "function definition" do
            parsePretty code "f x = y" `shouldBe` Right [D.Value (E.FunctionBinding "f" ["x"] "y") []]
        it "application" do
            parsePretty code "f = g x y" `shouldBe` Right [D.Value (E.ValueBinding "f" ("g" # "x" # "y")) []]
        it "identifiers may contain keywords" do
            parsePretty expression "matcher case1 diff" `shouldBe` Right ("matcher" # "case1" # "diff")

    describe "where clauses" do
        it "one local binding" do
            let program =
                    [text|
                    f = x where
                      x = 2
                    |]
            let result =
                    Right
                        [ D.Value
                            (E.ValueBinding "f" "x")
                            [ D.Value (E.ValueBinding "x" (E.IntLiteral 2)) []
                            ]
                        ]
            parsePretty code program `shouldBe` result
        it "multiple bindings" do
            let program =
                    [text|
                    f = g x where
                      g y = y
                      x = 111
                    |]
            parsePretty code program `shouldSatisfy` isRight
    describe "line wrapping" do
        it "simple" do
            let expr =
                    [text|
                    f
                      x
                      y
                      z
                    |]
            parsePretty expression expr `shouldBe` Right ("f" # "x" # "y" # "z")
        it "with operators" do
            let expr =
                    [text|
                    x
                      |> f
                      |> g
                    |]
            parsePretty expression expr `shouldBe` Right ("|>" # ("|>" # "x" # "f") # "g")

    describe "let" do
        it "inline" do
            parsePretty expression "let x = y; z" `shouldBe` Right (E.Let (E.ValueBinding "x" "y") "z")
        it "nested" do
            let expr =
                    [text|
                    let x = y
                    let z = x
                    z
                    |]
            parsePretty expression expr `shouldBe` Right (E.Let (E.ValueBinding "x" "y") $ E.Let (E.ValueBinding "z" "x") "z")

    describe "if-then-else" do
        it "simple" do
            parsePretty expression "if True then \"yes\" else \"huh???\""
                `shouldBe` Right (E.If "True" (E.TextLiteral "yes") (E.TextLiteral "huh???"))
        it "nested" do
            parsePretty expression "if if True then False else True then 1 else 0"
                `shouldBe` Right (E.If (E.If "True" "False" "True") (E.IntLiteral 1) (E.IntLiteral 0))
        it "partially applied (todo)" do
            parsePretty expression "(if _ then A else B)" `shouldBe` Right (E.Lambda "$1" $ E.If "$1" "A" "B")
        it "with operators" do
            parsePretty expression "x + if y || z then 4 else 5 * 2"
                `shouldBe` Right (binApp "+" "x" $ E.If (binApp "||" "y" "z") (E.IntLiteral 4) (binApp "*" (E.IntLiteral 5) (E.IntLiteral 2)))

    describe "pattern matching" do
        it "pattern" do
            parsePretty pattern' "Cons x (Cons y (Cons z xs))"
                `shouldBe` Right (P.Constructor "Cons" ["x", P.Constructor "Cons" ["y", P.Constructor "Cons" ["z", "xs"]]])
        it "int literal" do
            parsePretty pattern' "123" `shouldBe` Right (P.IntLiteral 123)
        it "many patterns" do
            parsePretty (some pattern') "(Cons x xs) y ('Hmmm z)"
                `shouldBe` Right [P.Constructor "Cons" ["x", "xs"], "y", P.Variant "'Hmmm" "z"]
        it "annotation pattern" do
            parsePretty pattern' "(Cons x xs : List Int)"
                `shouldBe` Right (P.Annotation (P.Constructor "Cons" ["x", "xs"]) (T.Application (T.Name "List") (T.Name "Int")))
        it "record" do
            parsePretty pattern' "{ x = x, y = y, z = z }" `shouldBe` Right (P.Record [("x", "x"), ("y", "y"), ("z", "z")])
        it "record with implicit names" do
            parsePretty pattern' "{ x, y, z }" `shouldBe` Right (P.Record [("x", "x"), ("y", "y"), ("z", "z")])
        it "list" do
            parsePretty pattern' "[1, 'a', Just x]"
                `shouldBe` Right (P.List [P.IntLiteral 1, P.CharLiteral "a", P.Constructor "Just" ["x"]])
        it "nested lists" do
            parsePretty pattern' "[x, [y, z], [[w], []]]"
                `shouldBe` Right (P.List ["x", P.List ["y", "z"], P.List [P.List ["w"], P.List []]])
        it "case expression" do
            let expr =
                    [text|
                    case list of
                      Cons x xs -> Yes
                      Nil -> No
                    |]
            parsePretty expression expr
                `shouldBe` Right (E.Case "list" [(P.Constructor "Cons" ["x", "xs"], "Yes"), (P.Constructor "Nil" [], "No")])
        it "nested case" do
            let expr =
                    [text|
                    case list of
                        Cons x xs -> case x of
                            Just _  -> Cons True xs
                            Nothing -> Cons False xs
                        Nil -> Nil
                    |]
            let result =
                    Right $
                        E.Case
                            "list"
                            [
                                ( P.Constructor "Cons" ["x", "xs"]
                                , E.Case
                                    "x"
                                    [ (P.Constructor "Just" ["_"], "Cons" # "True" # "xs")
                                    , (P.Constructor "Nothing" [], "Cons" # "False" # "xs")
                                    ]
                                )
                            , (P.Constructor "Nil" [], "Nil")
                            ]
            parsePretty expression expr `shouldBe` result
        it "match expression" do
            let expr =
                    [text|
                    match
                        Nothing -> Nothing
                        (Just x) -> Just (f x)
                    |]
            parsePretty expression expr
                `shouldBe` Right (E.Match [([P.Constructor "Nothing" []], "Nothing"), ([P.Constructor "Just" ["x"]], "Just" # ("f" # "x"))])
        it "inline match" do
            parsePretty expression "match 42 -> True; _ -> False"
                `shouldBe` Right (E.Match [([P.IntLiteral 42], "True"), ([P.Var "_"], "False")])
        it "match in parens" do
            let expr =
                    [text|
                    f (match
                         42 -> True
                         _ -> False)
                      x
                    |]
            parsePretty expression expr `shouldBe` Right ("f" # E.Match [([P.IntLiteral 42], "True"), ([P.Var "_"], "False")] # "x")
        it "multi-arg match" do
            let expr =
                    [text|
                    match
                        Nothing (Just x) y -> case1
                        x Nothing y -> case2
                        Nothing Nothing (Just y) -> case3
                    |]
            parsePretty expression expr
                `shouldBe` Right
                    ( E.Match
                        [ ([P.Constructor "Nothing" [], P.Constructor "Just" ["x"], "y"], "case1")
                        , (["x", P.Constructor "Nothing" [], "y"], "case2")
                        , ([P.Constructor "Nothing" [], P.Constructor "Nothing" [], P.Constructor "Just" ["y"]], "case3")
                        ]
                    )
        it "match with unit variant" do
            let expr =
                    [text|
                    match
                        'None -> Nothing
                        ('Some x) -> Just x
                    |]
            parsePretty expression expr
                `shouldBe` Right (E.Match [([P.Variant "'None" (P.Record [])], "Nothing"), ([P.Variant "'Some" "x"], "Just" # "x")])
        it "guard clauses (todo)" do
            let expr =
                    [text|
                    match
                        Nothing
                            | guess == True -> Just guess
                            | otherwise = Nothing
                        Just x = Just x
                    |]
            parsePretty expression expr `shouldSatisfy` isRight

    describe "implicit lambdas with wildcards" do
        it "(f _ x)" do
            parsePretty expression "(f _ x)" `shouldBe` Right (E.Lambda "$1" $ "f" # "$1" # "x")
        it "should work with operators" do
            parsePretty expression "(_ + x * _ |> f)" `shouldBe` Right (E.Lambda "$1" $ E.Lambda "$2" $ "|>" # ("+" # "$1" # ("*" # "x" # "$2")) # "f")
        it "should scope to the innermost parenthesis" do
            parsePretty expression "(f (_ + _) _ x)" `shouldBe` Right (E.Lambda "$1" $ "f" # E.Lambda "$1" (E.Lambda "$2" $ "+" # "$1" # "$2") # "$1" # "x")
        it "records and lists introduce a scope" do
            parsePretty expression "{x = _, y = 0} z" `shouldBe` Right (E.Lambda "$1" (E.Record [("x", "$1"), ("y", E.IntLiteral 0)]) # "z")
            parsePretty expression "[a, b, c, _, d, _]" `shouldBe` Right (E.Lambda "$1" $ E.Lambda "$2" $ E.List ["a", "b", "c", "$1", "d", "$2"])
        it "should require outer parenthesis" do
            parsePretty expression "f _" `shouldSatisfy` isLeft
            parsePretty expression "f _ x" `shouldSatisfy` isLeft

    describe "misc. builtins" do
        it "list" do
            parsePretty expression "[1, 2, 3]" `shouldBe` Right (E.List [E.IntLiteral 1, E.IntLiteral 2, E.IntLiteral 3])
        it "record construction" do
            parsePretty expression "{ x = 1, y }" `shouldBe` Right (E.Record [("x", E.IntLiteral 1), ("y", "y")])

    describe "operators" do
        it "2 + 2" do
            parsePretty expression "x + x" `shouldBe` Right (binApp "+" "x" "x")
        it "precedence" do
            parsePretty expression "x + y * z / w" `shouldBe` Right (binApp "+" "x" (binApp "/" (binApp "*" "y" "z") "w"))
        it "lens composition binds tighter than function application" do
            parsePretty expression "f x . y" `shouldBe` Right ("f" # binApp "." "x" "y")

    describe "types" do
        it "simple" do
            parsePretty type' "ThisIsAType" `shouldBe` Right "ThisIsAType"
        it "type application" do
            parsePretty type' "Either (List Int) Text"
                `shouldBe` Right (T.Application (T.Application "Either" (T.Application "List" "Int")) "Text")
        it "function type" do
            parsePretty type' "'b -> ('a -> 'b) -> Maybe 'a -> 'b"
                `shouldBe` Right
                    ( T.Function (T.Var "'b") $
                        T.Function (T.Function (T.Var "'a") (T.Var "'b")) $
                            T.Function (T.Application "Maybe" $ T.Var "'a") $
                                T.Var "'b"
                    )
        it "record" do
            parsePretty type' "{ x : Int, y : Int, z : Int }" `shouldBe` Right (T.Record $ NoExtRow [("x", "Int"), ("y", "Int"), ("z", "Int")])
        it "duplicate record fields" do
            parsePretty type' "{x : Int, y : Bool, x : Text}" `shouldBe` Right (T.Record $ NoExtRow [("y", "Bool"), ("x", "Int"), ("x", "Text")])
        it "variant" do
            parsePretty type' "['A Int, 'B, 'C Double]" `shouldBe` Right (T.Variant $ NoExtRow [("'A", "Int"), ("'B", "Unit"), ("'C", "Double")])
        it "type variable" do
            parsePretty type' "'var" `shouldBe` Right (T.Var "'var")
        it "forall" do
            parsePretty type' "forall 'a. Maybe 'a" `shouldBe` Right (T.Forall "'a" $ T.Application "Maybe" $ T.Var "'a")

    describe "full programs" do
        it "parses the old lambdaTest (with tabs)" do
            let program =
                    [text|
                    main = testt (λx y -> y) where
                     test z = z z
                     f y = y
                    
                    testt = λx y -> id x
                     (λx -> id x) 
                     2 y
                    
                    id x = x
                    ap = λf x -> f x
                    const x y = x
                    
                    
                    list = λc n -> c 1 (c 2 (c 3 n))
                    map = λf xs cons -> xs (b cons f)
                    b f g x = f (g x)
                    |]
            parsePretty code program `shouldSatisfy` isRight