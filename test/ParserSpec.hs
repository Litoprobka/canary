{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE QuasiQuotes #-}

module ParserSpec (spec) where

import Common
import Lexer
import NeatInterpolation
import Parser
import Playground
import Relude
import Syntax.Expression qualified as E
import Syntax.Pattern qualified as P
import Syntax.Row (ExtRow (..))
import Syntax.Type qualified as T
import Test.Hspec
import Text.Megaparsec (eof, errorBundlePretty, parse, pos1)

parsePretty :: Parser a -> Text -> Either String a
parsePretty parser input = input & parse (usingReaderT pos1 parser <* eof) "test" & first errorBundlePretty

spec :: Spec
spec = do
    describe "small definitions" do
        it "simple binding" do
            parsePretty code "x = 15" `shouldBe` Right [valueDec (E.ValueBinding "x" (E.Literal $ intLit 15)) []]
        it "function definition" do
            parsePretty code "f x = y" `shouldBe` Right [valueDec (E.FunctionBinding "f" ["x"] "y") []]
        it "application" do
            parsePretty code "f = g x y" `shouldBe` Right [valueDec (E.ValueBinding "f" ("g" # "x" # "y")) []]
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
                        [ valueDec
                            (E.ValueBinding "f" "x")
                            [ valueDec (E.ValueBinding "x" (E.Literal $ intLit 2)) []
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
            parsePretty expression "let x = y; z" `shouldBe` Right (let_ (E.ValueBinding "x" "y") "z")
        it "nested" do
            let expr =
                    [text|
                    let x = y
                    let z = x
                    z
                    |]
            parsePretty expression expr `shouldBe` Right (let_ (E.ValueBinding "x" "y") $ let_ (E.ValueBinding "z" "x") "z")

    describe "if-then-else" do
        it "simple" do
            parsePretty expression "if True then \"yes\" else \"huh???\""
                `shouldBe` Right (if_ "True" (E.Literal $ textLit "yes") (E.Literal $ textLit "huh???"))
        it "nested" do
            parsePretty expression "if if True then False else True then 1 else 0"
                `shouldBe` Right (if_ (if_ "True" "False" "True") (E.Literal $ intLit 1) (E.Literal $ intLit 0))
        it "partially applied" do
            parsePretty expression "(if _ then A else B)" `shouldBe` Right (lam "$1" $ if_ "$1" "A" "B")
        it "with operators" do
            parsePretty expression "x + if y || z then 4 else 5 * 2"
                `shouldBe` Right
                    (binApp "+" "x" $ if_ (binApp "||" "y" "z") (E.Literal $ intLit 4) (binApp "*" (E.Literal $ intLit 5) (E.Literal $ intLit 2)))
        it "fixity shenanigans" do
            parsePretty expression "if cond then 1 else 2 == 3 == 4" `shouldSatisfy` isLeft

    describe "pattern matching" do
        it "pattern" do
            parsePretty pattern' "Cons x (Cons y (Cons z xs))"
                `shouldBe` Right (con "Cons" ["x", con "Cons" ["y", con "Cons" ["z", "xs"]]])
        it "int literal" do
            parsePretty pattern' "123" `shouldBe` Right (P.Literal $ intLit 123)
        it "many patterns" do
            parsePretty (some pattern') "(Cons x xs) y ('Hmmm z)"
                `shouldBe` Right [con "Cons" ["x", "xs"], "y", P.Variant "'Hmmm" "z"]
        it "annotation pattern" do
            parsePretty pattern' "(Cons x xs : List Int)"
                `shouldBe` Right (P.Annotation (con "Cons" ["x", "xs"]) (T.Application (T.Name "List") (T.Name "Int")))
        it "record" do
            parsePretty pattern' "{ x = x, y = y, z = z }" `shouldBe` Right (recordP [("x", "x"), ("y", "y"), ("z", "z")])
        it "record with implicit names" do
            parsePretty pattern' "{ x, y, z }" `shouldBe` Right (recordP [("x", "x"), ("y", "y"), ("z", "z")])
        it "list" do
            parsePretty pattern' "[1, 'a', Just x]"
                `shouldBe` Right (listP [P.Literal $ intLit 1, P.Literal $ charLit "a", con "Just" ["x"]])
        it "nested lists" do
            parsePretty pattern' "[x, [y, z], [[w], []]]"
                `shouldBe` Right (listP ["x", listP ["y", "z"], listP [listP ["w"], listP []]])
        it "case expression" do
            let expr =
                    [text|
                    case list of
                      Cons x xs -> Yes
                      Nil -> No
                    |]
            parsePretty expression expr
                `shouldBe` Right (case_ "list" [(con "Cons" ["x", "xs"], "Yes"), (con "Nil" [], "No")])
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
                        case_
                            "list"
                            [
                                ( con "Cons" ["x", "xs"]
                                , case_
                                    "x"
                                    [ (con "Just" ["_"], "Cons" # "True" # "xs")
                                    , (con "Nothing" [], "Cons" # "False" # "xs")
                                    ]
                                )
                            , (con "Nil" [], "Nil")
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
                `shouldBe` Right (match [([con "Nothing" []], "Nothing"), ([con "Just" ["x"]], "Just" # ("f" # "x"))])
        it "inline match" do
            parsePretty expression "match 42 -> True; _ -> False"
                `shouldBe` Right (match [([P.Literal $ intLit 42], "True"), ([P.Var "_"], "False")])
        it "match in parens" do
            let expr =
                    [text|
                    f (match
                         42 -> True
                         _ -> False)
                      x
                    |]
            parsePretty expression expr `shouldBe` Right ("f" # match [([P.Literal $ intLit 42], "True"), ([P.Var "_"], "False")] # "x")
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
                    ( match
                        [ ([con "Nothing" [], con "Just" ["x"], "y"], "case1")
                        , (["x", con "Nothing" [], "y"], "case2")
                        , ([con "Nothing" [], con "Nothing" [], con "Just" ["y"]], "case3")
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
                `shouldBe` Right (match [([P.Variant "'None" (recordP [])], "Nothing"), ([P.Variant "'Some" "x"], "Just" # "x")])
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
            parsePretty expression "(f _ x)" `shouldBe` Right (lam "$1" $ "f" # "$1" # "x")
        it "should work with operators" do
            parsePretty expression "(_ + x * _ |> f)"
                `shouldBe` Right (lam "$1" $ lam "$2" $ "|>" # ("+" # "$1" # ("*" # "x" # "$2")) # "f")
        it "should scope to the innermost parenthesis" do
            parsePretty expression "(f (_ + _) _ x)"
                `shouldBe` Right (lam "$1" $ "f" # lam "$1" (lam "$2" $ "+" # "$1" # "$2") # "$1" # "x")
        it "records and lists introduce a scope" do
            parsePretty expression "{x = _, y = 0} z"
                `shouldBe` Right (lam "$1" (recordExpr [("x", "$1"), ("y", E.Literal $ intLit 0)]) # "z")
            parsePretty expression "[a, b, c, _, d, _]" `shouldBe` Right (lam "$1" $ lam "$2" $ list ["a", "b", "c", "$1", "d", "$2"])
        it "should require outer parenthesis" do
            parsePretty expression "f _" `shouldSatisfy` isLeft
            parsePretty expression "f _ x" `shouldSatisfy` isLeft

    describe "precedence shenanigans (todo: move to fixity resolution tests)" do
        it "let" do
            parsePretty expression "let x = y; z == w == v" `shouldSatisfy` isLeft
        it "let-let" do
            parsePretty expression "let x = y; let z = w; v"
                `shouldBe` Right (let_ (E.ValueBinding "x" "y") (let_ (E.ValueBinding "z" "w") "v"))
        it "case" do
            parsePretty expression "case x of y -> y == 1 == 2" `shouldSatisfy` isLeft

    describe "misc. builtins" do
        it "list" do
            parsePretty expression "[1, 2, 3]" `shouldBe` Right (list [E.Literal $ intLit 1, E.Literal $ intLit 2, E.Literal $ intLit 3])
        it "record construction" do
            parsePretty expression "{ x = 1, y }" `shouldBe` Right (recordExpr [("x", E.Literal $ intLit 1), ("y", "y")])

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
                    ( T.Function Blank (T.Var "'b") $
                        T.Function Blank (T.Function Blank (T.Var "'a") (T.Var "'b")) $
                            T.Function Blank (T.Application "Maybe" $ T.Var "'a") $
                                T.Var "'b"
                    )
        it "record" do
            parsePretty type' "{ x : Int, y : Int, z : Int }"
                `shouldBe` Right (recordT $ NoExtRow [("x", "Int"), ("y", "Int"), ("z", "Int")])
        it "duplicate record fields" do
            parsePretty type' "{x : Int, y : Bool, x : Text}"
                `shouldBe` Right (recordT $ NoExtRow [("y", "Bool"), ("x", "Int"), ("x", "Text")])
        it "variant" do
            parsePretty type' "['A Int, 'B, 'C Double]"
                `shouldBe` Right (variantT $ NoExtRow [("'A", "Int"), ("'B", "Unit"), ("'C", "Double")])
        it "type variable" do
            parsePretty type' "'var" `shouldBe` Right (T.Var "'var")
        it "forall" do
            parsePretty type' "forall 'a. Maybe 'a" `shouldBe` Right (T.Forall Blank "'a" $ T.Application "Maybe" $ T.Var "'a")
            parsePretty type' "∀ 'a. 'a -> 'a" `shouldBe` Right (T.Forall Blank "'a" $ (T.Var "'a") --> (T.Var "'a"))
        it "exists" do
            parsePretty type' "List (exists 'a. 'a)" `shouldBe` Right ("List" $: (∃) "'a" "'a")
            parsePretty type' "∃'a 'b. 'a -> 'b" `shouldBe` Right ((∃) "'a" $ (∃) "'b" $ "'a" --> "'b")

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