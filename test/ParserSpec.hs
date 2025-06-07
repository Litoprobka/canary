{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE QuasiQuotes #-}

module ParserSpec (spec) where

import Data.Traversable (for)
import FlatParse.Stateful qualified as FP
import Lexer
import NeatInterpolation
import Parser
import Playground
import Prettyprinter (Pretty, pretty)
import Proto (eof, parse)
import Relude hiding (readFile)
import Syntax.Row (ExtRow (..))
import Syntax.Row qualified as Row
import Syntax.Term (Pattern_ (..))
import Syntax.Term qualified as E
import System.Directory.OsPath
import System.File.OsPath
import System.OsPath
import Test.Hspec

parsePretty :: Parser' a -> Text -> Either String a
parsePretty parser input =
    lexedInput
        & parse (parser <* eof)
        & first show
  where
    inputBS = encodeUtf8 input
    lexedInput =
        let tokens = case lex' 0 inputBS of
                FP.OK result _ _ -> result
                _ -> []
         in mkTokenStream ("test", inputBS) tokens

shouldBePretty :: (HasCallStack, Show a, Pretty b, Eq a) => Either a b -> Either a b -> Expectation
shouldBePretty = shouldBe `on` second (show @String . pretty)

spec :: Spec
spec = do
    describe "small definitions" do
        it "simple binding" do
            parsePretty code "x = 15" `shouldBePretty` Right [valueDec (E.ValueB "x" (literal_ $ intLit 15)) []]
        it "function definition" do
            parsePretty code "f x = y" `shouldBePretty` Right [valueDec (E.FunctionB "f" ["x"] "y") []]
        it "application" do
            parsePretty code "f = g x y" `shouldBePretty` Right [valueDec (E.ValueB "f" $ infixApp ["g", "x", "y"]) []]
        it "identifiers may contain keywords" do
            parsePretty term "matcher case1 diff" `shouldBePretty` Right (infixApp ["matcher", "case1", "diff"])

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
                            (E.ValueB "f" "x")
                            [ valueDec (E.ValueB "x" (literal_ $ intLit 2)) []
                            ]
                        ]
            parsePretty code program `shouldBePretty` result
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
            parsePretty term expr `shouldBePretty` Right (infixApp ["f", "x", "y", "z"])
        it "with operators" do
            let expr =
                    [text|
                    x
                      |> f
                      |> g
                    |]
            parsePretty term expr `shouldBePretty` Right (noLoc $ E.InfixE [("x", Just "|>"), ("f", Just "|>")] "g")

    describe "let" do
        it "inline" do
            parsePretty term "let x = y; z" `shouldBePretty` Right (let_ (E.ValueB "x" "y") "z")
        it "nested" do
            let expr =
                    [text|
                    let x = y
                    let z = x
                    z
                    |]
            parsePretty term expr `shouldBePretty` Right (let_ (E.ValueB "x" "y") $ let_ (E.ValueB "z" "x") "z")

    describe "if-then-else" do
        it "simple" do
            parsePretty term "if True then \"yes\" else \"huh???\""
                `shouldBePretty` Right (if_ "True" (literal_ $ textLit "yes") (literal_ $ textLit "huh???"))
        it "nested" do
            parsePretty term "if if True then False else True then 1 else 0"
                `shouldBePretty` Right (if_ (if_ "True" "False" "True") (literal_ $ intLit 1) (literal_ $ intLit 0))
        -- resolving implicit lambdas in the parser is messy
        xit "(todo) partially applied" do
            parsePretty term "(if _ then A else B)" `shouldBePretty` Right (lam "$1" $ if_ "$1" "A" "B")
        it "with operators" do
            parsePretty term "x + if y || z then 4 else 5 * 2"
                `shouldBePretty` Right
                    (binApp "+" "x" $ if_ (binApp "||" "y" "z") (literal_ $ intLit 4) (binApp "*" (literal_ $ intLit 5) (literal_ $ intLit 2)))

    describe "pattern matching" do
        it "pattern" do
            parsePretty pattern' "Cons x (Cons y (Cons z xs))"
                `shouldBePretty` Right (con "Cons" ["x", con "Cons" ["y", con "Cons" ["z", "xs"]]])
        it "int literal" do
            parsePretty pattern' "123" `shouldBePretty` Right (noLoc $ LiteralP $ intLit 123)
        it "many patterns" do
            parsePretty (some patternParens) "(Cons x xs) y ('Hmmm z)"
                `shouldBePretty` Right [con "Cons" ["x", "xs"], "y", noLoc $ VariantP "'Hmmm" "z"]
        it "annotation pattern" do
            parsePretty pattern' "(Cons x xs : List Int)"
                `shouldBePretty` Right (noLoc $ AnnotationP (con "Cons" ["x", "xs"]) ("List" $: "Int"))
        it "record" do
            parsePretty pattern' "{ x = x, y = y, z = z }" `shouldBePretty` Right (recordP [("x", "x"), ("y", "y"), ("z", "z")])
        it "record with implicit names" do
            parsePretty pattern' "{ x, y, z }" `shouldBePretty` Right (recordP [("x", "x"), ("y", "y"), ("z", "z")])
        it "list" do
            parsePretty pattern' "[1, 'a', Just x]"
                `shouldBePretty` Right (listP [noLoc $ LiteralP $ intLit 1, noLoc $ LiteralP $ charLit "a", con "Just" ["x"]])
        it "nested lists" do
            parsePretty pattern' "[x, [y, z], [[w], []]]"
                `shouldBePretty` Right (listP ["x", listP ["y", "z"], listP [listP ["w"], listP []]])
        it "case expression" do
            let expr =
                    [text|
                    case list of
                      Cons x xs -> Yes
                      Nil -> No
                    |]
            parsePretty term expr
                `shouldBePretty` Right (case_ "list" [(con "Cons" ["x", "xs"], "Yes"), (con "Nil" [], "No")])
        it "nested case" do
            let expr =
                    [text|
                    case list of
                        Cons x xs -> case x of
                            Just _  -> Cons True xs
                            Nothing -> Cons False xs
                        Nil -> Nil`import yourmom from`
                    |]
            let result =
                    Right $
                        case_
                            "list"
                            [
                                ( con "Cons" ["x", "xs"]
                                , case_
                                    "x"
                                    [ (con "Just" ["_"], infixApp ["Cons", "True", "xs"])
                                    , (con "Nothing" [], infixApp ["Cons", "False", "xs"])
                                    ]
                                )
                            , (con "Nil" [], "Nil")
                            ]
            parsePretty term expr `shouldBePretty` result
        it "match expression" do
            let expr =
                    [text|
                    match
                        Nothing -> Nothing
                        (Just x) -> Just (f x)
                    |]
            parsePretty term expr
                `shouldBePretty` Right (match [([con "Nothing" []], "Nothing"), ([con "Just" ["x"]], "Just" # ("f" # "x"))])
        it "inline match" do
            parsePretty term "match 42 -> True; _ -> False"
                `shouldBePretty` Right (match [([noLoc $ LiteralP $ intLit 42], "True"), ([noLoc $ VarP "_"], "False")])
        xit "match in parens" do
            let expr =
                    [text|
                    f (match
                         42 -> True
                         _ -> False)
                      x
                    |]
            parsePretty term expr
                `shouldBePretty` Right ("f" # match [([noLoc $ LiteralP $ intLit 42], "True"), ([noLoc $ VarP "_"], "False")] # "x")
        it "multi-arg match" do
            let expr =
                    [text|
                    match
                        Nothing (Just x) y -> case1
                        x Nothing y -> case2
                        Nothing Nothing (Just y) -> case3
                    |]
            parsePretty term expr
                `shouldBePretty` Right
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
            parsePretty term expr
                `shouldBePretty` Right (match [([noLoc $ VariantP "'None" (recordP [])], "Nothing"), ([noLoc $ VariantP "'Some" "x"], "Just" # "x")])
        xit "guard clauses (todo)" do
            let expr =
                    [text|
                    match
                        Nothing
                            | guess == True -> Just guess
                            | otherwise = Nothing
                        Just x = Just x
                    |]
            parsePretty term expr `shouldSatisfy` isRight

    xdescribe "implicit lambdas with wildcards" do
        it "(f _ x)" do
            parsePretty term "(f _ x)" `shouldBePretty` Right (lam "$1" $ "f" # "$1" # "x")
        it "should work with operators" do
            parsePretty term "(_ + x * _ |> f)"
                `shouldBePretty` Right (lam "$1" $ lam "$2" $ "|>" # ("+" # "$1" # ("*" # "x" # "$2")) # "f")
        it "should scope to the innermost parenthesis" do
            parsePretty term "(f (_ + _) _ x)"
                `shouldBePretty` Right (lam "$1" $ "f" # lam "$1" (lam "$2" $ "+" # "$1" # "$2") # "$1" # "x")
        it "records and lists introduce a scope" do
            parsePretty term "{x = _, y = 0} z"
                `shouldBePretty` Right (lam "$1" (recordExpr [("x", "$1"), ("y", literal_ $ intLit 0)]) # "z")
            parsePretty term "[a, b, c, _, d, _]" `shouldBePretty` Right (lam "$1" $ lam "$2" $ list ["a", "b", "c", "$1", "d", "$2"])
        it "should require outer parenthesis" do
            parsePretty term "f _" `shouldSatisfy` isLeft
            parsePretty term "f _ x" `shouldSatisfy` isLeft

    xdescribe "precedence shenanigans (todo: move to fixity resolution tests)" do
        it "let" do
            parsePretty term "let x = y; z == w == v" `shouldSatisfy` isLeft
        it "let-let" do
            parsePretty term "let x = y; let z = w; v"
                `shouldBePretty` Right (let_ (E.ValueB "x" "y") (let_ (E.ValueB "z" "w") "v"))
        it "case" do
            parsePretty term "case x of y -> y == 1 == 2" `shouldSatisfy` isLeft
        it "precedence" do
            parsePretty term "x + y * z / w" `shouldBePretty` Right (binApp "+" "x" (binApp "/" (binApp "*" "y" "z") "w"))
        it "lens composition binds tighter than function application" do
            parsePretty term "f x . y" `shouldBePretty` Right ("f" # binApp "." "x" "y")
        it "if-then-else" do
            parsePretty term "if cond then 1 else 2 == 3 == 4" `shouldSatisfy` isLeft

    describe "misc. builtins" do
        it "list" do
            parsePretty term "[1, 2, 3]" `shouldBePretty` Right (list [literal_ $ intLit 1, literal_ $ intLit 2, literal_ $ intLit 3])
        it "record construction" do
            parsePretty term "{ x = 1, y }" `shouldBePretty` Right (recordExpr [("x", literal_ $ intLit 1), ("y", "y")])

    describe "operators" do
        it "2 + 2" do
            parsePretty term "x + x" `shouldBePretty` Right (binApp "+" "x" "x")

    describe "types" do
        it "simple" do
            parsePretty term "ThisIsAType" `shouldBePretty` Right "ThisIsAType"
        it "type application" do
            parsePretty term "Either (List Int) Text"
                `shouldBePretty` Right (infixApp ["Either", "List" $: "Int", "Text"])
        it "function type" do
            parsePretty term "'b -> ('a -> 'b) -> Maybe 'a -> 'b"
                `shouldBePretty` Right
                    ( (-->) "'b" $
                        (-->) ("'a" --> "'b") $
                            (-->) (($:) "Maybe" $ "'a") $
                                "'b"
                    )
        it "record" do
            parsePretty term "{ x : Int, y : Int, z : Int }"
                `shouldBePretty` Right (recordT $ NoExtRow [("x", "Int"), ("y", "Int"), ("z", "Int")])
        it "duplicate record fields" do
            parsePretty term "{x : Int, y : Bool, x : Text}"
                `shouldBePretty` Right (recordT $ NoExtRow [("y", "Bool"), ("x", "Int"), ("x", "Text")])
        it "variant" do
            parsePretty term "['A Int, 'B, 'C Double]"
                `shouldBePretty` Right (variantT $ NoExtRow [("'A", "Int"), ("'B", recordT (NoExtRow Row.empty)), ("'C", "Double")])
        it "type variable" do
            parsePretty term "'var" `shouldBePretty` Right "'var"
        it "forall" do
            parsePretty term "forall 'a. Maybe 'a" `shouldBePretty` Right (forall_ "'a" $ ($:) "Maybe" "'a")
            parsePretty term "∀ 'a. 'a -> 'a" `shouldBePretty` Right (forall_ "'a" $ "'a" --> "'a")
        it "exists" do
            parsePretty term "List (exists 'a. 'a)" `shouldBePretty` Right ("List" $: (∃) "'a" "'a")
            parsePretty term "∃'a 'b. 'a -> 'b" `shouldBePretty` Right ((∃) "'a" $ (∃) "'b" $ "'a" --> "'b")

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
        join $
            sequenceA_ <$> runIO do
                let testDir = [osp|./lang-tests/should-compile|]
                fileNames <- listDirectory testDir
                for fileNames \file -> do
                    fileContents <- decodeUtf8 <$> readFile (testDir </> file)
                    pure $ it (show $ takeFileName file) (parsePretty code fileContents `shouldSatisfy` isRight)
