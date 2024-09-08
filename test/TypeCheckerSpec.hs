{-# LANGUAGE OverloadedLists #-}

module TypeCheckerSpec (spec) where

import Data.Text qualified as Text
import Relude
import TypeChecker
import Playground
import Test.Hspec
import Syntax hiding (Name)
import Syntax.Expression qualified as E
import Syntax.Type qualified as T
import CheckerTypes

exprs :: [(Text, Expression Name)]
exprs =
    [ ("\\x f -> f x", λ "x" $ λ "f" $ "f" # "x")
    , ("\\x f -> f (f x)", λ "x" $ λ "f" $ "f" # ("f" # "x"))
    , ("\\x f -> f x x", λ "x" $ λ "f" $ "f" # "x" # "x")
    , ("\\f x -> f x", λ "f" $ λ "x" $ "f" # "x")
    , ("\\f g x -> f (g x)", λ "f" $ λ "g" $ λ "x" $ "f" # ("g" # "x"))
    , ("\\x y -> x (\\a -> x (y a a))", λ "x" $ λ "y" $ "x" # λ "a" ("y" # "a" # "a"))
    , ("\\a b c -> c (b a) (c a a)", λ "a" $ λ "b" $ λ "c" $ "c" # ("b" # "a") # ("c" # "a" # "a"))
    ,
        ( "\\a b -> a (\\x -> b x) (\\z -> a b b) ()"
        , λ "a" $ λ "b" $ "a" # λ "x" ("b" # "x") # λ "z" ("a" # "b" # "b") # "()"
        )
    , ("\\x -> Just x", λ "x" $ "Just" # "x")
    , ("\\x -> Just (Just x)", λ "x" $ "Just" # ("Just" # "x"))
    , ("\\x -> Just (Just Nothing)", λ "x" $ "Just" # ("Just" # "Nothing"))
    , ("Just", "Just")
    , ("\\y -> () : forall a. Maybe a -> ()", E.Annotation (λ "y" "()") $ T.Forall "'a" $ "Maybe" $: "'a" --> "Unit")
    ,
        ( "\\x -> ((\\y -> ()) : forall a. Maybe a -> ()) x"
        , λ "x" $ E.Annotation (λ "y" "()") (T.Forall "'a" $ "Maybe" $: "'a" --> "Unit") # "x"
        )
    , ("\\(Just x) -> x", λ (con "Just" ["x"]) "x")
    ,
        ( "\\def mb -> case mb of { Nothing -> def; Just x -> x }"
        , λ "def" $ λ "mb" $ E.Case "mb" [("Nothing", "def"), (con "Just" ["x"], "x")]
        )
    ,
        ( "\\cond -> case cond of { True -> id; False -> reverse }"
        , λ "cond" $ E.Case "cond" [("True", "id"), ("False", "reverse")]
        )
    , ("\\cond -> if cond then id else reverse", λ "cond" $ E.If "cond" "id" "reverse")
    , ("\\x y -> [x, y]", λ "x" $ λ "y" $ E.List ["x", "y"])
    , ("\\x y -> [x : ∀'a. 'a -> 'a, y]", λ "x" $ λ "y" $ E.List [E.Annotation "x" (T.Forall "'a" $ "'a" --> "'a"), "y"])
    , ("[id, \\() -> ()]", E.List ["id", λ (con "()" []) "()"])
    ]

errorExprs :: [(Text, Expression Name)]
errorExprs =
    [
        ( "\\x y z -> z (y x) (x y) (x y ())"
        , λ "x" $ λ "y" $ λ "z" $ "z" # ("y" # "x") # ("x" # "y") # ("x" # "y" # "()")
        )
    , ("\\f x y -> f x (f y)", λ "f" $ λ "x" $ λ "y" $ "f" # "x" # ("f" # "y"))
    , -- unless we get some magical rank-n inference, this should fail
      ("\\f g -> g (f ()) (f Nothing)", λ "f" $ λ "g" $ "g" # ("f" # "()") # ("f" # "Nothing"))
    ]

exprsToCheck :: [(Text, Expression Name, Type' Name)]
exprsToCheck =
    [ ("Nothing : ∀a. Maybe a", "Nothing", T.Forall "'a" $ "Maybe" $: "'a")
    , ("Nothing : Maybe (∀a. a)", "Nothing", "Maybe" $: T.Forall "'a" "'a")
    , ("Nothing : Maybe (∃a. a)", "Nothing", "Maybe" $: (∃) "'a" "'a")
    , ("() : ∃a. a", "()", (∃) "'a" "'a")
    , ("\\x -> () : (∃a. a) -> ()", λ "x" "()", (∃) "'a" "'a" --> "Unit")
    , ("\\x -> Just x : (∃a. a -> Maybe ())", λ "x" $ "Just" # "x", (∃) "'a" $ "'a" --> "Maybe" $: "Unit")
    , ("\\x -> Just x : (∃a. a -> Maybe a)", λ "x" $ "Just" # "x", (∃) "'a" $ "'a" --> "Maybe" $: "'a")
    , ("\\f -> f () : (∀a. a -> a) -> ()", λ "f" $ "f" # "()", T.Forall "'a" ("'a" --> "'a") --> "Unit")
    ,
        ( "\\f g -> g (f ()) (f Nothing) : ∀a. ∀b. (∀c. c -> a) -> (a -> a -> b) -> b"
        , λ "f" $ λ "g" $ "g" # ("f" # "()") # ("f" # "Nothing")
        , T.Forall "'a" $ T.Forall "'b" $ T.Forall "'c" ("'c" --> "'a") --> ("'a" --> "'a" --> "'b") --> "'b"
        )
    ]

quickLookExamples :: [(Text, Expression Name)]
quickLookExamples =
    [ ("cons id ids", "cons" # "id" # "ids")
    , ("head (cons id ids)", "head" # ("cons" # "id" # "ids"))
    , ("single id : List (∀a. a -> a)", E.Annotation ("single" # "id") $ list $ T.Forall "'a" $ "'a" --> "'a")
    , ("(\\x -> x) ids)", λ "x" "x" # "ids")
    , ("wikiF (Just reverse)", "wikiF" # ("Just" # "reverse"))
    ]

quickLookDefs :: HashMap Name (Type' Name)
quickLookDefs =
    defaultEnv
        <> fromList
            [ ("head", T.Forall "'a" $ list "'a" --> "Maybe" $: "'a")
            , ("single", T.Forall "'a" $ "'a" --> list "'a")
            , ("ids", list $ T.Forall "'a" $ "'a" --> "'a")
            , ("wikiF", "Maybe" $: T.Forall "'a" (list "'a" --> list "'a") --> "Maybe" $: ("Tuple" $: ("List" $: "Int") $: ("List" $: "Char")))
            ]

list :: Type' Name -> Type' Name
list ty = "List" $: ty

spec :: Spec
spec = do
    describe "sanity check" $ for_ exprs \(txt, expr) -> it (Text.unpack txt) do
        runDefault (check expr =<< normalise =<< infer expr) `shouldSatisfy` isRight
    describe "errors" $ for_ errorExprs \(txt, expr) -> it (Text.unpack txt) do
        runDefault (normalise =<< infer expr) `shouldSatisfy` isLeft
    describe "testing check" $ for_ exprsToCheck \(txt, expr, ty) -> it (Text.unpack txt) do
        runDefault (check expr ty) `shouldSatisfy` isRight
    describe "quick look-esque impredicativity" $ for_ quickLookExamples \(txt, expr) -> it (Text.unpack txt) do
        run quickLookDefs (check expr =<< normalise =<< infer expr) `shouldSatisfy` isRight
