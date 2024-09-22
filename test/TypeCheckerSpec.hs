{-# LANGUAGE OverloadedLists #-}

module TypeCheckerSpec (spec) where

import Data.HashMap.Strict qualified as HashMap
import Data.Text qualified as Text
import Effectful (runPureEff)
import NameGen (runNameGen)
import NameResolution
import Playground
import Prettyprinter hiding (list)
import Prettyprinter.Render.Text (putDoc)
import Relude
import Syntax
import Syntax.Declaration qualified as D
import Syntax.Expression qualified as E
import Syntax.Pattern qualified as P
import Syntax.Row (ExtRow (..))
import Syntax.Type qualified as T
import Test.Hspec
import TypeChecker

-- resolve names, silently discarding the scope errors
resolveSilent env = fmap fst . runNameResolution env

unitE = E.Record []
unitT = T.Record (NoExtRow [])

exprs :: [(Text, Expression Text)]
exprs =
    [ ("\\x f -> f x", λ "x" $ λ "f" $ "f" # "x")
    , ("\\x f -> f (f x)", λ "x" $ λ "f" $ "f" # ("f" # "x"))
    , ("\\x f -> f x x", λ "x" $ λ "f" $ "f" # "x" # "x")
    , ("\\f x -> f x", λ "f" $ λ "x" $ "f" # "x")
    , ("\\f g x -> f (g x)", λ "f" $ λ "g" $ λ "x" $ "f" # ("g" # "x"))
    , ("\\x y -> x (\\a -> x (y a a))", λ "x" $ λ "y" $ "x" # λ "a" ("y" # "a" # "a"))
    , ("\\a b c -> c (b a) (c a a)", λ "a" $ λ "b" $ λ "c" $ "c" # ("b" # "a") # ("c" # "a" # "a"))
    ,
        ( "\\a b -> a (\\x -> b x) (\\z -> a b b) {}"
        , λ "a" $ λ "b" $ "a" # λ "x" ("b" # "x") # λ "z" ("a" # "b" # "b") # unitE
        )
    , ("\\x -> Just x", λ "x" $ "Just" # "x")
    , ("\\x -> Just (Just x)", λ "x" $ "Just" # ("Just" # "x"))
    , ("\\x -> Just (Just Nothing)", λ "x" $ "Just" # ("Just" # "Nothing"))
    , ("Just", "Just")
    , ("\\y -> {} : forall a. Maybe a -> {}", E.Annotation (λ "y" unitE) $ T.Forall "'a" $ "Maybe" $: "'a" --> unitT)
    ,
        ( "\\x -> ((\\y -> {}) : forall a. Maybe a -> {}) x"
        , λ "x" $ E.Annotation (λ "y" unitE) (T.Forall "'a" $ "Maybe" $: "'a" --> unitT) # "x"
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
    , ("\\(x : ∀'a. 'a -> 'a) y -> [x, y]", λ (P.Annotation "x" $ T.Forall "'a" $ "'a" --> "'a") $ λ "y" $ E.List ["x", "y"])
    , ("[id, \\{} -> {}]", E.List ["id", λ (P.Record []) unitE])
    ]

errorExprs :: [(Text, Expression Text)]
errorExprs =
    [
        ( "\\x y z -> z (y x) (x y) (x y {})"
        , λ "x" $ λ "y" $ λ "z" $ "z" # ("y" # "x") # ("x" # "y") # ("x" # "y" # unitE)
        )
    , ("\\f x y -> f x (f y)", λ "f" $ λ "x" $ λ "y" $ "f" # "x" # ("f" # "y"))
    , -- unless we get some magical rank-n inference, this should fail
      ("\\f g -> g (f {}) (f Nothing)", λ "f" $ λ "g" $ "g" # ("f" # unitE) # ("f" # "Nothing"))
    ]

exprsToCheck :: [(Text, Expression Text, Type' Text)]
exprsToCheck =
    [ ("Nothing : ∀a. Maybe a", "Nothing", T.Forall "'a" $ "Maybe" $: "'a")
    , ("Nothing : Maybe (∀a. a)", "Nothing", "Maybe" $: T.Forall "'a" "'a")
    , ("Nothing : Maybe (∃a. a)", "Nothing", "Maybe" $: (∃) "'a" "'a")
    , ("{} : ∃a. a", "Nothing", (∃) "'a" "'a")
    , ("\\x -> {} : (∃a. a) -> {}", λ "x" (E.Record []), (∃) "'a" "'a" --> T.Record (NoExtRow []))
    , ("\\x -> Just x : (∃a. a -> Maybe {})", λ "x" $ "Just" # "x", (∃) "'a" $ "'a" --> "Maybe" $: unitT)
    , ("\\x -> Just x : (∃a. a -> Maybe a)", λ "x" $ "Just" # "x", (∃) "'a" $ "'a" --> "Maybe" $: "'a")
    , ("\\f -> f {} : (∀a. a -> a) -> {}", λ "f" $ "f" # unitE, T.Forall "'a" ("'a" --> "'a") --> unitT)
    ,
        ( "\\f g -> g (f {}) (f Nothing) : ∀a. ∀b. (∀c. c -> a) -> (a -> a -> b) -> b"
        , λ "f" $ λ "g" $ "g" # ("f" # unitE) # ("f" # "Nothing")
        , T.Forall "'a" $ T.Forall "'b" $ T.Forall "'c" ("'c" --> "'a") --> ("'a" --> "'a" --> "'b") --> "'b"
        )
    ]

quickLookExamples :: [(Text, Expression Text)]
quickLookExamples =
    [ ("cons id ids", "cons" # "id" # "ids")
    , ("head (cons id ids)", "head" # ("cons" # "id" # "ids"))
    , ("single id : List (∀a. a -> a)", E.Annotation ("single" # "id") $ list $ T.Forall "'a" $ "'a" --> "'a")
    , ("(\\x -> x) ids)", λ "x" "x" # "ids")
    , ("wikiF (Just reverse)", "wikiF" # ("Just" # "reverse"))
    , ("\\x y -> [x : ∀'a. 'a -> 'a, y]", λ "x" $ λ "y" $ E.List [E.Annotation "x" (T.Forall "'a" $ "'a" --> "'a"), "y"])
    ]

quickLookDefs :: [(Text, Type' Text)]
quickLookDefs =
    [ ("head", T.Forall "'a" $ list "'a" --> "Maybe" $: "'a")
    , ("single", T.Forall "'a" $ "'a" --> list "'a")
    , ("ids", list $ T.Forall "'a" $ "'a" --> "'a")
    ,
        ( "wikiF"
        , "Maybe" $: T.Forall "'a" (list "'a" --> list "'a") --> "Maybe" $: ("Tuple" $: ("List" $: "Int") $: ("List" $: "Char"))
        )
    ]

deepSkolemisation :: [(Text, Expression Text)]
deepSkolemisation =
    [ ("f g", "f" # "g")
    , ("f2 g2", "f2" # "g2")
    ]

dsDefs :: [(Text, Type' Text)]
dsDefs =
    [ ("f", T.Forall "'a" $ T.Forall "'b" $ "'a" --> "'b" --> "'b")
    , ("g", T.Forall "'p" ("'p" --> T.Forall "'q" ("'q" --> "'q")) --> "Int")
    , ("g2", (T.Forall "'a" ("'a" --> "'a") --> "Bool") --> "Text")
    , ("f2", "Int" --> "Int" --> "Bool")
    ]

patterns :: [(Text, Pattern Text)]
patterns =
    [ ("Nothing : Maybe (∀ 'a. 'a)", P.Annotation (con "Nothing" []) (T.Name "Maybe" $: T.Forall "'a" "'a"))
    , ("Just x  : Maybe (∀ 'a. 'a)", P.Annotation (con "Just" ["x"]) (T.Name "Maybe" $: T.Forall "'a" "'a"))
    , ("Just (x : ∀ 'a. 'a -> 'a)", con "Just" [P.Annotation "x" (T.Name "Maybe" $: T.Forall "'a" ("'a" --> "'a"))])
    ]

mutualRecursion :: [[Declaration Text]]
mutualRecursion =
    [
        [ D.Value (E.FunctionBinding "f" ["x", "y"] $ E.Record [("x", "myId" # "x"), ("y", "myId" # "y")]) []
        , D.Value (E.FunctionBinding "myId" ["x"] "x") []
        ]
    ,
        [ D.Value
            (E.FunctionBinding "f" ["double", "cond", "n"] $ E.If ("cond" # "n") "n" ("f" # "double" # "cond" # ("double" # "n")))
            []
        ]
    ,
        [ D.Type "Stack" ["'a"] [("Cons", ["'a", "Stack" $: "'a"]), ("Nil", [])]
        , D.Type "Peano" [] [("S", ["Peano"]), ("Z", [])]
        , D.Value
            ( E.FunctionBinding
                "length"
                ["xs"]
                ( E.Case
                    "xs"
                    [ (con "Cons" ["head", "tail"], "S" # ("length" # "tail"))
                    , (con "Nil" [], "Z")
                    ]
                )
            )
            []
        ]
    ]

list :: Type' Text -> Type' Text
list ty = "List" $: ty

spec :: Spec
spec = do
    describe "sanity check" $ for_ exprs \(txt, expr) ->
        it
            (Text.unpack txt)
            let tcResult = runPureEff $ runNameGen do
                    (scope, builtins, env) <- mkDefaults
                    expr' <- resolveSilent scope $ resolveExpr expr
                    run (Right <$> env) builtins $ check expr' =<< normalise =<< infer expr'
             in tcResult `shouldSatisfy` isRight
    describe "errors" $ for_ errorExprs \(txt, expr) ->
        it
            (Text.unpack txt)
            let tcResult = runPureEff $ runNameGen do
                    (scope, builtins, env) <- mkDefaults
                    expr' <- resolveSilent scope $ resolveExpr expr
                    run (Right <$> env) builtins $ check expr' =<< normalise =<< infer expr'
             in tcResult `shouldSatisfy` isLeft
    describe "testing check" $ for_ exprsToCheck \(txt, expr, ty) ->
        it
            (Text.unpack txt)
            let tcResult = runPureEff $ runNameGen do
                    (scope, builtins, env) <- mkDefaults
                    (expr', ty') <- resolveSilent scope do
                        expr' <- resolveExpr expr
                        ty' <- resolveType ty
                        pure (expr', ty')
                    run (Right <$> env) builtins $ check expr' ty'
             in tcResult `shouldSatisfy` isRight
    describe "quick look-esque impredicativity" $ for_ quickLookExamples \(txt, expr) ->
        it
            (Text.unpack txt)
            let tcResult = runPureEff $ runNameGen do
                    (scope, builtins, env) <- mkDefaults
                    (expr', quickLookDefs') <- resolveSilent scope do
                        expr' <- resolveExpr expr
                        quickLookDefs' <- fromList <$> traverse (\(name, ty) -> liftA2 (,) (declare name) (resolveType ty)) quickLookDefs
                        pure (expr', quickLookDefs')
                    run (fmap Right $ quickLookDefs' <> env) builtins $ check expr' =<< normalise =<< infer expr'
             in tcResult `shouldSatisfy` isRight
    describe "deep subsumption examples" $ for_ deepSkolemisation \(txt, expr) ->
        it
            (Text.unpack txt)
            let tcResult = runPureEff $ runNameGen do
                    (scope, builtins, env) <- mkDefaults
                    (expr', dsDefs') <- resolveSilent scope do
                        expr' <- resolveExpr expr
                        dsDefs' <- fromList <$> traverse (\(name, ty) -> liftA2 (,) (declare name) (resolveType ty)) dsDefs
                        pure (expr', dsDefs')
                    run (fmap Right $ dsDefs' <> env) builtins $ check expr' =<< normalise =<< infer expr'
             in tcResult `shouldSatisfy` isRight
    describe "impredicative patterns" $ for_ patterns \(txt, pat) ->
        it
            (Text.unpack txt)
            let tcResult = runPureEff $ runNameGen do
                    (scope, builtins, env) <- mkDefaults
                    pat' <- resolveSilent scope $ declarePat pat
                    run (Right <$> env) builtins $ inferPattern pat'
             in tcResult `shouldSatisfy` isRight
    describe "mutual recursion" $ for_ mutualRecursion \decls ->
        it
            "decls"
            let tcResult = runPureEff $ runNameGen do
                    (scope, builtins, env) <- mkDefaults
                    resolvedDecls <- fst <$> resolveNames scope decls
                    typecheck env builtins resolvedDecls
             in do
                    {- case tcResult of
                        Left _ -> pass
                        Right checkedBindings -> putDoc $ sep $ pretty . uncurry D.Signature <$> HashMap.toList checkedBindings
                    -}
                    tcResult `shouldSatisfy` isRight
