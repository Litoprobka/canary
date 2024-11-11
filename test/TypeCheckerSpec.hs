{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedLists #-}

module TypeCheckerSpec (spec) where

import Common
import Data.Text qualified as Text
import Diagnostic (runDiagnose')
import Effectful (runPureEff)
import Fixity (resolveFixity, testGraph, testOpMap)
import LensyUniplate
import NameGen
import NameResolution
import Playground
import Prettyprinter hiding (list)
import Relude hiding (State)
import Syntax
import Syntax.Expression qualified as E
import Syntax.Pattern qualified as P
import Syntax.Row (ExtRow (..))
import Syntax.Type qualified as T
import Test.Hspec
import TypeChecker

unitE = E.Record Blank []
unitT = T.Record Blank (NoExtRow [])
forall_ = T.Forall Blank

exprs :: [(Text, Expression 'Parse)]
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
    , ("\\y -> {} : forall a. Maybe a -> {}", E.Annotation (λ "y" unitE) $ forall_ "'a" $ "Maybe" $: "'a" --> unitT)
    ,
        ( "\\x -> ((\\y -> {}) : forall a. Maybe a -> {}) x"
        , λ "x" $ E.Annotation (λ "y" unitE) (forall_ "'a" $ "Maybe" $: "'a" --> unitT) # "x"
        )
    , ("\\(Just x) -> x", λ (con "Just" ["x"]) "x")
    ,
        ( "\\def mb -> case mb of { Nothing -> def; Just x -> x }"
        , λ "def" $ λ "mb" $ case_ "mb" [("Nothing", "def"), (con "Just" ["x"], "x")]
        )
    ,
        ( "\\cond -> case cond of { True -> id; False -> reverse }"
        , λ "cond" $ case_ "cond" [("True", "id"), ("False", "reverse")]
        )
    , ("\\cond -> if cond then id else reverse", λ "cond" $ if_ "cond" "id" "reverse")
    , ("\\x y -> [x, y]", λ "x" $ λ "y" $ list ["x", "y"])
    , ("\\(x : ∀'a. 'a -> 'a) y -> [x, y]", λ (P.Annotation "x" $ forall_ "'a" $ "'a" --> "'a") $ λ "y" $ list ["x", "y"])
    , ("[id, \\{} -> {}]", list ["id", λ (P.Record Blank []) unitE])
    ]

errorExprs :: [(Text, Expression 'Parse)]
errorExprs =
    [
        ( "\\x y z -> z (y x) (x y) (x y {})"
        , λ "x" $ λ "y" $ λ "z" $ "z" # ("y" # "x") # ("x" # "y") # ("x" # "y" # unitE)
        )
    , ("\\f x y -> f x (f y)", λ "f" $ λ "x" $ λ "y" $ "f" # "x" # ("f" # "y"))
    , -- unless we get some magical rank-n inference, this should fail
      ("\\f g -> g (f {}) (f Nothing)", λ "f" $ λ "g" $ "g" # ("f" # unitE) # ("f" # "Nothing"))
    ]

exprsToCheck :: [(Text, Expression 'Parse, Type' 'Parse)]
exprsToCheck =
    [ ("Nothing : ∀a. Maybe a", "Nothing", forall_ "'a" $ "Maybe" $: "'a")
    , ("Nothing : Maybe (∀a. a)", "Nothing", "Maybe" $: forall_ "'a" "'a")
    , ("Nothing : Maybe (∃a. a)", "Nothing", "Maybe" $: (∃) "'a" "'a")
    , ("{} : ∃a. a", "Nothing", (∃) "'a" "'a")
    , ("\\x -> {} : (∃a. a) -> {}", λ "x" (recordExpr []), (∃) "'a" "'a" --> unitT)
    , ("\\x -> Just x : (∃a. a -> Maybe {})", λ "x" $ "Just" # "x", (∃) "'a" $ "'a" --> "Maybe" $: unitT)
    , ("\\x -> Just x : (∃a. a -> Maybe a)", λ "x" $ "Just" # "x", (∃) "'a" $ "'a" --> "Maybe" $: "'a")
    , ("\\f -> f {} : (∀a. a -> a) -> {}", λ "f" $ "f" # unitE, forall_ "'a" ("'a" --> "'a") --> unitT)
    ,
        ( "\\f g -> g (f {}) (f Nothing) : ∀a. ∀b. (∀c. c -> a) -> (a -> a -> b) -> b"
        , λ "f" $ λ "g" $ "g" # ("f" # unitE) # ("f" # "Nothing")
        , forall_ "'a" $ forall_ "'b" $ forall_ "'c" ("'c" --> "'a") --> ("'a" --> "'a" --> "'b") --> "'b"
        )
    , ("[1, []] : List (∃a. a)", list [E.Literal $ intLit 1, list []], "List" $: T.Exists Blank "'a" "'a")
    ]

quickLookExamples :: [(Text, Expression 'Parse)]
quickLookExamples =
    [ ("cons id ids", "cons" # "id" # "ids")
    , ("head (cons id ids)", "head" # ("cons" # "id" # "ids"))
    , ("single id : List (∀a. a -> a)", E.Annotation ("single" # "id") $ listTy $ forall_ "'a" $ "'a" --> "'a")
    , ("(\\x -> x) ids)", λ "x" "x" # "ids")
    , ("wikiF (Just reverse)", "wikiF" # ("Just" # "reverse"))
    , ("\\x y -> [x : ∀'a. 'a -> 'a, y]", λ "x" $ λ "y" $ list [E.Annotation "x" (forall_ "'a" $ "'a" --> "'a"), "y"])
    ]

quickLookDefs :: [(SimpleName, Type' 'Parse)]
quickLookDefs =
    [ ("head", forall_ "'a" $ listTy "'a" --> "Maybe" $: "'a")
    , ("single", forall_ "'a" $ "'a" --> listTy "'a")
    , ("ids", listTy $ forall_ "'a" $ "'a" --> "'a")
    ,
        ( "wikiF"
        , "Maybe" $: forall_ "'a" (listTy "'a" --> listTy "'a") --> "Maybe" $: ("Tuple" $: ("List" $: "Int") $: ("List" $: "Char"))
        )
    ]

deepSkolemisation :: [(Text, Expression 'Parse)]
deepSkolemisation =
    [ ("f g", "f" # "g")
    , ("f2 g2", "f2" # "g2")
    ]

dsDefs :: [(SimpleName, Type' 'Parse)]
dsDefs =
    [ ("f", forall_ "'a" $ forall_ "'b" $ "'a" --> "'b" --> "'b")
    , ("g", forall_ "'p" ("'p" --> forall_ "'q" ("'q" --> "'q")) --> "Int")
    , ("g2", (forall_ "'a" ("'a" --> "'a") --> "Bool") --> "Text")
    , ("f2", "Int" --> "Int" --> "Bool")
    ]

patterns :: [(Text, Pattern 'Parse)]
patterns =
    [ ("Nothing : Maybe (∀ 'a. 'a)", P.Annotation (con "Nothing" []) (T.Name "Maybe" $: forall_ "'a" "'a"))
    , ("Just x  : Maybe (∀ 'a. 'a)", P.Annotation (con "Just" ["x"]) (T.Name "Maybe" $: forall_ "'a" "'a"))
    , ("Just (x : ∀ 'a. 'a -> 'a)", con "Just" [P.Annotation "x" (T.Name "Maybe" $: forall_ "'a" ("'a" --> "'a"))])
    ]

mutualRecursion :: [(Text, [Declaration 'Parse])]
mutualRecursion =
    [
        ( "f and myId"
        ,
            [ valueDec (E.FunctionBinding "f" ["x", "y"] $ recordExpr [("x", "myId" # "x"), ("y", "myId" # "y")]) []
            , valueDec (E.FunctionBinding "myId" ["x"] "x") []
            ]
        )
    ,
        ( "f double cond n"
        ,
            [ valueDec
                (E.FunctionBinding "f" ["double", "cond", "n"] $ if_ ("cond" # "n") "n" ("f" # "double" # "cond" # ("double" # "n")))
                []
            ]
        )
    ,
        ( "length"
        ,
            [ typeDec "Stack" ["'a"] [conDec "Cons" ["'a", "Stack" $: "'a"], conDec "Nil" []]
            , typeDec "Peano" [] [conDec "S" ["Peano"], conDec "Z" []]
            , valueDec
                ( E.FunctionBinding
                    "length"
                    ["xs"]
                    ( case_
                        "xs"
                        [ (con "Cons" ["head", "tail"], "S" # ("length" # "tail"))
                        , (con "Nil" [], "Z")
                        ]
                    )
                )
                []
            ]
        )
    ,
        ( "xs and os (mutual recursion)"
        ,
            [ valueDec (E.ValueBinding "xs" $ "Cons" # E.Literal (intLit 0) # "os") []
            , valueDec (E.ValueBinding "os" $ "Cons" # E.Literal (intLit 1) # "xs") []
            , typeDec "Stack" ["'a"] [conDec "Cons" ["'a", "Stack" $: "'a"], conDec "Nil" []]
            ]
        )
    ]

listTy :: Type' 'Parse -> Type' 'Parse
listTy ty = "List" $: ty

spec :: Spec
spec = do
    describe "sanity check" $ for_ exprs \(txt, expr) ->
        it
            (Text.unpack txt)
            let tcResult =
                    testCheck
                        (dummyFixity =<< resolveExpr expr)
                        (\expr' ->  infer expr' & normalise >>= check expr' . cast uniplateCast)
             in tcResult `shouldSatisfy` isJust
    describe "errors" $ for_ errorExprs \(txt, expr) ->
        it
            (Text.unpack txt)
            let tcResult =
                    testCheck
                        (dummyFixity =<< resolveExpr expr)
                        (\expr' -> infer expr' & normalise >>= check expr' . cast uniplateCast)
             in tcResult `shouldSatisfy` isNothing
    describe "testing check" $ for_ exprsToCheck \(txt, expr, ty) ->
        it
            (Text.unpack txt)
            let tcResult =
                    testCheck
                        ( do
                            expr' <- dummyFixity =<< resolveExpr expr
                            ty' <- cast uniplateCast <$> resolveType ty
                            pure (expr', ty')
                        )
                        (uncurry check)
             in tcResult `shouldSatisfy` isJust
    describe "quick look-esque impredicativity" $ for_ quickLookExamples \(txt, expr) ->
        it
            (Text.unpack txt)
            let tcResult = fst $ runPureEff $ runDiagnose' ("<none>", "") $ runNameGen do
                    (scope, builtins, env) <- mkDefaults
                    (expr', quickLookDefs') <- runNameResolution scope do
                        expr' <- dummyFixity =<< resolveExpr expr
                        quickLookDefs' <-
                            fromList <$> traverse (\(name, ty) -> liftA2 (,) (declare name) (cast uniplateCast <$> resolveType ty)) quickLookDefs
                        pure (expr', quickLookDefs')
                    run (fmap Right $ quickLookDefs' <> env) builtins $ check expr' . cast uniplateCast =<< normalise (infer expr')
             in tcResult `shouldSatisfy` isJust
    describe "deep subsumption examples" $ for_ deepSkolemisation \(txt, expr) ->
        it
            (Text.unpack txt)
            let tcResult = fst $ runPureEff $ runDiagnose' ("<none>", "") $ runNameGen do
                    (scope, builtins, env) <- mkDefaults
                    (expr', dsDefs') <- runNameResolution scope do
                        expr' <- dummyFixity =<< resolveExpr expr
                        dsDefs' <- fromList <$> traverse (\(name, ty) -> liftA2 (,) (declare name) (cast uniplateCast <$> resolveType ty)) dsDefs
                        pure (expr', dsDefs')
                    run (fmap Right $ dsDefs' <> env) builtins $ check expr' . cast uniplateCast =<< normalise (infer expr')
             in tcResult `shouldSatisfy` isJust
    describe "impredicative patterns" $ for_ patterns \(txt, pat) ->
        it
            (Text.unpack txt)
            let tcResult =
                    testCheck
                        (cast uniplateCast <$> declarePat pat)
                        inferPattern
             in tcResult `shouldSatisfy` isJust
    describe "mutual recursion" $ for_ mutualRecursion \(name, decls) ->
        it
            (toString name)
            let tcResult = fst $ runPureEff $ runDiagnose' ("<none>", "") $ runNameGen do
                    (scope, builtins, env) <- mkDefaults
                    resolvedDecls <- resolveFixity testOpMap testGraph =<< runNameResolution scope (resolveNames decls)
                    typecheck env builtins resolvedDecls
             in do
                    {- case tcResult of
                        Left _ -> pass
                        Right checkedBindings -> putDoc $ sep $ pretty . uncurry D.Signature <$> HashMap.toList checkedBindings
                    -}
                    tcResult `shouldSatisfy` isJust
