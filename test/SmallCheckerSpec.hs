{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Redundant bracket" #-}
module SmallCheckerSpec (spec) where

import Data.Text qualified as Text
import Relude hiding (Type)
import SmallChecker
import Test.Hspec
import SmallTestPrelude

infixr 2 -->
(-->) :: Type -> Type -> Type
(-->) = TFn

infixl 1 $$
($$) :: Expr -> Expr -> Expr
($$) = EApp

infixl 3 $:
($:) :: Type -> Type -> Type
($:) = TApp

exprs :: [(Text, Expr)]
exprs =
    [ ("\\x f -> f x", ELambda x' $ ELambda f' $ EApp f x)
    , ("\\x f -> f (f x)", ELambda x' $ ELambda f' $ f $$ EApp f x)
    , ("\\x f -> f x x", ELambda x' $ ELambda f' $ f $$ x $$ x)
    , ("\\f x -> f x", ELambda f' $ ELambda x' $ EApp f x)
    , ("\\f g x -> f (g x)", ELambda f' $ ELambda g' $ ELambda x' $ f $$ EApp g x)
    , ("\\x y -> x (\\a -> x (y a a))", ELambda x' $ ELambda y' $ EApp x $ ELambda a' $ y $$ a $$ a)
    , ("\\a b c -> c (b a) (c a a)", ELambda a' $ ELambda b' $ ELambda c' $ c $$ (b $$ a) $$ (c $$ a $$ a))
    ,
        ( "\\a b -> a (\\x -> b x) (\\z -> a b b) ()"
        , ELambda a' $ ELambda b' $ a $$ ELambda x' (b $$ x) $$ ELambda z' (a $$ b $$ b) $$ "()"
        )
    , ("\\x -> Just x", ELambda x' $ "Just" $$ x)
    , ("\\x -> Just (Just x)", ELambda x' $ "Just" $$ ("Just" $$ x))
    , ("\\x -> Just (Just Nothing)", ELambda x' $ "Just" $$ ("Just" $$ "Nothing"))
    , ("Just", "Just")
    , ( "\\y -> () : forall a. Maybe a -> ()", EAnn (ELambda y' "()") $ TForall a' $ "Maybe" $: a'' --> "()")
    ,
        ( "\\x -> ((\\y -> ()) : forall a. Maybe a -> ()) x"
        , ELambda x' $ EAnn (ELambda y' "()") (TForall a' $ "Maybe" $: a'' --> "()") $$ x
        )
    ]

errorExprs :: [(Text, Expr)]
errorExprs =
    [ ("\\x y z -> z (y x) (x y) (x y ())", ELambda x' $ ELambda y' $ ELambda z' $ z $$ (y $$ x) $$ (x $$ y) $$ (x $$ y $$ "()"))
    , ("\\f x y -> f x (f y)", ELambda f' $ ELambda x' $ ELambda y' $ f $$ x $$ (f $$ y))
    , -- unless we get some magical rank-n inference, this should fail
      ("\\f g -> g (f ()) (f Nothing)", ELambda f' $ ELambda g' $ g $$ EApp f "()" $$ EApp f "Nothing")
    ]

exprsToCheck :: [(Text, Expr, Type)]
exprsToCheck =
    [ ("Nothing : ∀a. Maybe a", "Nothing", TForall a' $ "Maybe" $: a'')
    , ("Nothing : Maybe (∀a. a)", "Nothing", "Maybe" $: TForall a' a'')
    , ("Nothing : Maybe (∃a. a)", "Nothing", "Maybe" $: TExists a' a'')
    , ("() : ∃a. a", "()", TExists a' a'')
    , ("\\x -> () : (∃a. a) -> ()", ELambda x' "()", (TExists a' a'') --> "()")
    , ("\\x -> Just x : (∃a. a -> Maybe ())", ELambda x' $ "Just" $$ x, TExists a' $ a'' --> "Maybe" $: "()")
    , ("\\x -> Just x : (∃a. a -> Maybe a)", ELambda x' $ "Just" $$ x, TExists a' $ a'' --> "Maybe" $: a'')
    , ("\\f -> f () : (∀a. a -> a) -> ()", ELambda f' $ f $$ "()", TForall a' (a'' --> a'') --> "()")
    ,
        ( "\\f g -> g (f ()) (f Nothing) : ∀a. ∀b. (∀c. c -> a) -> (a -> a -> b) -> b"
        , ELambda f' $ ELambda g' $ g $$ EApp f "()" $$ EApp f "Nothing"
        , TForall a' $ TForall b' $ TForall c' (c'' --> a'') --> (a'' --> a'' --> b'') --> b''
        )
    ]

x' = Name "x" 0
y' = Name "y" 0
z' = Name "z" 0
f' = Name "f" 0
g' = Name "g" 0
a' = Name "a" 0
b' = Name "b" 0
c' = Name "c" 0
[x, y, z, f, g, a, b, c] = EName <$> [x', y', z', f', g', a', b', c']
[x'', y'', z'', f'', g'', a'', b'', c''] = TVar <$> [x', y', z', f', g', a', b', c']

spec :: Spec
spec = do
    describe "sanity check" $ for_ exprs \(txt, expr) -> it (Text.unpack txt) do
        runDefault (check expr =<< normalise =<< infer expr) `shouldSatisfy` isRight
    describe "errors" $ for_ errorExprs \(txt, expr) -> it (Text.unpack txt) do
        runDefault (normalise =<< infer expr) `shouldSatisfy` isLeft
    describe "testing check" $ for_ exprsToCheck \(txt, expr, ty) -> it (Text.unpack txt) do
        runDefault (check expr ty) `shouldSatisfy` isRight
