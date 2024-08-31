module SmallCheckerSpec (spec) where

import SmallChecker
import Relude
import Test.Hspec
import Data.Text qualified as Text

id' :: Expr
id' = ELambda x (EName x)
  where
    x = Name "x" 0

exprs, errorExprs :: [(Text, Expr)]
(exprs, errorExprs) = (exprs', errorExprs') where
    exprs' =
      [ ("\\x f -> f x", ELambda x' $ ELambda f' $ EApp f x)
      , ("\\x f -> f (f x)", ELambda x' $ ELambda f' $ f `EApp` (EApp f x))
      , ("\\x f -> f x x", ELambda x' $ ELambda f' $ f `EApp` x `EApp` x)
      , ("\\f x -> f x", ELambda f' $ ELambda x' $ EApp f x)
      , ("\\f g x -> f (g x)", ELambda f' $ ELambda g' $ ELambda x' $ f `EApp` (g `EApp` x))
      , ("\\x y -> x (\\a -> x (y a a))", ELambda x' $ ELambda y' $ EApp x $ ELambda a' $ y `EApp` a `EApp` a)
      , ("\\a b c -> c (b a) (c a a)", ELambda a' $ ELambda b' $ ELambda c' $ c `EApp` (b `EApp` a) `EApp` (c `EApp` a `EApp` a))
      , ("\\a b -> a (\\x -> b x) (\\z -> a b b) ()", ELambda a' $ ELambda b' $ a `EApp` (ELambda x' $ b `EApp` x) `EApp` (ELambda z' $ a `EApp` b `EApp` b) `EApp` EUnit)
      ]
    errorExprs' =
      [ ("\\x y z -> z (y x) (x y) (x y ())", ELambda x' $ ELambda y' $ ELambda z' $ z `EApp` (y `EApp` x) `EApp` (x `EApp` y) `EApp` (x `EApp` y `EApp` EUnit))
      , ("\\f x y -> f x (f y)", ELambda f' $ ELambda x' $ ELambda y' $ f `EApp` x `EApp` (f `EApp` y))
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

spec :: Spec
spec = do
    describe "sanity check" $ for_ exprs \(txt, expr) -> it (Text.unpack txt) do
        run (check expr =<< normalise =<< infer expr) `shouldSatisfy` isRight
    describe "errors" $ for_ errorExprs \(txt, expr) -> it (Text.unpack txt) do
        run (normalise =<< infer expr) `shouldSatisfy` isLeft


    