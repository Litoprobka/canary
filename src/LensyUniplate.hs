{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}

module LensyUniplate (
    Traversal,
    Traversal',
    SelfTraversal,
    transform,
    transformM,
    transform',
    transformM',
    transformInsideOut,
    cast,
    UniplateCast (..),
    unicast,
    para,
) where

import LangPrelude
import Relude.Monad (State, get, modify)

-- long story short, `uniplate` has a shitty interface and `lens` is too heavyweight

type Traversal s t a b = forall f. Applicative f => (a -> f b) -> (s -> f t)
type Traversal' s a = Traversal s s a a
type SelfTraversal s a b = Traversal (s a) (s b) (s a) (s b)

-- this is basically `over`, but recursive
transform :: Traversal' a a -> (a -> a) -> a -> a
transform trav f = f . runIdentity . trav (Identity . transform trav f)

-- type-changing version of transform with an option to short-circuit
transform' :: Traversal a b a b -> (a -> Either b a) -> a -> b
transform' trav f = runIdentity . transformM' trav (Identity . f)

-- apply a type-changing self-traversal
cast :: Traversal a b a b -> a -> b
cast trav = transform' trav Right

transformM :: Monad m => Traversal' a a -> (a -> m a) -> a -> m a
transformM trav f = f >=> trav (transformM trav f)

-- inside-out applicative version of transform
transformInsideOut :: Monad m => Traversal' a a -> (a -> m a) -> a -> m a
transformInsideOut trav f = f <=< trav (transformM trav f)

-- outside-in transform with an option to short-circuit
transformM' :: Monad m => Traversal a b a b -> (a -> m (Either b a)) -> a -> m b
transformM' trav f = f >=> either pure (trav $ transformM' trav f)

-- fold via a self-traversal
para :: Traversal' a a -> (a -> [r] -> r) -> a -> r
para trav f x = f x (para trav f <$> toListOf trav x)

toListOf :: Traversal' s a -> s -> [a]
toListOf trav = getConst . trav \x -> Const [x]

-- a type-changing self-traversal
class UniplateCast from to where
    uniplateCast :: Traversal from to from to

-- cast a value from one type to another using its UniplateCast instance
unicast :: UniplateCast from to => from -> to
unicast = cast uniplateCast

-- usage examples

data Tree a = Leaf a | Branch (Tree a) (Tree a) deriving (Show)

travTree :: (a -> b) -> SelfTraversal Tree a b
travTree f recur = \case
    Leaf x -> pure $ Leaf $ f x
    Branch lhs rhs -> Branch <$> recur lhs <*> recur rhs

travTree' :: SelfTraversal Tree a a
travTree' = travTree id

example = Branch (Branch (Leaf @Int 15) (Leaf 20)) (Branch (Leaf 40) (Leaf 50))

-- >>> transform travTree' (mapLeaf (*2)) example
-- Branch (Branch (Leaf 30) (Leaf 40)) (Branch (Leaf 80) (Leaf 100))

-- >>> transform travTree' (mapLeaf (*2)) (Leaf 333)
-- Leaf 666

-- >>> transform' (travTree id) (Right . mapLeaf (*2)) example
-- Branch (Branch (Leaf 30) (Leaf 40)) (Branch (Leaf 80) (Leaf 100))

-- >>> transform' (travTree id) (Right . mapLeaf (*2)) (Leaf 333)
-- Leaf 666
mapLeaf f = \case
    Leaf x -> Leaf (f x)
    branch -> branch

-- >>> flip runState 0 $ transformM travTree' iterLeaves example
-- (Branch (Branch (Leaf 1) (Leaf 2)) (Branch (Leaf 3) (Leaf 4)),4)

-- >>> flip runState 0 $ transformM' travTree' (fmap Left . iterLeaves) example
-- (Branch (Branch (Leaf 15) (Leaf 20)) (Branch (Leaf 40) (Leaf 50)),0)

-- >>> flip runState 0 $ transformM' travTree' (fmap Left . iterLeaves) (Leaf 333)
-- (Leaf 1,1)

-- >>> flip runState 0 $ transformM' travTree' (fmap Right . iterLeaves) example
-- (Branch (Branch (Leaf 1) (Leaf 2)) (Branch (Leaf 3) (Leaf 4)),4)
iterLeaves :: Tree Integer -> State Integer (Tree Integer)
iterLeaves = appLeaf $ const do
    modify (+ 1)
    get
appLeaf f = \case
    Leaf x -> Leaf <$> f x
    branch -> pure branch

-- >>> flip runState 0 $ transformM' travTree' iterEvens example
-- (Branch (Branch (Leaf 1) (Leaf 2)) (Branch (Leaf 40) (Leaf 50)),2)
iterEvens :: Tree Integer -> State Integer (Either (Tree Integer) (Tree Integer))
iterEvens = \case
    Leaf _ -> modify (+ 1) >> Right . Leaf <$> get
    b@(Branch (Leaf x) _)
        | even x -> pure $ Left b
    branch -> pure $ Right branch

-- >>> para travTree' (\x xs -> sum (getLeaf x ++ xs)) example
-- 125
-- >>> para travTree' (\x xs -> getLeaf x ++ xs) example
getLeaf :: Tree a -> [a]
getLeaf (Leaf x) = [x]
getLeaf _ = []
