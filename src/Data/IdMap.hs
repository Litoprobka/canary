module Data.IdMap where

import Relude hiding (null, toList)

import Data.Foldable qualified as Foldable
import Data.IntMap.Strict qualified as IntMap

-- todo: strict tuples

-- | a newtype wrapper of IntMap for keys that have a lossy but 1-to-1 conversion to Int
newtype IdMap k v = IdMap (IntMap (k, v)) deriving (Show, Functor, Foldable, Traversable, Semigroup, Monoid)

class HasId k where
    toId :: k -> Int

empty :: IdMap k v
empty = IdMap IntMap.empty

null :: IdMap k v -> Bool
null (IdMap idmap) = IntMap.null idmap

insert :: HasId k => k -> v -> IdMap k v -> IdMap k v
insert !k v (IdMap idmap) = IdMap $ IntMap.insert (toId k) (k, v) idmap

lookup :: HasId k => k -> IdMap k v -> Maybe v
lookup !k (IdMap idmap) = snd <$> IntMap.lookup (toId k) idmap

lookupDefault :: HasId k => v -> k -> IdMap k v -> v
lookupDefault def !k (IdMap idmap) = snd $ IntMap.findWithDefault (k, def) (toId k) idmap

one :: HasId k => k -> v -> IdMap k v
one !k v = IdMap $ IntMap.singleton (toId k) (k, v)

toList :: IdMap k v -> [(k, v)]
toList (IdMap idmap) = Foldable.toList idmap

fromList :: HasId k => [(k, v)] -> IdMap k v
fromList pairs = IdMap . IntMap.fromList $ map (\(k, v) -> (toId k, (k, v))) pairs

delete :: HasId k => k -> IdMap k v -> IdMap k v
delete !k (IdMap idmap) = IdMap $ IntMap.delete (toId k) idmap

filter :: (v -> Bool) -> IdMap k v -> IdMap k v
filter p (IdMap idmap) = IdMap $ IntMap.filter (p . snd) idmap

adjust :: HasId k => (v -> v) -> k -> IdMap k v -> IdMap k v
adjust f !k (IdMap idmap) = IdMap $ IntMap.adjust (second f) (toId k) idmap

update :: HasId k => (v -> Maybe v) -> k -> IdMap k v -> IdMap k v
update f !k (IdMap idmap) = IdMap $ IntMap.update (traverse f) (toId k) idmap

mapWithKey :: (k -> a -> b) -> IdMap k a -> IdMap k b
mapWithKey f (IdMap idmap) = IdMap $ IntMap.map (\(k, v) -> (k, f k v)) idmap

mapMaybe :: (a -> Maybe b) -> IdMap k a -> Maybe (IdMap k b)
mapMaybe f (IdMap idmap) = guarded (not . null) . IdMap $ IntMap.mapMaybe (\(k, v) -> (k,) <$> f v) idmap

keys :: IdMap k v -> [k]
keys = map fst . toList

merge :: (a -> b -> c) -> (a -> c) -> (b -> c) -> IdMap k a -> IdMap k b -> IdMap k c
merge both onlyA onlyB (IdMap as) (IdMap bs) = IdMap $ IntMap.mergeWithKey (\_ (k, a) (_, b) -> Just (k, both a b)) ((fmap . fmap) onlyA) ((fmap . fmap) onlyB) as bs

unionWith :: (a -> a -> a) -> IdMap k a -> IdMap k a -> IdMap k a
unionWith f (IdMap lhs) (IdMap rhs) = IdMap $ IntMap.unionWith (\(k, l) (_, r) -> (k, f l r)) lhs rhs
