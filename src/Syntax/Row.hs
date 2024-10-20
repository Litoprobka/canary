{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE NoFieldSelectors #-}

module Syntax.Row (OpenName, Row, ExtRow (..), empty, lookup, has, sortedRow, extension, visible, extend, diff, unionWithM) where

import Data.HashMap.Strict qualified as HashMap
import Data.Sequence.NonEmpty (NESeq)
import Data.Sequence.NonEmpty qualified as NESeq
import GHC.IsList qualified (Item, toList)
import Relude hiding (empty)
import CheckerTypes (SimpleName)

type OpenName = SimpleName

newtype Row a
  = Row (HashMap OpenName (NESeq a))
  deriving (Show, Eq, Functor, Foldable, Traversable)

data ExtRow a
  = ExtRow {row :: Row a, _ext :: a}
  | NoExtRow {row :: Row a}
  deriving (Show, Eq, Functor, Foldable, Traversable)

empty :: Row a
empty = Row HashMap.empty

lookup :: OpenName -> Row a -> Maybe a
lookup k (Row fields) = HashMap.lookup k fields <&> NESeq.head

has :: Eq a => OpenName -> a -> Row a -> Bool
has k v = (Just v ==) . lookup k

-- extend { a : Int } { a : Text, b : Int | r }
-- -> { a : Int, a : Text, b : Int | r }
extend :: Row a -> ExtRow a -> ExtRow a
extend row ext = ext{row = row <> ext.row}

-- diff { a : Int, a : Double, b : Text } { a : Unit, b : Text }
-- -> { a : Double }
diff :: Row a -> Row a -> Row a
diff (Row lhs) (Row rhs) = Row $ HashMap.differenceWith dropMatching lhs rhs
 where
  dropMatching lhsSeq rhsSeq = NESeq.nonEmptySeq $ NESeq.drop (NESeq.length rhsSeq) lhsSeq

unionWithM :: Monad m => (a -> a -> m a) -> Row a -> Row a -> m (Row a)
unionWithM f (Row lhs) (Row rhs) = Row <$> sequence (HashMap.unionWith unionSeq (pure <$> lhs) (pure <$> rhs))
 where
  unionSeq pureLhs pureRhs = do
    lhsSeq <- pureLhs
    rhsSeq <- pureRhs
    sequence $ NESeq.zipWith f lhsSeq rhsSeq

extension :: ExtRow a -> Maybe a
extension (ExtRow _ ext) = Just ext
extension (NoExtRow _) = Nothing

visible :: Row a -> [(OpenName, a)]
visible (Row fields) = fields & HashMap.toList & map (second NESeq.head)

sortedRow :: Row a -> [(OpenName, a)]
sortedRow (Row fields) = fields & HashMap.toList & sortOn fst & concatMap \(k, vs) -> (k,) <$> toList vs

instance One (Row a) where
  type OneItem (Row a) = (OpenName, a)
  one = fromList . one

instance IsList (Row a) where
  type Item (Row a) = (OpenName, a)
  fromList = Row . foldl' addField HashMap.empty
   where
    addField fields (k, v) = fields & HashMap.insertWith (flip (<>)) k (NESeq.singleton v)
  toList (Row fields) = fields & HashMap.toList & concatMap \(k, vs) -> (k,) <$> toList vs

-- >>> fromList @(Row Int) [("a", 1), ("a", 2), ("b", 1)] <> fromList @(Row Int) [("b", 4), ("a", 7)]
-- Row (fromList [("a",fromList (1 :| [2,7])),("b",fromList (1 :| [4]))])
instance Semigroup (Row a) where
  Row lhs <> Row rhs = Row $ HashMap.unionWith (<>) lhs rhs
