{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE NoFieldSelectors #-}

module Syntax.Row (
    OpenName,
    Row,
    ExtRow (..),
    empty,
    lookup,
    has,
    sortedRow,
    extension,
    visible,
    extend,
    diff,
    unionWithM,
    zipRows,
    indexDuplicates,
    isEmpty,
) where

import Common (SimpleName)
import Data.HashMap.Strict qualified as HashMap
import Data.Sequence.NonEmpty (NESeq)
import Data.Sequence.NonEmpty qualified as NESeq
import GHC.IsList qualified as IsList
import Relude hiding (empty)

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

isEmpty :: Row a -> Bool
isEmpty (Row fields) = HashMap.null fields

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

-- convert two rows into a row of matching fields,
-- a row of fields present only in the first and only in the second rows
zipRows :: Row a -> Row b -> (Row (a, b), Row a, Row b)
zipRows (Row lhs) (Row rhs) =
    (\(both, l, r) -> (Row both, Row l, Row r)) $
        ( HashMap.intersectionWith f lhs rhs & \isect ->
            ( fst3 <$> isect
            , HashMap.mapMaybe (NESeq.nonEmptySeq . snd3) isect
            , HashMap.mapMaybe (NESeq.nonEmptySeq . thd) isect
            )
        )
            <> (mempty, HashMap.difference lhs rhs, mempty)
            <> (mempty, mempty, HashMap.difference rhs lhs)
  where
    f seq1 seq2 =
        ( NESeq.zip seq1 seq2
        , NESeq.drop (NESeq.length seq2) seq1
        , NESeq.drop (NESeq.length seq1) seq2
        )
    fst3 (x, _, _) = x
    snd3 (_, x, _) = x
    thd (_, _, x) = x

extension :: ExtRow a -> Maybe a
extension (ExtRow _ ext) = Just ext
extension (NoExtRow _) = Nothing

visible :: Row a -> [(OpenName, a)]
visible (Row fields) = fields & HashMap.toList & map (second NESeq.head)

indexDuplicates :: Row a -> [(OpenName, (Int, a))]
indexDuplicates (Row fields) = fields & HashMap.toList >>= \(key, s) -> (key,) <$> zip [0 ..] (toList s)

-- fromIndexed :: [(OpenName, (Int, a))] -> Row a
-- fromIndexed = Row . fmap (NESeq.fromList . fmap snd . NE.sortOn fst) . HashMap.fromListWith (<>) . map (second (:| []))

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
