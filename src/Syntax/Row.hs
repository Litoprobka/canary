{-# LANGUAGE TypeFamilies #-}

module Syntax.Row (OpenName, Row, empty, lookup, has) where

import Data.HashMap.Strict qualified as HashMap
import Data.Sequence.NonEmpty (NESeq)
import Data.Sequence.NonEmpty qualified as NESeq
import GHC.IsList qualified (Item, toList)
import Relude hiding (empty)

type OpenName = Text

-- row extensions are TBD
newtype Row a
    = Row (HashMap OpenName (NESeq a))
    deriving (Show, Eq, Functor, Foldable, Traversable)

empty :: Row a
empty = Row HashMap.empty

lookup :: OpenName -> Row a -> Maybe a
lookup k (Row fields) = HashMap.lookup k fields <&> NESeq.head

has :: Eq a => OpenName -> a -> Row a -> Bool
has k v = (Just v ==) . lookup k

instance IsList (Row a) where
    type Item (Row a) = (OpenName, a)
    fromList = Row . foldl' addField HashMap.empty
      where
        addField fields (k, v) = fields & HashMap.insertWith (flip (<>)) k (NESeq.singleton v)
    toList (Row fields) = fields & HashMap.toList & concatMap \(k, vs) -> (k,) <$> toList vs
