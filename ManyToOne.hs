{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE NoFieldSelectors #-}

module ManyToOne where

import qualified Data.HashMap.Strict as HashMap
import Relude

newtype Id = Id Int deriving (Show, Eq, Hashable, Enum)

data ManyToOne k v = ManyToOne
    { nextId :: Id
    , keyToId :: HashMap k Id
    , idToValue :: HashMap Id (Int, v)
    }

insert :: Hashable k => k -> v -> ManyToOne k v -> ManyToOne k v
insert k v ManyToOne{nextId, keyToId, idToValue} =
    ManyToOne
        { nextId = succ nextId
        , keyToId = HashMap.insert k nextId keyToId
        , idToValue = HashMap.insert nextId (1, v) idToValue
        }

insertMany :: Hashable k => [k] -> v -> ManyToOne k v -> ManyToOne k v
insertMany keys v mtv =
    mtv
        { nextId = succ mtv.nextId
        , keyToId = foldr (`HashMap.insert` mtv.nextId) mtv.keyToId keys
        , idToValue = HashMap.insert mtv.nextId (1, v) mtv.idToValue
        }

addKey :: Hashable k => k -> k -> ManyToOne k v -> ManyToOne k v
addKey newKey oldKey mtv = case lookupId oldKey mtv of
    Nothing -> mtv
    Just id' ->
        mtv
            { keyToId = HashMap.insert newKey id' mtv.keyToId
            }

{-
mergeKeys :: Hashable k => (v -> v -> v) -> k -> k -> ManyToOne k v -> ManyToOne k v
mergeKeys f k1 k2 mtv = case (lookupId k1 mtv, lookupId k2 mtv) of
    (Just id1, Just id2)
        | id1 == id2 -> mtv
        | otherwise -> mtv
            { idToValue = mtv.idToValue & HashMap.delete id2 & HashMap.adjust id1
            }
-}

deleteKey :: Hashable k => k -> ManyToOne k v -> ManyToOne k v
deleteKey k mtv =
    mtv
        { keyToId = HashMap.delete k mtv.keyToId
        , idToValue = case lookupId k mtv of
            Nothing -> mtv.idToValue
            Just id' -> HashMap.alter (>>= decRefCount) id' mtv.idToValue
        }
  where
    decRefCount (1, _) = Nothing
    decRefCount v = Just v

deleteValue :: Hashable k => k -> ManyToOne k v -> ManyToOne k v
deleteValue k mtv = case lookupId k mtv of
    Nothing -> mtv
    Just id' ->
        mtv
            { keyToId = HashMap.filter (/= id') mtv.keyToId
            , idToValue = HashMap.delete id' mtv.idToValue
            }

lookup :: Hashable k => k -> ManyToOne k v -> Maybe v
lookup k mtv =
    lookupId k mtv
        >>= flip HashMap.lookup mtv.idToValue
        <&> snd

lookupId :: Hashable k => k -> ManyToOne k v -> Maybe Id
lookupId k mtv = HashMap.lookup k mtv.keyToId
