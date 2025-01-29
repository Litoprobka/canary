{-# HLINT ignore "Functor law" #-}
{-# OPTIONS_GHC -Wno-missing-export-lists #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module Poset where

import Common (Loc (Blank))
import Data.HashMap.Strict qualified as HashMap
import Data.HashSet qualified as HashSet
import Data.Sequence qualified as Seq
import Diagnostic (Diagnose, internalError)
import Effectful.Error.Static (Error, runErrorNoCallStack, throwError)
import Effectful.Writer.Static.Local (Writer, tell)
import LangPrelude hiding (cycle)
import Relude.Extra (traverseToSnd)

-- a partially ordered set implementation with an emphasis on equality
-- items are stored as equivalence classes and strict > relations between them

newtype EqClass a = EqClass Int deriving (Show, Eq, Enum, Hashable, Pretty)

data Cycle a = Cycle (EqClass a) (EqClass a)

data PosetError = forall key. Pretty key => LookupError key

type Ctx es = Error PosetError :> es
type CycleWarnings a es = Writer (Seq (Cycle a)) :> es
type CycleErrors a es = Error (Cycle a) :> es

data Poset a = Poset
    { nextClass :: EqClass a
    , classes :: HashMap a (EqClass a)
    , relations :: HashMap (EqClass a) (HashSet (EqClass a))
    }

empty :: Poset a
empty =
    Poset
        { nextClass = EqClass 0
        , classes = HashMap.empty
        , relations = HashMap.empty
        }

lookup' :: (Error PosetError :> es, Hashable k, Pretty k) => k -> HashMap k v -> Eff es v
lookup' k hmap = maybe (throwError $ LookupError k) pure $ HashMap.lookup k hmap

-- | merge two equivalence classes. Error out if there was a relation between them
mergeStrict :: (Ctx es, CycleErrors a es) => Hashable a => EqClass a -> EqClass a -> Poset a -> Eff es (Poset a)
mergeStrict l r = mergeWith (const $ throwError $ Cycle l r) l r

-- | merge two equvalience classes. If the classes already have a GT / LT relation, add a relation in the other direction instead
mergeLenient :: (Ctx es, CycleWarnings a es, Hashable a) => EqClass a -> EqClass a -> Poset a -> Eff es (Poset a)
mergeLenient l r poset =
    mergeWith
        (const $ (addRelationLenient' l r GT poset >>= addRelationLenient' l r LT) <* tell (Seq.singleton $ Cycle l r))
        l
        r
        poset

-- | merge two equivalence classes. If it causes a cycle, merge the whole cycle into one class
mergeRec :: (Ctx es, Hashable a) => EqClass a -> EqClass a -> Poset a -> Eff es (Poset a)
mergeRec l r poset = mergeWith handleCycle l r poset
  where
    handleCycle posetWithCycle = do
        inCycleL <- inCycle l r
        inCycleR <- inCycle r l
        foldlM (\acc cl -> mergeRec cl r acc) posetWithCycle $ inCycleL <> inCycleR
    inCycle higher lower =
        lookup' higher poset.relations
            <&> HashSet.toList
                >>= traverse (traverseToSnd $ flip lookup' poset.relations)
            <&> filter (HashSet.member lower . snd)
            <&> map fst
            <&> HashSet.fromList

{- | merge two equivalence classes by moving all items to the right one
O(n) in class count
-}
mergeWith
    :: (Error PosetError :> es, Hashable a)
    => (Poset a -> Eff es (Poset a)) -- a callback that's called in case of a cycle
    -> EqClass a
    -> EqClass a
    -> Poset a
    -> Eff es (Poset a)
mergeWith onCycle classL classR Poset{classes, relations, nextClass} = do
    lhsGreaterThan <- lookup' classL relations
    rhsGreaterThan <- lookup' classR relations
    let cycle = HashSet.member classL rhsGreaterThan || HashSet.member classR lhsGreaterThan
        newPoset = Poset{classes = newClasses, relations = newRelations, nextClass}
        newClasses = (classR <$ lhsClassElems) <> classes
        newRelations = preserveTransitivity . replaceOldClass <$> HashMap.delete classL relations
        replaceOldClass hset
            | HashSet.member classL hset = HashSet.delete classL $ (rhsGreaterThan <>) $ HashSet.insert classR hset
            | HashSet.member classR hset = lhsGreaterThan <> hset
            | otherwise = hset
        preserveTransitivity hset
            | HashSet.member classR hset = lhsGreaterThan <> rhsGreaterThan <> hset
            | otherwise = hset
        lhsClassElems = HashMap.filter (== classL) classes
    if cycle
        then onCycle newPoset
        else pure newPoset

-- | add a relation between two classes, erroring out in case of a cycle
addGtRel :: (Ctx es, CycleErrors a es) => EqClass a -> EqClass a -> Poset a -> Eff es (Poset a)
addGtRel l r = addGreaterThanRel (const $ throwError $ Cycle l r) l r

-- | add a relation between two classes; merge them if the relation causes a cycle (i.e. A > B and B > A)
addGteRel :: (Ctx es, Hashable a) => a -> a -> Poset a -> Eff es (Poset a)
addGteRel lhs rhs poset =
    let (lhsClass, poset') = eqClass lhs poset
        (rhsClass, poset'') = eqClass rhs poset'
     in addGteRel' lhsClass rhsClass poset''

addGteRel' :: (Ctx es, Hashable a) => EqClass a -> EqClass a -> Poset a -> Eff es (Poset a)
addGteRel' l r poset = addGreaterThanRel (const $ mergeRec l r poset) l r poset

{- | add a relation between two classes, preserving transitivity
O(n) in class count
-}
addGreaterThanRel
    :: Error PosetError :> es
    => (Poset a -> Eff es (Poset a))
    -- ^ a callback that's called in case of a cycle
    -> EqClass a
    -> EqClass a
    -> Poset a
    -> Eff es (Poset a)
addGreaterThanRel onCycle greaterClass lesserClass poset = do
    lesserClassBiggerThan <- lookup' lesserClass poset.relations
    let newRels = HashSet.insert lesserClass lesserClassBiggerThan
    if HashSet.member greaterClass lesserClassBiggerThan
        then onCycle poset{relations = relations newRels}
        else pure poset{relations = relations newRels}
  where
    relations newRels = addTransitiveRels newRels <$> HashMap.adjust (<> newRels) greaterClass poset.relations
    addTransitiveRels newRels hset
        | HashSet.member greaterClass hset = hset <> newRels
        | otherwise = hset

-- | add a strict relation between the classes of two items - that is, classes may not be merged if they form a cycle
addRelationStrict
    :: (Ctx es, CycleErrors a es, Hashable a) => a -> a -> Ordering -> Poset a -> Eff es (Poset a)
addRelationStrict lhs rhs order poset =
    let (lhsClass, poset') = eqClass lhs poset
        (rhsClass, poset'') = eqClass rhs poset'
     in addRelationStrict' lhsClass rhsClass order poset''

-- | add a strict relation between two classes - that is, classes may not be merged if they form a cycle
addRelationStrict'
    :: (Ctx es, CycleErrors a es, Hashable a) => EqClass a -> EqClass a -> Ordering -> Poset a -> Eff es (Poset a)
addRelationStrict' lhs rhs = \case
    EQ -> mergeStrict lhs rhs
    GT -> addGtRel lhs rhs
    LT -> addGtRel rhs lhs

-- | add a GTE / LTE relation between the classes of two items. Ignores class cycles
addRelationLenient
    :: (Ctx es, CycleWarnings a es, Hashable a) => a -> a -> Ordering -> Poset a -> Eff es (Poset a)
addRelationLenient lhs rhs order poset =
    let (lhsClass, poset') = eqClass lhs poset
        (rhsClass, poset'') = eqClass rhs poset'
     in addRelationLenient' lhsClass rhsClass order poset''

-- | add a GTE / LTE relation between two classes. Ignores class cycles
addRelationLenient'
    :: (Ctx es, CycleWarnings a es, Hashable a) => EqClass a -> EqClass a -> Ordering -> Poset a -> Eff es (Poset a)
addRelationLenient' lhs rhs = \case
    EQ -> mergeLenient lhs rhs
    GT -> addGreaterThanRel warnOnCycle lhs rhs
    LT -> addGreaterThanRel warnOnCycle rhs lhs
  where
    warnOnCycle = (<$ tell (Seq.singleton $ Cycle lhs rhs))

-- add an item to a fresh equivalence class. If it belonged to a different equality class, it gets moved
newClass :: Hashable a => a -> Poset a -> (EqClass a, Poset a)
newClass x Poset{nextClass, classes, relations} =
    ( nextClass
    , Poset
        { nextClass = succ nextClass
        , classes = HashMap.insert x nextClass classes
        , relations = HashMap.insert nextClass HashSet.empty relations
        }
    )

-- get the equivalence class of an item; create a new class if the item didn't have one
eqClass :: Hashable a => a -> Poset a -> (EqClass a, Poset a)
eqClass x poset = case HashMap.lookup x poset.classes of
    Just class_ -> (class_, poset)
    Nothing -> newClass x poset

items :: EqClass a -> Poset a -> [a]
items cl poset = map fst . filter ((== cl) . snd) $ HashMap.toList poset.classes

data PosetOrdering
    = DefinedOrder Ordering
    | NoOrder
    | AmbiguousOrder
    deriving (Eq, Show)

-- find out the relation between two poset items
relation :: (Ctx es, Pretty a, Hashable a) => a -> a -> Poset a -> Eff es PosetOrdering
relation lhs rhs poset = do
    lhsClass <- lookup' lhs poset.classes
    rhsClass <- lookup' rhs poset.classes
    classRelation lhsClass rhsClass poset

classRelation :: Ctx es => EqClass a -> EqClass a -> Poset a -> Eff es PosetOrdering
classRelation lhsClass rhsClass poset = do
    lhsGreaterThan <- lookup' lhsClass poset.relations
    rhsGreaterThan <- lookup' rhsClass poset.relations
    pure case (HashSet.member rhsClass lhsGreaterThan, HashSet.member lhsClass rhsGreaterThan) of
        _ | lhsClass == rhsClass -> DefinedOrder EQ
        (True, False) -> DefinedOrder GT
        (False, True) -> DefinedOrder LT
        (True, True) -> AmbiguousOrder
        (False, False) -> NoOrder

-- convert a poset to a list of equivalence classes, lowest to highest
-- the order of uncomparable elements is not guaranteed
ordered :: Poset a -> [[a]]
ordered p@Poset{relations} = map (`items` p) $ sortBy cmp (HashMap.keys relations)
  where
    cmp l r = case runPureEff $ runErrorNoCallStack @PosetError $ classRelation l r p of
        Right (DefinedOrder order) -> order
        _ -> EQ

-- poset indexing errors should not ever happen, unless you misuse keys from one poset for the other
-- so throwing an internal error is good enough in most cases
reportError :: Diagnose :> es => Eff (Error PosetError : es) a -> Eff es a
reportError = runErrorNoCallStack @PosetError >=> either asDiagnoseError pure
  where
    asDiagnoseError (Poset.LookupError key) = internalError Blank $ "invalid poset key" <+> pretty key
