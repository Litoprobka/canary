{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}

module Infix where

import CheckerTypes (Name, getLoc, zipLoc)
import Control.Monad (foldM)
import Data.HashMap.Strict qualified as HashMap
import Data.HashSet qualified as HashSet
import Data.List.NonEmpty qualified as NE
import Effectful (Eff, runPureEff, (:>))
import Effectful.Error.Static (Error, runErrorNoCallStack, throwError)
import Effectful.Reader.Static (Reader, ask, runReader)
import Playground ()
import Relude hiding (Op, Reader, ask, runReader)
import Syntax (Expression)
import Syntax.Expression qualified as E

newtype EqClass = EqClass Int deriving (Show, Eq, Hashable)

type PriorityGraph = HashMap EqClass (HashSet EqClass)
type OpMap = HashMap Name (Fixity, EqClass)

data Fixity = InfixL | InfixR | InfixChain | Infix deriving (Eq)

data Priority = Left' | Right' deriving (Show)

type Ctx es = (Reader OpMap :> es, Reader PriorityGraph :> es, Error Text :> es)

lookup' :: (Error Text :> es, Hashable k) => k -> HashMap k v -> Eff es v
lookup' key hmap = case HashMap.lookup key hmap of
    Nothing -> throwError @Text "missing operator"
    Just v -> pure v

priority :: Ctx es => Name -> Name -> Eff es Priority
priority prev next = do
    graph <- ask @PriorityGraph
    opMap <- ask @OpMap
    (prevFixity, prevEq) <- lookup' prev opMap
    prevHigherThan <- lookup' prevEq graph
    (nextFixity, nextEq) <- lookup' next opMap
    nextHigherThan <- lookup' nextEq graph
    if
        | prev == next && prevFixity == InfixChain -> pure Left'
        | prevEq == nextEq -> case (prevFixity, nextFixity) of
            (InfixL, InfixL) -> pure Left'
            (InfixR, InfixR) -> pure Right'
            _ -> throwError @Text $ "incompatible fixity of " <> show prev <> " and " <> show next
        | HashSet.member nextEq prevHigherThan -> pure Left'
        | HashSet.member prevEq nextHigherThan -> pure Right'
        | otherwise -> throwError @Text $ "undefined ordering of " <> show prev <> " and " <> show next

parse :: [(Expression Name, Name)] -> Expression Name -> Either Text (Expression Name)
parse pairs last' = runPureEff . runErrorNoCallStack . runReader testOpMap . runReader testGraph $ go [] pairs
  where
    go :: Ctx es => [(Expression Name, Name)] -> [(Expression Name, Name)] -> Eff es (Expression Name)
    go [] [] = pure last'
    go ((x, op) : rest) [] = do
        last'' <- appOrMerge op x last'
        foldM (\acc (z, op') -> appOrMerge op' z acc) last'' rest
    go [] ((x, op) : rest) = go [(x, op)] rest
    go ((x, prev) : stack) ((y, next) : rest) = do
        newStack <- pop (y, next) ((x, prev) :| stack)
        go newStack rest

    pop :: Ctx es => (Expression Name, Name) -> NonEmpty (Expression Name, Name) -> Eff es [(Expression Name, Name)]
    pop (y, next) ((x, prev) :| stack) =
        priority prev next >>= \case
            Right' -> pure ((y, next) : (x, prev) : stack)
            Left' -> do
                newX <- appOrMerge prev x y
                case NE.nonEmpty stack of
                    Nothing -> pure [(newX, next)]
                    Just stack' -> pop (newX, next) stack'

    appOrMerge :: Ctx es => Name -> Expression Name -> Expression Name -> Eff es (Expression Name)
    appOrMerge op lhs rhs = do
        opMap <- ask @OpMap
        (fixity, _) <- lookup' op opMap
        let loc = zipLoc (getLoc lhs) (getLoc rhs)
        pure case (fixity, lhs) of
            (InfixChain, E.Application _ (E.Name op') (E.List _ args))
                | op == op' ->
                    E.Application loc (E.Name op') (E.List loc $ args <> [rhs])
            (InfixChain, _) -> E.Application loc (E.Name op) $ E.List loc [lhs, rhs]
            _ -> E.Application loc (E.Application loc (E.Name op) lhs) rhs

testOpMap :: OpMap
testOpMap =
    HashMap.fromList
        [ ("+", (InfixL, EqClass 0))
        , ("*", (InfixL, EqClass 1))
        , ("?", (InfixR, EqClass 2))
        , ("^", (InfixR, EqClass 3))
        , ("==", (InfixChain, EqClass 4))
        ]

testGraph :: PriorityGraph
testGraph =
    HashMap.fromList
        [ (EqClass 3, HashSet.fromList [EqClass 0, EqClass 1, EqClass 2, EqClass 4])
        , (EqClass 2, HashSet.fromList [EqClass 0, EqClass 4])
        , (EqClass 1, HashSet.fromList [EqClass 0, EqClass 4])
        , (EqClass 0, HashSet.fromList [EqClass 4])
        , (EqClass 4, HashSet.fromList [])
        ]