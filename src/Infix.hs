{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}

module Infix where

import Data.HashMap.Strict qualified as HashMap
import Data.HashSet qualified as HashSet
import Effectful (Eff, (:>), runPureEff)
import Effectful.Error.Static (Error, throwError, runErrorNoCallStack)
import Effectful.Reader.Static (Reader, ask, runReader)
import Relude hiding (Op, Reader, ask, runReader)
import qualified Data.List.NonEmpty as NE
import qualified Data.Sequence as Seq
import Control.Monad (foldM)

newtype EqClass = EqClass Int deriving (Show, Eq, Hashable)

type PriorityGraph = HashMap EqClass (HashSet EqClass)
type OpMap = HashMap Text (Fixity, EqClass)

data Fixity = InfixL | InfixR | InfixChain | Infix deriving (Eq)

data Priority = Left' | Right' deriving (Show)

data TokenList = Op Text Int TokenList | Term Int

data AST = Term' Int | Op' Text AST AST | Chain Text (Seq AST) deriving (Show)

prettyAst :: AST -> Text
prettyAst (Term' n) = show n
prettyAst (Op' op lhs rhs) = "(" <> prettyAst lhs <> " " <> op <> " " <> prettyAst rhs <> ")"
prettyAst (Chain op args) = "((" <> op <> ")" <> foldMap ((" " <>) . prettyAst) args <> ")"

type Ctx es = (Reader OpMap :> es, Reader PriorityGraph :> es, Error Text :> es)

lookup' :: (Ctx es, Hashable k) => k -> HashMap k v -> Eff es v
lookup' key hmap = case HashMap.lookup key hmap of
    Nothing -> throwError @Text "missing operator"
    Just v -> pure v

priority :: Ctx es => Text -> Text -> Eff es Priority
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
            _ -> throwError @Text $ "incompatible fixity of " <> prev <> " and " <> next
        | HashSet.member nextEq prevHigherThan -> pure Left'
        | HashSet.member prevEq nextHigherThan -> pure Right'
        | otherwise -> throwError @Text $ "undefined ordering of " <> prev <> " and " <> next

parse :: TokenList -> Either Text AST
parse = runPureEff . runErrorNoCallStack . runReader testOpMap . runReader testGraph . go []
  where
    go :: Ctx es => [(AST, Text)] -> TokenList -> Eff es AST
    go [] (Term y) = pure $ Term' y
    go ((x, op) : rest) (Term y) = do
        last' <- opOrMerge op x $ Term' y
        foldM (\acc (z, op') -> opOrMerge op' z acc) last' rest
    go [] (Op op x rest) = go [(Term' x, op)] rest
    go ((x, prev) : stack) (Op next y rest) = do
        newStack <- pop (Term' y, next) ((x, prev) :| stack)
        go newStack rest


    pop :: Ctx es => (AST, Text) -> NonEmpty (AST, Text) -> Eff es [(AST, Text)]
    pop (y, next) ((x, prev) :| stack) =
        priority prev next >>= \case
            Right' -> pure ((y, next) : (x, prev) : stack)
            Left' -> do
                newX <- opOrMerge prev x y
                case NE.nonEmpty stack of
                    Nothing -> pure [(newX, next)]
                    Just stack' -> pop (newX, next) stack'

    opOrMerge :: Ctx es => Text -> AST -> AST -> Eff es AST
    opOrMerge op lhs rhs = do
        opMap <- ask @OpMap
        (fixity, _) <- lookup' op opMap
        pure case (fixity, lhs) of
            (InfixChain, Chain op' args) | op == op' -> Chain op $ args Seq.|> rhs
            (InfixChain, _) -> Chain op $ Seq.fromList [lhs, rhs]
            _ -> Op' op lhs rhs


testOpMap :: OpMap
testOpMap = HashMap.fromList
    [ ("+", (InfixL, EqClass 0))
    , ("*", (InfixL, EqClass 1))
    , ("?", (InfixR, EqClass 2))
    , ("^", (InfixR, EqClass 3))
    , ("==", (InfixChain, EqClass 4))
    ]

testGraph :: PriorityGraph
testGraph = HashMap.fromList
    [ (EqClass 3, HashSet.fromList [EqClass 0, EqClass 1, EqClass 2, EqClass 4])
    , (EqClass 2, HashSet.fromList [EqClass 0, EqClass 4])
    , (EqClass 1, HashSet.fromList [EqClass 0, EqClass 4])
    , (EqClass 0, HashSet.fromList [EqClass 4])
    , (EqClass 4, HashSet.fromList [])
    ]