{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE DataKinds #-}

module Infix where

import Common (Name, getLoc, zipLoc, Pass (..))
import Control.Monad (foldM)
import Data.HashMap.Strict qualified as HashMap
import Data.HashSet qualified as HashSet
import Data.List.NonEmpty qualified as NE
import Effectful (Eff, runPureEff, (:>))
import Effectful.Error.Static (Error, runErrorNoCallStack, throwError)
import Effectful.Reader.Static (Reader, ask, runReader)
import Playground ()
import Relude hiding (Op, Reader, ask, runReader)
import Syntax (Expression, Pattern)
import Syntax.Expression qualified as E
import qualified Syntax.Pattern as P
import qualified Syntax.Type as T
import Syntax.Expression (Binding)

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

resolveFixity :: Expression 'NameRes -> Either Text (Expression 'Fixity)
resolveFixity = runPureEff . runErrorNoCallStack . runReader testOpMap . runReader testGraph . parse

parse :: Ctx es => Expression 'NameRes -> Eff es (Expression 'Fixity)
parse = \case
    E.Lambda loc arg body -> E.Lambda loc (castP arg) <$> parse body
    E.Application loc lhs rhs -> E.Application loc <$> parse lhs <*> parse rhs
    E.Let loc bind expr -> E.Let loc <$> parseBinding bind <*> parse expr
    E.Case loc arg cases -> E.Case loc <$> parse arg <*> traverse (bitraverse (pure . castP) parse) cases
    -- | Haskell's \cases
    E.Match loc cases -> E.Match loc <$> traverse (bitraverse (pure . map castP) parse) cases
    E.If loc cond true false -> E.If loc <$> parse cond <*> parse true <*> parse false
    -- | value : Type
    E.Annotation loc e ty -> E.Annotation loc <$> parse e <*> pure (T.cast id ty)
    E.Name name -> pure $ E.Name name
    -- | .field.otherField.thirdField
    E.RecordLens loc row -> pure $ E.RecordLens loc row
    E.Constructor name -> pure $ E.Constructor name
    E.Variant name -> pure $ E.Variant name
    E.Record loc row -> E.Record loc <$> traverse parse row
    E.List loc exprs -> E.List loc <$> traverse parse exprs
    E.IntLiteral loc n -> pure $ E.IntLiteral loc n
    E.TextLiteral loc txt -> pure $ E.TextLiteral loc txt
    E.CharLiteral loc c -> pure $ E.CharLiteral loc c
    -- | an unresolved expression with infix / prefix operators
    E.Infix _ pairs last' -> join $ go' <$> traverse (bitraverse parse pure) pairs <*> parse last'
  where
    go' :: Ctx es => [(Expression 'Fixity, Name)] -> Expression 'Fixity -> Eff es (Expression 'Fixity)
    go' pairs last' = go [] pairs
      where
        go :: Ctx es => [(Expression 'Fixity, Name)] -> [(Expression 'Fixity, Name)] -> Eff es (Expression 'Fixity)
        go [] [] = pure last'
        go ((x, op) : rest) [] = do
            last'' <- appOrMerge op x last'
            foldM (\acc (z, op') -> appOrMerge op' z acc) last'' rest
        go [] ((x, op) : rest) = go [(x, op)] rest
        go ((x, prev) : stack) ((y, next) : rest) = do
            newStack <- pop (y, next) ((x, prev) :| stack)
            go newStack rest

    pop :: Ctx es => (Expression 'Fixity, Name) -> NonEmpty (Expression 'Fixity, Name) -> Eff es [(Expression 'Fixity, Name)]
    pop (y, next) ((x, prev) :| stack) =
        priority prev next >>= \case
            Right' -> pure ((y, next) : (x, prev) : stack)
            Left' -> do
                newX <- appOrMerge prev x y
                case NE.nonEmpty stack of
                    Nothing -> pure [(newX, next)]
                    Just stack' -> pop (newX, next) stack'

    appOrMerge :: Ctx es => Name -> Expression 'Fixity -> Expression 'Fixity -> Eff es (Expression 'Fixity)
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

-- * Helpers

parseBinding :: Ctx es => Binding 'NameRes -> Eff es (Binding 'Fixity)
parseBinding = \case
    E.ValueBinding loc pat expr -> E.ValueBinding loc (castP pat) <$> parse expr
    E.FunctionBinding loc name pats body -> E.FunctionBinding loc name (fmap castP pats) <$> parse body

castP :: Pattern 'NameRes -> Pattern 'Fixity
castP = P.cast \recur -> \case
    P.Annotation loc pat ty -> P.Annotation loc (recur pat) (T.cast id ty)
    other -> recur other
