{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}

module Fixity (resolveFixity, testOpMap, testGraph, parse, Fixity (..)) where

import Common (Fixity (..), Loc (..), Name, Pass (..), getLoc, mkNotes, zipLocOf)
import Control.Monad (foldM)
import Data.HashMap.Strict qualified as HashMap
import Data.HashSet qualified as HashSet
import Data.List.NonEmpty qualified as NE
import Diagnostic (Diagnose, dummy, fatal)
import Effectful (Eff, (:>))
import Effectful.Reader.Static (Reader, ask, runReader)
import Error.Diagnose (Marker (This), Report (..))
import LensyUniplate
import Prettyprinter (Pretty, pretty, (<+>))
import Relude hiding (Op, Reader, ask, runReader)
import Syntax
import Syntax.Declaration qualified as D
import Syntax.Expression (DoStatement)
import Syntax.Expression qualified as E

newtype EqClass = EqClass Int deriving (Show, Eq, Hashable, Pretty)

type PriorityGraph = HashMap EqClass (HashSet EqClass)
type Op = Maybe Name
type OpMap = HashMap Op (Fixity, EqClass)

data Priority = Left' | Right' deriving (Show)

type Ctx es = (Reader OpMap :> es, Reader PriorityGraph :> es, Diagnose :> es)

data OpError
    = IncompatibleFixity Op Op
    | UndefinedOrdering Op Op
    | MissingOperator Op

opError :: Ctx es => OpError -> Eff es a
opError =
    fatal . one . \case
        IncompatibleFixity prev next ->
            Err
                Nothing
                ("incompatible fixity of" <+> pretty prev <+> "and" <+> pretty next)
                (mkNotes [(getLocMb next, This "next operator"), (getLocMb prev, This "previous operator")])
                []
        UndefinedOrdering prev next ->
            Err
                Nothing
                ("undefined ordering of" <+> pretty prev <+> "and" <+> pretty next)
                (mkNotes [(getLocMb next, This "next operator"), (getLocMb prev, This "previous operator")])
                []
        MissingOperator op ->
            Err
                Nothing
                ("missing operator" <+> pretty op)
                (mkNotes [(getLocMb op, This "is lacking a fixity declaration")])
                []
  where
    getLocMb = maybe Blank getLoc

lookup' :: (Diagnose :> es, Hashable k, Pretty k) => k -> HashMap k v -> Eff es v
lookup' key hmap = case HashMap.lookup key hmap of
    Nothing -> fatal . one . dummy $ "missing operator" <+> pretty key
    Just v -> pure v

priority :: Ctx es => Op -> Op -> Eff es Priority
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
            _ -> opError $ IncompatibleFixity prev next
        | HashSet.member nextEq prevHigherThan -> pure Left'
        | HashSet.member prevEq nextHigherThan -> pure Right'
        | otherwise -> opError $ UndefinedOrdering prev next
resolveFixity :: Diagnose :> es => OpMap -> PriorityGraph -> [Declaration 'NameRes] -> Eff es [Declaration 'Fixity]
resolveFixity opMap graph = runReader opMap . runReader graph . traverse parseDeclaration

parseDeclaration :: Ctx es => Declaration 'NameRes -> Eff es (Declaration 'Fixity)
parseDeclaration = \case
    D.Value loc binding locals -> D.Value loc <$> parseBinding binding <*> traverse parseDeclaration locals
    D.Type loc name vars constrs ->
        pure $
            D.Type loc name vars $
                constrs & map \(D.Constructor cloc cname args) -> D.Constructor cloc cname (cast uniplateCast <$> args)
    D.Alias loc name ty -> pure $ D.Alias loc name (cast uniplateCast ty)
    D.Signature loc name ty -> pure $ D.Signature loc name (cast uniplateCast ty)
    D.Fixity loc fixity op above below -> pure $ D.Fixity loc fixity op above below

parse :: Ctx es => Expression 'NameRes -> Eff es (Expression 'Fixity)
parse = \case
    E.Lambda loc arg body -> E.Lambda loc (cast uniplateCast arg) <$> parse body
    E.WildcardLambda loc args body -> E.WildcardLambda loc args <$> parse body
    E.Application lhs rhs -> E.Application <$> parse lhs <*> parse rhs
    E.Let loc binding expr -> E.Let loc <$> parseBinding binding <*> parse expr
    E.Case loc arg cases -> E.Case loc <$> parse arg <*> traverse (bitraverse (pure . cast uniplateCast) parse) cases
    -- \| Haskell's \cases
    E.Match loc cases -> E.Match loc <$> traverse (bitraverse (pure . map (cast uniplateCast)) parse) cases
    E.If loc cond true false -> E.If loc <$> parse cond <*> parse true <*> parse false
    -- \| value : Type
    E.Annotation e ty -> E.Annotation <$> parse e <*> pure (cast uniplateCast ty)
    E.Name name -> pure $ E.Name name
    -- \| .field.otherField.thirdField
    E.RecordLens loc row -> pure $ E.RecordLens loc row
    E.Constructor name -> pure $ E.Constructor name
    E.Variant name -> pure $ E.Variant name
    E.Record loc row -> E.Record loc <$> traverse parse row
    E.List loc exprs -> E.List loc <$> traverse parse exprs
    E.Do loc stmts lastAction -> E.Do loc <$> traverse parseStmt stmts <*> parse lastAction
    E.Literal lit -> pure $ E.Literal lit
    -- \| an unresolved expression with infix / prefix operators
    E.Infix _ pairs last' -> join $ go' <$> traverse (bitraverse parse pure) pairs <*> parse last'
  where
    go' :: Ctx es => [(Expression 'Fixity, Op)] -> Expression 'Fixity -> Eff es (Expression 'Fixity)
    go' pairs last' = go [] pairs
      where
        go :: Ctx es => [(Expression 'Fixity, Op)] -> [(Expression 'Fixity, Op)] -> Eff es (Expression 'Fixity)
        go [] [] = pure last'
        go ((x, op) : rest) [] = do
            last'' <- appOrMerge op x last'
            foldM (\acc (z, op') -> appOrMerge op' z acc) last'' rest
        go [] ((x, op) : rest) = go [(x, op)] rest
        go ((x, prev) : stack) ((y, next) : rest) = do
            newStack <- pop (y, next) ((x, prev) :| stack)
            go newStack rest

    pop :: Ctx es => (Expression 'Fixity, Op) -> NonEmpty (Expression 'Fixity, Op) -> Eff es [(Expression 'Fixity, Op)]
    pop (y, next) ((x, prev) :| stack) =
        priority prev next >>= \case
            Right' -> pure ((y, next) : (x, prev) : stack)
            Left' -> do
                newX <- appOrMerge prev x y
                case NE.nonEmpty stack of
                    Nothing -> pure [(newX, next)]
                    Just stack' -> pop (newX, next) stack'

    appOrMerge :: Ctx es => Op -> Expression 'Fixity -> Expression 'Fixity -> Eff es (Expression 'Fixity)
    appOrMerge mbOp lhs rhs = do
        opMap <- ask @OpMap
        (fixity, _) <- lookup' mbOp opMap
        let loc = zipLocOf lhs rhs
        pure case (mbOp, fixity, lhs) of
            (Nothing, _, _) -> E.Application lhs rhs
            (Just op, InfixChain, E.Application (E.Name op') (E.List _ args))
                | op == op' ->
                    E.Application (E.Name op') (E.List loc $ args <> [rhs])
            (Just op, InfixChain, _) -> E.Application (E.Name op) $ E.List loc [lhs, rhs]
            (Just op, _, _) -> E.Application (E.Application (E.Name op) lhs) rhs

-- * Helpers

parseBinding :: Ctx es => Binding 'NameRes -> Eff es (Binding 'Fixity)
parseBinding = \case
    E.ValueBinding pat expr -> E.ValueBinding (cast uniplateCast pat) <$> parse expr
    E.FunctionBinding name pats body -> E.FunctionBinding name (fmap (cast uniplateCast) pats) <$> parse body

parseStmt :: Ctx es => DoStatement 'NameRes -> Eff es (DoStatement 'Fixity)
parseStmt = \case
    E.Bind pat body -> E.Bind (cast uniplateCast pat) <$> parse body
    E.With loc pat body -> E.With loc (cast uniplateCast pat) <$> parse body
    E.DoLet loc binding -> E.DoLet loc <$> parseBinding binding
    E.Action expr -> E.Action <$> parse expr

---

testOpMap :: OpMap
testOpMap =
    HashMap.fromList
        [ (Nothing, (InfixL, EqClass 0))
        -- , ("+", (InfixL, EqClass 0))
        -- , ("*", (InfixL, EqClass 1))
        -- , ("?", (InfixR, EqClass 2))
        -- , ("^", (InfixR, EqClass 3))
        -- , ("==", (InfixChain, EqClass 4))
        ]

testGraph :: PriorityGraph
testGraph =
    HashMap.fromList $
        map
            (second $ HashSet.fromList . map EqClass)
            [ (EqClass 0, [])
            -- , (EqClass 3, [0, 1, 2, 4])
            -- , (EqClass 2, [0, 4])
            -- , (EqClass 1, [0, 4])
            -- , (EqClass 0, [4])
            -- , (EqClass 4, [])
            ]