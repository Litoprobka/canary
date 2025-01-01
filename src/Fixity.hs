{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE OverloadedRecordDot #-}

module Fixity (resolveFixity, testGraph, parse, Fixity (..)) where

import Common (Fixity (..), Loc (..), Name, Pass (..), PriorityRelation' (..), getLoc, mkNotes, zipLocOf)
import Control.Monad (foldM)
import Data.HashMap.Strict qualified as HashMap
import Data.HashSet qualified as HashSet
import Data.List.NonEmpty qualified as NE
import Diagnostic (Diagnose, dummy, fatal)
import Effectful (Eff, (:>))
import Effectful.Reader.Static (Reader, asks, runReader)
import Effectful.State.Static.Local (execState, gets, modify, modifyM)
import Error.Diagnose (Marker (This), Report (..))
import LensyUniplate
import Prettyprinter (Pretty, pretty, (<+>))
import Relude hiding (Op, Reader, ask, asks, cycle, execState, get, gets, modify, runReader)
import Syntax
import Syntax.Declaration qualified as D
import Syntax.Expression (DoStatement)
import Syntax.Expression qualified as E

newtype EqClass = EqClass Int deriving (Show, Eq, Hashable, Pretty)

type PG = PriorityGraph -- a synonym for type application
data PriorityGraph = PriorityGraph
    { graph :: HashMap EqClass (HashSet EqClass)
    , nextClass :: EqClass
    , opMap :: HashMap Op (Fixity, EqClass)
    }
type Op = Maybe Name

data Priority = Left' | Right' deriving (Show)

type Ctx es = (Reader PriorityGraph :> es, Diagnose :> es)

data OpError
    = IncompatibleFixity Op Op
    | UndefinedOrdering Op Op
    | MissingOperator Op
    | SelfRelation Op
    | PriorityCycle Op Op

opError :: Diagnose :> es => OpError -> Eff es a
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
        SelfRelation op ->
            Err
                Nothing
                ("self-reference in fixity declaration" <+> pretty op)
                (mkNotes [(getLocMb op, This "is referenced in its own fixity declaration")])
                []
        PriorityCycle op op2 ->
            Err
                Nothing
                ("priority cycle between" <+> pretty op <+> "and" <+> pretty op2)
                (mkNotes [(getLocMb op, This "occured at this declaration")])
                []
  where
    getLocMb = maybe Blank getLoc

lookup' :: (Diagnose :> es, Hashable k, Pretty k) => k -> HashMap k v -> Eff es v
lookup' key hmap = case HashMap.lookup key hmap of
    Nothing -> fatal . one . dummy $ "missing operator" <+> pretty key
    Just v -> pure v

{- | figure out which of the two operators has a higher priority
throws an error on incompatible fixities
-}
priority :: Ctx es => Op -> Op -> Eff es Priority
priority prev next = do
    graph <- asks @PG (.graph)
    opMap <- asks @PG (.opMap)
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

-- traverse all fixity declarations and construct a new priority graph
collectOperators :: Diagnose :> es => PriorityGraph -> [Declaration 'NameRes] -> Eff es PriorityGraph
collectOperators initGraph = execState @PG initGraph . traverse_ go
  where
    go = \case
        (D.Fixity _ fixity op rels) -> do
            traverse_ (addRelation fixity op GT) rels.above
            traverse_ (addRelation fixity op LT) rels.below
            traverse_ (addRelation fixity op EQ) rels.equal
        _nonFixity -> pass

    addRelation _ op_ _ op2_
        | op_ == op2_ = opError $ SelfRelation $ Just op_
    addRelation fixity op_ rel op2_ = do
        let op = Just op_
        let op2 = Just op2_
        opMap <- gets @PG (.opMap)
        lhsEqClass <- case HashMap.lookup op opMap of
            Nothing -> newEqClass op fixity
            Just (_, eqClass) -> do
                modify @PG \pg -> pg{opMap = HashMap.insert op (fixity, eqClass) pg.opMap}
                pure eqClass
        rhsEqClass <- maybe (newEqClass op2 Infix) (pure . snd) (HashMap.lookup op2 opMap)
        modifyM case rel of
            GT -> addHigherThanRel (op, lhsEqClass) (op2, rhsEqClass)
            LT -> addHigherThanRel (op2, rhsEqClass) (op, lhsEqClass)
            EQ -> mergeClasses (op, lhsEqClass) (op2, rhsEqClass)

    newEqClass op fixity = do
        eqClass <- gets @PG (.nextClass)
        modify \pg ->
            pg
                { nextClass = inc pg.nextClass
                , opMap = HashMap.insert op (fixity, pg.nextClass) pg.opMap
                , graph = HashMap.insert pg.nextClass HashSet.empty pg.graph
                }
        pure eqClass
    inc (EqClass n) = EqClass $ succ n

    mergeClasses (op, lhs) (op2, rhs) PriorityGraph{opMap, graph, nextClass} = do
        lhsHigherThan <- lookup' lhs graph
        rhsHigherThan <- lookup' rhs graph
        let cycle = HashSet.member lhs rhsHigherThan || HashSet.member rhs lhsHigherThan
        when cycle do
            opError $ PriorityCycle op op2

        let replaceOldClass hset
                | HashSet.member lhs hset = HashSet.insert rhs $ HashSet.delete lhs hset
                | otherwise = hset

        let lhsClassElems = HashMap.filter ((== lhs) . snd) opMap
            newOpMap = fmap (second $ const rhs) lhsClassElems <> opMap
            newGraph = fmap replaceOldClass graph
        pure PriorityGraph{opMap = newOpMap, graph = newGraph, nextClass}

    addHigherThanRel (op, higherClass) (op2, lowerClass) pg = do
        lowerClassHigherThan <- lookup' lowerClass pg.graph
        when (HashSet.member higherClass lowerClassHigherThan) do
            opError $ PriorityCycle op op2

        let addTransitiveRels hset
                | HashSet.member higherClass hset = HashSet.insert lowerClass hset
                | otherwise = hset

        let graph = fmap addTransitiveRels pg.graph
        pure pg{graph}

resolveFixity :: Diagnose :> es => PriorityGraph -> [Declaration 'NameRes] -> Eff es [Declaration 'Fixity]
resolveFixity graph decls = do
    newGraph <- collectOperators graph decls
    runReader newGraph $ traverse parseDeclaration decls

parseDeclaration :: Ctx es => Declaration 'NameRes -> Eff es (Declaration 'Fixity)
parseDeclaration = \case
    D.Value loc binding locals -> D.Value loc <$> parseBinding binding <*> traverse parseDeclaration locals
    D.Type loc name vars constrs ->
        pure $
            D.Type loc name vars $
                constrs & map \(D.Constructor cloc cname args) -> D.Constructor cloc cname (cast uniplateCast <$> args)
    D.Alias loc name ty -> pure $ D.Alias loc name (cast uniplateCast ty)
    D.Signature loc name ty -> pure $ D.Signature loc name (cast uniplateCast ty)
    D.Fixity loc fixity op PriorityRelation{above, below, equal} -> pure $ D.Fixity loc fixity op PriorityRelation{above, below, equal}

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
        opMap <- asks @PG (.opMap)
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

testGraph :: PriorityGraph
testGraph =
    PriorityGraph
        { graph =
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
        , nextClass = EqClass 1
        , opMap =
            HashMap.fromList
                [ (Nothing, (InfixL, EqClass 0))
                -- , ("+", (InfixL, EqClass 0))
                -- , ("*", (InfixL, EqClass 1))
                -- , ("?", (InfixR, EqClass 2))
                -- , ("^", (InfixR, EqClass 3))
                -- , ("==", (InfixChain, EqClass 4))
                ]
        }
