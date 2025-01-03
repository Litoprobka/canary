{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedRecordDot #-}

module Fixity (resolveFixity, parse, Fixity (..)) where

import Common (Fixity (..), Loc (..), Name, Pass (..), PriorityRelation' (..), getLoc, mkNotes, zipLocOf)
import Control.Monad (foldM)
import Data.HashMap.Strict qualified as HashMap
import Data.List.NonEmpty qualified as NE
import Diagnostic (Diagnose, dummy, fatal, nonFatal)
import Effectful (Eff, (:>))
import Effectful.Error.Static (Error, runErrorNoCallStack)
import Effectful.Reader.Static (Reader, ask, runReader)
import Effectful.State.Static.Local (State, execState, get, modify, modifyM, runState, state)
import Effectful.Writer.Static.Local (Writer, runWriter)
import Error.Diagnose (Marker (This), Report (..))
import LensyUniplate
import Poset (Poset, PosetError)
import Poset qualified
import Prettyprinter (Pretty, comma, hsep, pretty, punctuate, (<+>))
import Relude hiding (Op, Reader, State, ask, asks, cycle, execState, get, gets, modify, runReader, runState, state)
import Syntax
import Syntax.Declaration qualified as D
import Syntax.Expression (DoStatement)
import Syntax.Expression qualified as E

type Op = Maybe Name

type FixityMap = HashMap Op Fixity
data Priority = Left' | Right' deriving (Show)

type Ctx es = (Reader (Poset Op) :> es, Reader FixityMap :> es, Diagnose :> es)

data OpError
    = IncompatibleFixity Op Op
    | UndefinedOrdering Op Op
    | AmbiguousOrdering Op Op
    | MissingOperator Op
    | SelfRelation Op

data OpWarning = PriorityCycle Loc [Op] [Op]

opError :: Diagnose :> es => OpError -> Eff es a
opError =
    fatal . one . \case
        IncompatibleFixity prev next ->
            Err
                Nothing
                ("incompatible fixity of" <+> mbPretty prev <+> "and" <+> mbPretty next)
                (mkNotes [(getLocMb next, This "next operator"), (getLocMb prev, This "previous operator")])
                []
        UndefinedOrdering prev next ->
            Err
                Nothing
                ("undefined ordering of" <+> mbPretty prev <+> "and" <+> mbPretty next)
                (mkNotes [(getLocMb next, This "next operator"), (getLocMb prev, This "previous operator")])
                []
        AmbiguousOrdering prev next ->
            Err
                Nothing
                -- TODO: this error is very unclear
                ("ambiguous ordering of" <+> mbPretty prev <+> "and" <+> mbPretty next <+> "- their priority relations are cyclic")
                (mkNotes [(getLocMb next, This "next operator"), (getLocMb prev, This "previous operator")])
                []
        MissingOperator op ->
            Err
                Nothing
                ("missing operator" <+> mbPretty op)
                (mkNotes [(getLocMb op, This "is lacking a fixity declaration")])
                []
        SelfRelation op ->
            Err
                Nothing
                ("self-reference in fixity declaration" <+> mbPretty op)
                (mkNotes [(getLocMb op, This "is referenced in its own fixity declaration")])
                []
  where
    getLocMb = maybe Blank getLoc
    mbPretty Nothing = "function application"
    mbPretty (Just op) = pretty op

opWarning :: Diagnose :> es => OpWarning -> Eff es ()
opWarning =
    nonFatal . \case
        PriorityCycle loc ops ops2 ->
            Warn
                Nothing
                ( "priority cycle between" <+> hsep (punctuate comma $ map mbPretty ops) <+> "and" <+> hsep (punctuate comma $ map mbPretty ops2)
                )
                (mkNotes [(loc, This "occured at this declaration")])
                []
  where
    mbPretty Nothing = "function application"
    mbPretty (Just op) = pretty op

reportPosetError :: Diagnose :> es => Eff (Error PosetError : es) a -> Eff es a
reportPosetError = runErrorNoCallStack @PosetError >=> either asDiagnoseError pure
  where
    asDiagnoseError (Poset.LookupError key) = fatal . one . dummy $ "missing operator" <+> pretty key

reportCycleWarnings :: (State (Poset Op) :> es, Diagnose :> es) => Loc -> Eff (Writer (Seq (Poset.Cycle Op)) : es) a -> Eff es a
reportCycleWarnings loc action = do
    (x, warnings) <- runWriter action
    poset <- get @(Poset Op)
    for_ warnings \w -> do
        opWarning . toOpWarning poset $ w
    pure x
  where
    toOpWarning poset (Poset.Cycle lhsClass rhsClass) =
        PriorityCycle loc (Poset.items lhsClass poset) (Poset.items rhsClass poset)

lookup' :: (Diagnose :> es, Hashable k, Pretty k) => k -> HashMap k v -> Eff es v
lookup' key hmap = case HashMap.lookup key hmap of
    Nothing -> fatal . one . dummy $ "missing operator" <+> pretty key
    Just v -> pure v

{- | figure out which of the two operators has a higher priority
throws an error on incompatible fixities
-}
priority :: Ctx es => Op -> Op -> Eff es Priority
priority prev next = do
    poset <- ask @(Poset Op)
    fixities <- ask @FixityMap
    prevFixity <- lookup' prev fixities
    nextFixity <- lookup' next fixities
    order <- reportPosetError $ Poset.relation prev next poset
    case order of
        _ | prev == next && prevFixity == InfixChain -> pure Left'
        Poset.DefinedOrder EQ -> case (prevFixity, nextFixity) of
            (InfixL, InfixL) -> pure Left'
            (InfixR, InfixR) -> pure Left'
            _ -> opError $ IncompatibleFixity prev next
        Poset.DefinedOrder GT -> pure Left'
        Poset.DefinedOrder LT -> pure Right'
        -- we don't error out on priority cycles when constructing the priority graph
        -- instead, relations where A > B and B > A are considered borked and are treated as if A and B are not comparable
        Poset.NoOrder -> opError $ UndefinedOrdering prev next
        Poset.AmbiguousOrder -> opError $ AmbiguousOrdering prev next

-- traverse all fixity declarations and construct a new priority graph
collectOperators :: Diagnose :> es => FixityMap -> Poset Op -> [Declaration 'NameRes] -> Eff es (FixityMap, Poset Op)
collectOperators fixityMap poset = runState @(Poset Op) poset . execState @FixityMap fixityMap . reportPosetError . traverse_ go
  where
    go = \case
        (D.Fixity loc fixity op rels) -> reportCycleWarnings loc do
            -- all operators implicitly have a lower precedence than function application, unless stated otherwise
            let below
                    | Nothing `notElem` rels.above = Nothing : map Just rels.below
                    | otherwise = map Just rels.below

            modify @FixityMap $ HashMap.insert (Just op) fixity

            traverse_ (addRelation op GT) rels.above
            traverse_ (addRelation op LT) below
            traverse_ (addRelation op EQ . Just) rels.equal
        _nonFixity -> pass

    addRelation op_ _ op2
        | Just op_ == op2 = opError $ SelfRelation $ Just op_
    addRelation op_ rel op2 = do
        let op = Just op_
        lhsClass <- state $ Poset.eqClass op
        rhsClass <- state $ Poset.eqClass op2
        modifyM @(Poset Op) $ Poset.addRelationLenient lhsClass rhsClass rel

resolveFixity :: Diagnose :> es => [Declaration 'NameRes] -> Eff es [Declaration 'Fixity]
resolveFixity = resolveFixityWithEnv fixityMap poset
  where
    fixityMap = HashMap.singleton Nothing InfixL
    (_, poset) = Poset.eqClass Nothing Poset.empty

resolveFixityWithEnv :: Diagnose :> es => FixityMap -> Poset Op -> [Declaration 'NameRes] -> Eff es [Declaration 'Fixity]
resolveFixityWithEnv fixityMap poset decls = do
    (newFixityMap, newPoset) <- collectOperators fixityMap poset decls
    runReader newFixityMap $ runReader newPoset $ traverse parseDeclaration decls

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
        fixity <- lookup' mbOp =<< ask @FixityMap
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
