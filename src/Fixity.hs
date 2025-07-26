{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE PatternSynonyms #-}

module Fixity (resolveFixity, run, traversal, parse, Fixity (..)) where

import Common (
    Fixity (..),
    Loc (..),
    Located (..),
    Name,
    Pass (..),
    getLoc,
    mkNotes,
    unLoc,
    zipLocOf,
    pattern L,
    pattern Located,
 )
import Control.Monad (foldM)
import Data.IdMap qualified as Map
import Data.List.NonEmpty qualified as NE
import Data.Poset (Poset)
import Data.Poset qualified as Poset
import DependencyResolution (FixityMap, Op (..))
import Diagnostic (Diagnose, fatal)
import Effectful.Error.Static (runErrorNoCallStackWith)
import Effectful.Reader.Static (Reader, ask, runReader)
import Error.Diagnose (Marker (This), Position (..), Report (..))
import LangPrelude hiding (cycle)
import Syntax
import Syntax.AstTraversal
import Syntax.Declaration qualified as D
import Syntax.Term

data Priority = Left' | Right' deriving (Show)

type Ctx es = (Reader (Poset Op) :> es, Reader FixityMap :> es, Diagnose :> es)

data OpError
    = IncompatibleFixity Op Op
    | UndefinedOrdering Op Op
    | AmbiguousOrdering Op Op

opError :: Diagnose :> es => OpError -> Eff es a
opError =
    fatal . one . \case
        IncompatibleFixity prev next ->
            Err
                Nothing
                ("incompatible fixity of" <+> pretty prev <+> "and" <+> pretty next)
                (mkNotes [(getLocOp next, This "next operator"), (getLocOp prev, This "previous operator")])
                []
        UndefinedOrdering prev next ->
            Err
                Nothing
                ("undefined ordering of" <+> pretty prev <+> "and" <+> pretty next)
                (mkNotes [(getLocOp next, This "next operator"), (getLocOp prev, This "previous operator")])
                []
        AmbiguousOrdering prev next ->
            Err
                Nothing
                -- TODO: this error is very unclear
                ("ambiguous ordering of" <+> pretty prev <+> "and" <+> pretty next <+> "- their priority relations are cyclic")
                (mkNotes [(getLocOp next, This "next operator"), (getLocOp prev, This "previous operator")])
                []
  where
    getLocOp = \case
        AppOp -> Loc Position{file = "<builtin>", begin = (0, 0), end = (0, 0)}
        Op op -> getLoc op

lookupFixity :: Op -> FixityMap -> Fixity
lookupFixity = Map.lookupDefault Infix

{- | figure out which of the two operators has a higher priority

throws an error on incompatible fixities
-}
priority :: Ctx es => Op -> Op -> Eff es Priority
priority prev next = do
    poset <- ask @(Poset Op)
    fixities <- ask @FixityMap
    let prevFixity = lookupFixity prev fixities
        nextFixity = lookupFixity next fixities
    order <- runErrorNoCallStackWith @Poset.PosetError (const $ pure defaultRelation) $ Poset.relation prev next poset
    case order of
        _ | prev == next && prevFixity == InfixChain -> pure Left'
        Poset.DefinedOrder EQ -> case (prevFixity, nextFixity) of
            (InfixL, InfixL) -> pure Left'
            (InfixR, InfixR) -> pure Right'
            _ -> opError $ IncompatibleFixity prev next
        Poset.DefinedOrder GT -> pure Left'
        Poset.DefinedOrder LT -> pure Right'
        -- we don't error out on priority cycles when constructing the priority graph
        -- instead, relations where A > B and B > A are considered borked and are treated as if A and B are not comparable
        Poset.NoOrder -> opError $ UndefinedOrdering prev next
        Poset.AmbiguousOrder -> opError $ AmbiguousOrdering prev next
  where
    -- a relation that's used when one of the operators lacks a fixity declaration
    defaultRelation = case (prev, next) of
        (AppOp, Op _) -> Poset.DefinedOrder GT
        (Op _, AppOp) -> Poset.DefinedOrder LT
        (Op _, Op _) -> Poset.NoOrder
        (AppOp, AppOp) -> Poset.DefinedOrder GT -- this shouldn't normally happen

run :: FixityMap -> Poset Op -> Eff (Reader (Poset Op) : Reader FixityMap : es) a -> Eff es a
run fixityMap poset = runReader fixityMap . runReader poset

resolveFixity :: Diagnose :> es => FixityMap -> Poset Op -> [Declaration 'DependencyRes] -> Eff es [Declaration 'Fixity]
resolveFixity fixityMap poset decls =
    run fixityMap poset $ traverse traversal.declaration decls

parseDeclaration :: Ctx es => Declaration 'DependencyRes -> Eff es (Declaration 'Fixity)
parseDeclaration = traverse \case
    D.Value binding locals -> D.Value <$> traversal.binding binding <*> traverse traversal.declaration locals
    D.Type name binders constrs ->
        D.Type name
            <$> for binders traversal.binder
            <*> for constrs \(D.Constructor cloc cname args) -> D.Constructor cloc cname <$> traverse parse args
    D.GADT name mbKind constrs ->
        D.GADT name <$> traverse parse mbKind <*> traverse (travGadtConstructor traversal) constrs
    D.Signature name ty -> D.Signature name <$> parse ty

traversal :: forall es. Ctx es => AstTraversal 'DependencyRes 'Fixity (Eff es)
traversal =
    tie
        UntiedTraversal
            { term = const parse
            , pattern_ = const parsePattern
            , declaration = const parseDeclaration
            , name = const pure
            , binding = defTravBinding
            , binder = defTravBinder
            , statement = defTravStatement
            }

parse :: Ctx es => Term 'DependencyRes -> Eff es (Term 'Fixity)
parse (term' :@ termLoc) =
    Located termLoc <$> case term' of
        InfixE pairs last' -> do
            pairs' <- traverse (bitraverse parse (pure . maybe AppOp Op)) pairs
            last'' <- parse last'
            shuntingYard id appOrMerge pairs' last''
        other -> unLoc <$> partialTravTerm traversal (other :@ termLoc)
  where
    appOrMerge :: Ctx es => Op -> Expr 'Fixity -> Expr 'Fixity -> Eff es (Expr 'Fixity)
    appOrMerge mbOp lhs rhs = do
        fixity <- lookupFixity mbOp <$> ask @FixityMap
        let loc = zipLocOf lhs rhs
        pure $ Located loc case (mbOp, fixity, lhs) of
            (AppOp, _, _) -> App Visible lhs rhs
            -- todo: InfixChain applications should use a special AST node, otherwise
            -- stuff like `(==) [a, b] == c` gets incorrectly parsed as `(==) [a, b, c]`
            (Op op, InfixChain, L (App Visible (Located nloc (Name op')) (L (List args))))
                | op == op' ->
                    App Visible (Located nloc $ Name op') (Located loc $ List $ args <> [rhs])
            (Op op, InfixChain, _) -> App Visible (Located (getLoc op) (Name op)) $ Located loc $ List [lhs, rhs]
            (Op op, _, _) -> App Visible (Located (zipLocOf lhs op) $ App Visible (Located (getLoc op) (Name op)) lhs) rhs

parsePattern :: Ctx es => Pattern 'DependencyRes -> Eff es (Pattern 'Fixity)
parsePattern (term' :@ termLoc) =
    Located termLoc <$> case term' of
        InfixP pairs l -> do
            pairs' <- traverse (bitraverse parsePattern pure) pairs
            l' <- parsePattern l
            shuntingYard Op conP pairs' l'
        other -> unLoc <$> partialTravPattern traversal (other :@ termLoc)
  where
    conP :: Applicative m => Name -> Pattern 'Fixity -> Pattern 'Fixity -> m (Pattern 'Fixity)
    conP conOp lhs rhs = pure $ ConstructorP conOp [(Visible, lhs), (Visible, rhs)] :@ zipLocOf lhs rhs

shuntingYard
    :: forall es a unloc op. (a ~ Located unloc, Ctx es) => (op -> Op) -> (op -> a -> a -> Eff es a) -> [(a, op)] -> a -> Eff es unloc
shuntingYard toOp app pairs last' = go [] pairs <&> unLoc
  where
    go :: [(a, op)] -> [(a, op)] -> Eff es a
    go [] [] = pure last'
    go ((x, op) : rest) [] = do
        last'' <- app op x last'
        foldM (\acc (z, op') -> app op' z acc) last'' rest
    go [] ((x, op) : rest) = go [(x, op)] rest
    go ((x, prev) : stack) ((y, next) : rest) = do
        newStack <- pop (y, next) ((x, prev) :| stack)
        go newStack rest

    pop :: (a, op) -> NonEmpty (a, op) -> Eff es [(a, op)]
    pop (y, next) ((x, prev) :| stack) =
        priority (toOp prev) (toOp next) >>= \case
            Right' -> pure ((y, next) : (x, prev) : stack)
            Left' -> do
                newX <- app prev x y
                case NE.nonEmpty stack of
                    Nothing -> pure [(newX, next)]
                    Just stack' -> pop (newX, next) stack'
