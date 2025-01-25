{-# LANGUAGE DataKinds #-}

module Fixity (resolveFixity, run, parse, Fixity (..)) where

import Common (Fixity (..), Loc (..), Name, Pass (..), cast, getLoc, mkNotes, zipLocOf)
import Control.Monad (foldM)
import Data.HashMap.Strict qualified as HashMap
import Data.List.NonEmpty qualified as NE
import Diagnostic (Diagnose, fatal, internalError)
import Effectful.Reader.Static (Reader, ask, runReader)
import Error.Diagnose (Marker (This), Report (..))
import LangPrelude hiding (cycle)
import LensyUniplate (unicast)
import Poset (Poset)
import Poset qualified
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
  where
    getLocMb = maybe Blank getLoc
    mbPretty Nothing = "function application"
    mbPretty (Just op) = pretty op

lookup' :: (Diagnose :> es, Hashable k, Pretty k) => k -> HashMap k v -> Eff es v
lookup' key hmap = case HashMap.lookup key hmap of
    Nothing -> internalError Blank $ "missing operator" <+> pretty key
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
    order <- Poset.reportError $ Poset.relation prev next poset
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

run :: FixityMap -> Poset Op -> Eff (Reader (Poset Op) : Reader FixityMap : es) a -> Eff es a
run fixityMap poset = runReader fixityMap . runReader poset

resolveFixity :: Diagnose :> es => FixityMap -> Poset Op -> [Declaration 'DependencyRes] -> Eff es [Declaration 'Fixity]
resolveFixity fixityMap poset decls =
    run fixityMap poset $ traverse parseDeclaration decls

parseDeclaration :: Ctx es => Declaration 'DependencyRes -> Eff es (Declaration 'Fixity)
parseDeclaration = \case
    D.Value loc binding locals -> D.Value loc <$> parseBinding binding <*> traverse parseDeclaration locals
    D.Type loc name binders constrs ->
        pure $
            D.Type loc name (map cast binders) $
                constrs & map \(D.Constructor cloc cname args) -> D.Constructor cloc cname (unicast <$> args)
    D.GADT loc name mbKind constrs ->
        pure $ D.GADT loc name (fmap unicast mbKind) $ map cast constrs
    D.Signature loc name ty -> pure $ D.Signature loc name (unicast ty)

parse :: Ctx es => Expression 'DependencyRes -> Eff es (Expression 'Fixity)
parse = \case
    E.Lambda loc arg body -> E.Lambda loc (unicast arg) <$> parse body
    E.WildcardLambda loc args body -> E.WildcardLambda loc args <$> parse body
    E.Application lhs rhs -> E.Application <$> parse lhs <*> parse rhs
    E.TypeApplication expr tyArg -> E.TypeApplication <$> parse expr <*> pure (unicast tyArg)
    E.Let loc binding expr -> E.Let loc <$> parseBinding binding <*> parse expr
    E.LetRec loc bindings expr -> E.LetRec loc <$> traverse parseBinding bindings <*> parse expr
    E.Case loc arg cases -> E.Case loc <$> parse arg <*> traverse (bitraverse (pure . unicast) parse) cases
    E.Match loc cases -> E.Match loc <$> traverse (bitraverse (pure . map unicast) parse) cases
    E.If loc cond true false -> E.If loc <$> parse cond <*> parse true <*> parse false
    E.Annotation e ty -> E.Annotation <$> parse e <*> pure (unicast ty)
    E.Name name -> pure $ E.Name name
    E.RecordLens loc row -> pure $ E.RecordLens loc row
    E.Constructor name -> pure $ E.Constructor name
    E.Variant name -> pure $ E.Variant name
    E.Record loc row -> E.Record loc <$> traverse parse row
    E.List loc exprs -> E.List loc <$> traverse parse exprs
    E.Do loc stmts lastAction -> E.Do loc <$> traverse parseStmt stmts <*> parse lastAction
    E.Literal lit -> pure $ E.Literal lit
    E.Infix pairs last' -> join $ go' <$> traverse (bitraverse parse pure) pairs <*> parse last'
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

parseBinding :: Ctx es => Binding 'DependencyRes -> Eff es (Binding 'Fixity)
parseBinding = \case
    E.ValueBinding pat expr -> E.ValueBinding (unicast pat) <$> parse expr
    E.FunctionBinding name pats body -> E.FunctionBinding name (fmap unicast pats) <$> parse body

parseStmt :: Ctx es => DoStatement 'DependencyRes -> Eff es (DoStatement 'Fixity)
parseStmt = \case
    E.Bind pat body -> E.Bind (unicast pat) <$> parse body
    E.With loc pat body -> E.With loc (unicast pat) <$> parse body
    E.DoLet loc binding -> E.DoLet loc <$> parseBinding binding
    E.Action expr -> E.Action <$> parse expr
