{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DuplicateRecordFields #-}

module Fixity (resolveFixity, run, parse, Fixity (..)) where

import Common (Fixity (..), Loc (..), Name, Pass (..), getLoc, mkNotes, zipLocOf)
import Control.Monad (foldM)
import Data.HashMap.Strict qualified as HashMap
import Data.List.NonEmpty qualified as NE
import Data.Traversable (for)
import Diagnostic (Diagnose, fatal, internalError)
import Effectful.Reader.Static (Reader, ask, runReader)
import Error.Diagnose (Marker (This), Report (..))
import LangPrelude hiding (cycle)
import Poset (Poset)
import Poset qualified
import Syntax
import Syntax.Declaration (GadtConstructor (..))
import Syntax.Declaration qualified as D
import Syntax.Term

type Op = Maybe Name

type FixityMap = HashMap Op Fixity
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
        D.Type loc name
            <$> for binders parseBinder
            <*> for constrs \(D.Constructor cloc cname args) -> D.Constructor cloc cname <$> traverse parse args
    D.GADT loc name mbKind constrs ->
        D.GADT loc name <$> traverse parse mbKind <*> traverse parseGadtConstructor constrs
    D.Signature loc name ty -> D.Signature loc name <$> parse ty
  where
    parseGadtConstructor GadtConstructor{loc, name, sig} = D.GadtConstructor loc name <$> parse sig

parse :: Ctx es => Term 'DependencyRes -> Eff es (Term 'Fixity)
parse = \case
    Lambda loc arg body -> Lambda loc <$> parsePattern arg <*> parse body
    WildcardLambda loc args body -> WildcardLambda loc args <$> parse body
    Application lhs rhs -> Application <$> parse lhs <*> parse rhs
    TypeApplication expr tyArg -> TypeApplication <$> parse expr <*> parse tyArg
    Let loc binding expr -> Let loc <$> parseBinding binding <*> parse expr
    LetRec loc bindings expr -> LetRec loc <$> traverse parseBinding bindings <*> parse expr
    Case loc arg cases -> Case loc <$> parse arg <*> traverse (bitraverse parsePattern parse) cases
    Match loc cases -> Match loc <$> traverse (bitraverse (traverse parsePattern) parse) cases
    If loc cond true false -> If loc <$> parse cond <*> parse true <*> parse false
    Annotation e ty -> Annotation <$> parse e <*> parse ty
    Name name -> pure $ Name name
    RecordLens loc row -> pure $ RecordLens loc row
    Variant name -> pure $ Variant name
    Record loc row -> Record loc <$> traverse parse row
    List loc exprs -> List loc <$> traverse parse exprs
    Do loc stmts lastAction -> Do loc <$> traverse parseStmt stmts <*> parse lastAction
    Literal lit -> pure $ Literal lit
    InfixE pairs last' -> join $ go' <$> traverse (bitraverse parse pure) pairs <*> parse last'
    -- Var name -> pure $ Var name
    Forall loc binder body -> Forall loc <$> parseBinder binder <*> parse body
    Exists loc binder body -> Exists loc <$> parseBinder binder <*> parse body
    Function loc lhs rhs -> Function loc <$> parse lhs <*> parse rhs
    VariantT loc row -> VariantT loc <$> traverse parse row
    RecordT loc row -> RecordT loc <$> traverse parse row
  where
    go' :: Ctx es => [(Expr 'Fixity, Op)] -> Expr 'Fixity -> Eff es (Expr 'Fixity)
    go' pairs last' = go [] pairs
      where
        go :: Ctx es => [(Expr 'Fixity, Op)] -> [(Expr 'Fixity, Op)] -> Eff es (Expr 'Fixity)
        go [] [] = pure last'
        go ((x, op) : rest) [] = do
            last'' <- appOrMerge op x last'
            foldM (\acc (z, op') -> appOrMerge op' z acc) last'' rest
        go [] ((x, op) : rest) = go [(x, op)] rest
        go ((x, prev) : stack) ((y, next) : rest) = do
            newStack <- pop (y, next) ((x, prev) :| stack)
            go newStack rest

    pop :: Ctx es => (Expr 'Fixity, Op) -> NonEmpty (Expr 'Fixity, Op) -> Eff es [(Expr 'Fixity, Op)]
    pop (y, next) ((x, prev) :| stack) =
        priority prev next >>= \case
            Right' -> pure ((y, next) : (x, prev) : stack)
            Left' -> do
                newX <- appOrMerge prev x y
                case NE.nonEmpty stack of
                    Nothing -> pure [(newX, next)]
                    Just stack' -> pop (newX, next) stack'

    appOrMerge :: Ctx es => Op -> Expr 'Fixity -> Expr 'Fixity -> Eff es (Expr 'Fixity)
    appOrMerge mbOp lhs rhs = do
        fixity <- lookup' mbOp =<< ask @FixityMap
        let loc = zipLocOf lhs rhs
        pure case (mbOp, fixity, lhs) of
            (Nothing, _, _) -> Application lhs rhs
            (Just op, InfixChain, Application (Name op') (List _ args))
                | op == op' ->
                    Application (Name op') (List loc $ args <> [rhs])
            (Just op, InfixChain, _) -> Application (Name op) $ List loc [lhs, rhs]
            (Just op, _, _) -> Application (Application (Name op) lhs) rhs

-- * Helpers

parseBinder :: Ctx es => VarBinder DependencyRes -> Eff es (VarBinder 'Fixity)
parseBinder VarBinder{var, kind} = VarBinder var <$> traverse parse kind

parsePattern :: Ctx es => Pattern 'DependencyRes -> Eff es (Pattern 'Fixity)
parsePattern = \case
    VarP name -> pure $ VarP name
    WildcardP loc name -> pure $ WildcardP loc name
    AnnotationP pat ty -> AnnotationP <$> parsePattern pat <*> parse ty
    ConstructorP name pats -> ConstructorP name <$> traverse parsePattern pats
    VariantP name pat -> VariantP name <$> parsePattern pat
    RecordP loc row -> RecordP loc <$> traverse parsePattern row
    ListP loc pats -> ListP loc <$> traverse parsePattern pats
    LiteralP lit -> pure $ LiteralP lit

parseBinding :: Ctx es => Binding 'DependencyRes -> Eff es (Binding 'Fixity)
parseBinding = \case
    ValueB pat expr -> ValueB <$> parsePattern pat <*> parse expr
    FunctionB name pats body -> FunctionB name <$> traverse parsePattern pats <*> parse body

parseStmt :: Ctx es => DoStatement 'DependencyRes -> Eff es (DoStatement 'Fixity)
parseStmt = \case
    Bind pat body -> Bind <$> parsePattern pat <*> parse body
    With loc pat body -> With loc <$> parsePattern pat <*> parse body
    DoLet loc binding -> DoLet loc <$> parseBinding binding
    Action expr -> Action <$> parse expr
