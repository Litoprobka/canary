{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE PatternSynonyms #-}

module Fixity (resolveFixity, run, parse, Fixity (..)) where

import Common (Fixity (..), Loc (..), Located (..), Name, Pass (..), getLoc, mkNotes, unLoc, zipLocOf, pattern L, pattern (:@))
import Control.Monad (foldM)
import Data.EnumMap.Strict qualified as Map
import Data.List.NonEmpty qualified as NE
import Data.Traversable (for)
import DependencyResolution (FixityMap, Op (..))
import Diagnostic (Diagnose, fatal)
import Effectful.Error.Static (runErrorNoCallStackWith)
import Effectful.Reader.Static (Reader, ask, runReader)
import Error.Diagnose (Marker (This), Position (..), Report (..))
import LangPrelude hiding (cycle)
import Poset (Poset)
import Poset qualified
import Syntax
import Syntax.Declaration (GadtConstructor (..))
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
lookupFixity = Map.findWithDefault Infix

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
            (InfixR, InfixR) -> pure Left'
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
    run fixityMap poset $ traverse parseDeclaration decls

parseDeclaration :: Ctx es => Declaration 'DependencyRes -> Eff es (Declaration 'Fixity)
parseDeclaration = traverse \case
    D.Value binding locals -> D.Value <$> parseBinding binding <*> traverse parseDeclaration locals
    D.Type name binders constrs ->
        D.Type name
            <$> for binders parseBinder
            <*> for constrs \(D.Constructor cloc cname args) -> D.Constructor cloc cname <$> traverse parse args
    D.GADT name mbKind constrs ->
        D.GADT name <$> traverse parse mbKind <*> traverse parseGadtConstructor constrs
    D.Signature name ty -> D.Signature name <$> parse ty
  where
    parseGadtConstructor GadtConstructor{loc, name, sig} = D.GadtConstructor loc name <$> parse sig

parse :: Ctx es => Term 'DependencyRes -> Eff es (Term 'Fixity)
parse = traverse \case
    Lambda arg body -> Lambda <$> parsePattern arg <*> parse body
    WildcardLambda args body -> WildcardLambda args <$> parse body
    App lhs rhs -> App <$> parse lhs <*> parse rhs
    TypeApp expr tyArg -> TypeApp <$> parse expr <*> parse tyArg
    Let binding expr -> Let <$> parseBinding binding <*> parse expr
    LetRec bindings expr -> LetRec <$> traverse parseBinding bindings <*> parse expr
    Case arg cases -> Case <$> parse arg <*> traverse (bitraverse parsePattern parse) cases
    Match cases -> Match <$> traverse (bitraverse (traverse parsePattern) parse) cases
    If cond true false -> If <$> parse cond <*> parse true <*> parse false
    Annotation e ty -> Annotation <$> parse e <*> parse ty
    Name name -> pure $ Name name
    RecordLens row -> pure $ RecordLens row
    Variant name -> pure $ Variant name
    Record row -> Record <$> traverse parse row
    Sigma x y -> Sigma <$> parse x <*> parse y
    List exprs -> List <$> traverse parse exprs
    Do stmts lastAction -> Do <$> traverse parseStmt stmts <*> parse lastAction
    Literal lit -> pure $ Literal lit
    InfixE pairs last' -> do
        pairs' <- traverse (bitraverse parse (pure . maybe AppOp Op)) pairs
        last'' <- parse last'
        go' pairs' last''
    Function lhs rhs -> Function <$> parse lhs <*> parse rhs
    Q q vis e binder body -> Q q vis e <$> parseBinder binder <*> parse body
    VariantT row -> VariantT <$> traverse parse row
    RecordT row -> RecordT <$> traverse parse row
  where
    go' :: Ctx es => [(Expr 'Fixity, Op)] -> Expr 'Fixity -> Eff es (Expr_ 'Fixity)
    go' pairs last' = go [] pairs <&> unLoc
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
        fixity <- lookupFixity mbOp <$> ask @FixityMap
        let loc = zipLocOf lhs rhs
        pure $ Located loc case (mbOp, fixity, lhs) of
            (AppOp, _, _) -> App lhs rhs
            (Op op, InfixChain, L (App (Located nloc (Name op')) (L (List args))))
                | op == op' ->
                    App (Located nloc $ Name op') (Located loc $ List $ args <> [rhs])
            (Op op, InfixChain, _) -> App (Located (getLoc op) (Name op)) $ Located loc $ List [lhs, rhs]
            (Op op, _, _) -> App (Located (zipLocOf lhs op) $ App (Located (getLoc op) (Name op)) lhs) rhs

-- * Helpers

parseBinder :: Ctx es => VarBinder DependencyRes -> Eff es (VarBinder 'Fixity)
parseBinder VarBinder{var, kind} = VarBinder var <$> traverse parse kind

parsePattern :: Ctx es => Pattern 'DependencyRes -> Eff es (Pattern 'Fixity)
parsePattern = traverse \case
    VarP name -> pure $ VarP name
    WildcardP name -> pure $ WildcardP name
    AnnotationP pat ty -> AnnotationP <$> parsePattern pat <*> parse ty
    ConstructorP name pats -> ConstructorP name <$> traverse parsePattern pats
    VariantP name pat -> VariantP name <$> parsePattern pat
    RecordP row -> RecordP <$> traverse parsePattern row
    ListP pats -> ListP <$> traverse parsePattern pats
    LiteralP lit -> pure $ LiteralP lit
    InfixP pairs l -> do
        pairs' <- traverse (bitraverse parsePattern pure) pairs
        l' <- parsePattern l
        go' pairs' l'
  where
    go' :: Ctx es => [(Pattern 'Fixity, Name)] -> Pattern 'Fixity -> Eff es (Pattern_ 'Fixity)
    go' pairs last' = go [] pairs <&> unLoc
      where
        go :: Ctx es => [(Pattern 'Fixity, Name)] -> [(Pattern 'Fixity, Name)] -> Eff es (Pattern 'Fixity)
        go [] [] = pure last'
        go ((x, op) : rest) [] =
            pure
                let last'' = conP op x last'
                 in foldl' (\acc (z, op') -> conP op' z acc) last'' rest
        go [] ((x, op) : rest) = go [(x, op)] rest
        go ((x, prev) : stack) ((y, next) : rest) = do
            newStack <- pop (y, next) ((x, prev) :| stack)
            go newStack rest

    conP :: Name -> Pattern 'Fixity -> Pattern 'Fixity -> Pattern 'Fixity
    conP conOp lhs rhs = ConstructorP conOp [lhs, rhs] :@ zipLocOf lhs rhs

    pop :: Ctx es => (Pattern 'Fixity, Name) -> NonEmpty (Pattern 'Fixity, Name) -> Eff es [(Pattern 'Fixity, Name)]
    pop (y, next) ((x, prev) :| stack) =
        priority (Op prev) (Op next) >>= \case
            Right' -> pure ((y, next) : (x, prev) : stack)
            Left' -> do
                let newX = conP prev x y
                case NE.nonEmpty stack of
                    Nothing -> pure [(newX, next)]
                    Just stack' -> pop (newX, next) stack'

parseBinding :: Ctx es => Binding 'DependencyRes -> Eff es (Binding 'Fixity)
parseBinding = \case
    ValueB pat expr -> ValueB <$> parsePattern pat <*> parse expr
    FunctionB name pats body -> FunctionB name <$> traverse parsePattern pats <*> parse body

parseStmt :: Ctx es => DoStatement 'DependencyRes -> Eff es (DoStatement 'Fixity)
parseStmt = traverse \case
    Bind pat body -> Bind <$> parsePattern pat <*> parse body
    With pat body -> With <$> parsePattern pat <*> parse body
    DoLet binding -> DoLet <$> parseBinding binding
    Action expr -> Action <$> parse expr
