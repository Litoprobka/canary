module Desugar where

import Common
import Error.Diagnose (Position (..))
import LangPrelude
import Syntax
import Syntax.Core qualified as C
import Syntax.Elaborated qualified as E

-- TODO: properly handle recursive bindings (that is, don't infinitely loop on them)
desugar :: ETerm -> CoreTerm
desugar = \case
    E.Var index -> C.Var index
    E.Name name -> C.Name name
    E.Literal lit -> C.Literal lit
    E.App vis lhs rhs -> C.App vis (go lhs) (go rhs)
    E.Lambda vis (E.VarP arg) body -> C.Lambda vis arg (go body)
    E.Lambda vis (E.WildcardP arg) body -> C.Lambda vis (Name' arg) (go body)
    E.Lambda vis pat body -> C.Lambda vis (Name' "x") $ C.lift 1 $ go (E.Case (E.Var (Index (-1))) [(pat, body)])
    E.Let binding expr -> case binding of
        E.ValueB name body -> C.Let (toSimpleName_ $ unLoc name) (desugar body) (C.lift 1 $ desugar expr)
        E.FunctionB name args body -> desugar $ E.Let (E.ValueB name asLambda) expr
          where
            asLambda = foldr (uncurry E.Lambda) body args
    E.LetRec _bindings _body -> error "todo: letrec desugar"
    E.Case arg matches -> C.Case (go arg) $ fmap (bimap flattenPattern go) matches
    E.Match _matches@((_ :| [], _) : _) -> error "todo: lift in match"
    {-do
       name <- freshName $ Name' "matchArg" :@ loc
       matches' <- for matches \case
           ((pat ::: _) :| [], body) -> bitraverse flattenPattern go (pat, body)
           _ -> internalError loc "inconsistent pattern count in a match expression"
       pure $ C.Lambda name $ C.Case (C.Name name) matches'-}
    E.Match _ -> error "todo: multi-arg match desugar"
    E.If cond true false ->
        C.Case
            (go cond)
            [ (C.ConstructorP (TrueName :@ loc) [], go true)
            , (C.WildcardP "", go false)
            ]
    E.Variant name -> C.Lambda Visible (Name' "x") $ C.Variant name (C.Var $ Index 0)
    E.Record fields -> C.Record $ fmap go fields
    E.RecordAccess record field ->
        let arg = go record
         in C.Case arg [(C.RecordP (one (field, unLoc field)), C.Var (Index 0))]
    {- `record.field` gets desugared to
        case record of
            {field} -> field
    -}
    E.Sigma x y -> C.Sigma (go x) (go y)
    E.List xs -> foldr ((C.App Visible . C.App Visible cons) . go) nil xs
    E.Do{} -> error "todo: desugar do blocks"
    E.Q q vis er (var ::: kind) body -> C.Q q vis er var (go kind) (go body)
    E.VariantT row -> C.VariantT $ fmap go row
    E.RecordT row -> C.RecordT $ fmap go row
    E.UniVar uni -> C.UniVar uni
    E.AppPruning lhs pruning -> C.AppPruning (desugar lhs) pruning
  where
    go = desugar
    cons = C.Name $ ConsName :@ loc
    nil = C.Name $ NilName :@ loc
    loc = Loc Position{begin = (0, 0), end = (0, 0), file = "<eval>"}

    -- we only support non-nested patterns for now
    flattenPattern :: EPattern -> CorePattern
    flattenPattern p = case p of
        E.VarP name -> C.VarP name
        E.WildcardP name -> C.WildcardP name
        E.ConstructorP name pats -> C.ConstructorP name (fmap asVar pats)
        E.VariantP name pat -> C.VariantP name (asVar pat)
        E.RecordP row -> C.RecordP $ fmap asVar row
        E.SigmaP lhs rhs -> C.SigmaP (asVar lhs) (asVar rhs)
        E.ListP _ -> error "todo: list pattern desugaring"
        E.LiteralP lit -> C.LiteralP lit

    asVar (E.VarP name) = name
    asVar (E.WildcardP txt) = Wildcard' txt
    asVar _ = error "todo: nested patterns"

-- idk, perhaps typecheck should produce CoreTerm right away
resugar :: CoreTerm -> ETerm
resugar = \case
    C.Var index -> E.Var index
    C.Name name -> E.Name name
    C.TyCon name args -> foldl' (E.App Visible) (E.Name name) (fmap resugar args)
    C.Con name args -> foldl' (E.App Visible) (E.Name name) (fmap resugar args)
    C.Variant name arg -> E.App Visible (E.Variant name) (resugar arg)
    C.Lambda vis var body -> E.Lambda vis (E.VarP var) $ resugar body
    C.App vis lhs rhs -> E.App vis (resugar lhs) (resugar rhs)
    C.Case arg matches -> E.Case (resugar arg) $ fmap (bimap resugarPattern resugar) matches
    C.Let _name _expr _body -> error "bindings are annoying" -- E.Let (E.VarP name) (resugar expr) (resugar body)
    C.Literal lit -> E.Literal lit
    C.Record row -> E.Record (fmap resugar row)
    C.Sigma lhs rhs -> E.Sigma (resugar lhs) (resugar rhs)
    C.Q q v e var ty body -> E.Q q v e (var ::: resugar ty) (resugar body)
    C.VariantT row -> E.VariantT $ fmap resugar row
    C.RecordT row -> E.RecordT $ fmap resugar row
    C.UniVar uni -> E.UniVar uni
    C.AppPruning lhs pruning -> E.AppPruning (resugar lhs) pruning
  where
    resugarPattern = \case
        C.VarP name -> E.VarP name
        C.WildcardP txt -> E.WildcardP txt
        C.ConstructorP name args -> E.ConstructorP name $ fmap E.VarP args
        C.VariantP name arg -> E.VariantP name $ E.VarP arg
        C.RecordP nameRow -> E.RecordP $ fmap E.VarP nameRow
        C.SigmaP lhs rhs -> E.SigmaP (E.VarP lhs) (E.VarP rhs)
        C.LiteralP lit -> E.LiteralP lit
