module Desugar where

import Common
import Error.Diagnose (Position (..))
import LangPrelude
import Syntax
import Syntax.Core qualified as C
import Syntax.Elaborated qualified as E

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
    E.Match matches@((_ :| [], _) : _) -> C.Lambda Visible (Name' "x") $ C.lift 1 $ C.Case (C.Var (Index 0)) (fmap desugarMatchBranch matches)
      where
        desugarMatchBranch ((pat ::: _) :| _, body) = (flattenPattern pat, go body)
    E.Match _ -> error "todo: multi-arg match desugar"
    E.If cond true false ->
        C.Case
            (go cond)
            [ (C.ConstructorP TrueName [], go true)
            , (C.WildcardP "_", C.lift 1 $ go false)
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
    E.List ty xs ->
        let cty = go ty
         in foldr
                (\x xs -> C.Con cons $ fromList [(Implicit, cty), (Visible, go x), (Visible, xs)])
                (C.Con nil $ fromList [(Implicit, cty)])
                xs
    E.Do{} -> error "todo: desugar do blocks"
    E.Q q vis er (var ::: kind) body -> C.Q q vis er var (go kind) (go body)
    E.VariantT row -> C.VariantT $ fmap go row
    E.RecordT row -> C.RecordT $ fmap go row
    E.Core coreTerm -> coreTerm
  where
    go = desugar
    cons = ConsName :@ loc
    nil = NilName :@ loc
    loc = Loc Position{begin = (0, 0), end = (0, 0), file = "<eval>"}

    -- we only support non-nested patterns for now
    flattenPattern :: EPattern -> CorePattern
    flattenPattern p = case p of
        E.VarP name -> C.VarP name
        E.WildcardP name -> C.WildcardP name
        E.ConstructorP name pats -> C.ConstructorP (unLoc name) ((fmap . fmap) asVar pats)
        E.VariantP name pat -> C.VariantP name (asVar pat)
        E.RecordP row -> C.RecordP $ fmap asVar row
        E.SigmaP vis lhs rhs -> C.SigmaP vis (asVar lhs) (asVar rhs)
        E.ListP [_x] -> error "todo: list patterns need a type" -- C.ConstructorP ConsName [(Implicit, ty), (Visible, asVar x)]
        E.ListP [] -> error "todo: list patterns need a type" -- C.ConstructorP NilName [(Implicit, ty)]
        E.ListP _ -> error "todo: list pattern desugaring"
        E.LiteralP lit -> C.LiteralP lit

    asVar (E.VarP name) = name
    asVar (E.WildcardP txt) = Wildcard' txt
    asVar _ = error "todo: nested patterns"
