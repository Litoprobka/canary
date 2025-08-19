module Desugar where

import Common
import Control.Monad.ST
import Data.Foldable1 (foldl1')
import Data.IdMap qualified as IdMap
import Data.IntMap.Strict qualified as IntMap
import Data.Map.Strict qualified as Map
import Data.Row (OpenName)
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
    E.Lambda vis pat body -> C.Lambda vis "x" $ go (E.Case (E.Var (Index 0)) [(pat, E.liftAt 1 (Level $ E.patternArity pat) body)])
    E.Let binding expr -> case binding of
        E.ValueB name body -> C.Let (toSimpleName_ name) (desugar body) (desugar expr)
        E.FunctionB name args body -> desugar $ E.Let (E.ValueB name asLambda) expr
          where
            asLambda = foldr (uncurry E.Lambda) body args
    E.LetRec _bindings _body -> error "todo: letrec desugar"
    E.Case arg [] -> C.Case (go arg) []
    E.Case arg (m : rest) -> fromTree' (go arg) $ foldl1' (merge const) $ fmap (uncurry toTree . second go) (m :| rest)
    E.Match [] -> error "empty match"
    E.Match (m@(pats, _) : rest) ->
        let len = length pats
            mkBranch (pats, body) = toTreeNested (toList $ fmap E.unTyped pats) (go body)
            tree = foldl1' (mergeNested const) $ fmap mkBranch (m :| rest)
            body = fromNested (\_ term -> term) (Level len) (fmap Level [0 .. pred len]) tree
         in foldr (\i -> C.Lambda Visible (Name' $ "x" <> show i)) body [0 .. pred len]
    E.If cond true false ->
        C.Case
            (go cond)
            [ (C.ConstructorP TrueName [], go true)
            , (C.VarP (Wildcard' "_"), C.lift 1 $ go false)
            ]
    E.Variant name -> C.Lambda Visible "x" $ C.Variant name (C.Var $ Index 0)
    E.Record fields -> C.Record $ fmap go fields
    E.RecordAccess record field ->
        let arg = go record
         in C.Case arg [(C.RecordP ((field, unLoc field) :< Nil), C.Var (Index 0))]
    {- `record.field` gets desugared to
        case record of
            {field} -> field
    -}
    E.Sigma x y -> C.Sigma (go x) (go y)
    E.List ty xs ->
        let cty = go ty
         in foldr
                (\x xs -> C.Con ConsName $ fromList [(Implicit, cty), (Visible, go x), (Visible, xs)])
                (C.Con NilName $ fromList [(Implicit, cty)])
                xs
    E.Do{} -> error "todo: desugar do blocks"
    E.Q q vis er (var ::: kind) body -> C.Q q vis er var (go kind) (go body)
    E.VariantT row -> C.TyCon VariantName $ oneVis $ C.Row $ fmap go row
    E.RecordT row -> C.TyCon RecordName $ oneVis $ C.Row $ fmap go row
    E.Core coreTerm -> coreTerm
  where
    oneVis x = (Visible, x) :< Nil
    go = desugar

data Nested a
    = NotNested a
    | Nested (CaseTree (Nested a))
    deriving (Show)

data CaseTree a
    = Leaf a
    | Branch (CaseTreeNE a) (Maybe a)
    deriving (Show)

-- here, visibilities and names are only preserved for pretty-printing
data Args = Args Int [(Visibility, SimpleName_)] deriving (Show)

newtype CaseTreeNE a
    = ConB (IdMap Name_ (Args, Nested a))
    deriving (Show)

toTree :: EPattern -> a -> CaseTree a
toTree pat body = case pat of
    E.VarP _ -> Leaf body
    E.WildcardP _ -> Leaf body
    E.ConstructorP con args -> Branch (ConB $ IdMap.one con (mkArgs args, toTreeNested (snd <$> toList args) body)) Nothing
    _ -> error "todo"
  where
    mkArgs args = Args (length args) (zipWith (\i (vis, argPat) -> (vis, argName i argPat)) [0 ..] args)
    argName (i :: Int) = \case
        E.VarP name -> name
        E.WildcardP txt -> Wildcard' txt
        _ -> Name' $ "x" <> show i

toTreeNested :: [EPattern] -> a -> Nested a
toTreeNested [] x = NotNested x
toTreeNested (pat : pats) x = Nested $ toTree pat (toTreeNested pats x)

fromTree' :: CoreTerm -> CaseTree CoreTerm -> CoreTerm
fromTree' arg = fromTree (\_ term -> term) arg (Level 0)

fromTree :: (Level -> a -> CoreTerm) -> CoreTerm -> Level -> CaseTree a -> CoreTerm
fromTree toTerm arg lvl = \case
    Leaf body -> toTerm lvl body
    Branch cases Nothing -> C.Case arg $ mkBranches cases
    Branch cases (Just def) -> C.Case arg $ mkBranches cases <> [(C.VarP (Wildcard' "_"), toTerm lvl def)]
  where
    mkBranches (ConB cases) =
        fmap
            ( \(name, (Args n args, nested)) -> (C.ConstructorP name args, fromNested toTerm (lvl `incLevel` n) [lvl .. lvl `incLevel` pred n] nested)
            )
            (IdMap.toList cases)

-- this should pass the indexes
{-
  case _ of
    (x, y, z) -> case x@2 of
      w -> case x@3 of
        _ -> _
-}
fromNested :: (Level -> a -> CoreTerm) -> Level -> [Level] -> Nested a -> CoreTerm
fromNested toTerm lvl = \cases
    _ (NotNested term) -> toTerm lvl term
    (argLvl : lvls) (Nested nested) -> fromTree (flip (fromNested toTerm) lvls) (C.Var $ levelToIndex lvl argLvl) lvl nested
    _ _ -> error "nested-pattern length mismatch"

merge :: (a -> a -> a) -> CaseTree a -> CaseTree a -> CaseTree a
merge f = \cases
    (Leaf lhs) (Leaf rhs) -> Leaf $ f lhs rhs
    (Branch (ConB lhs) lhsDef) (Leaf x) -> Branch (ConB $ (fmap . fmap) (flip (mergeNested f) (NotNested x)) lhs) (Just $ mergeDefaultR f lhsDef x)
    (Leaf x) (Branch (ConB rhs) rhsDef) -> Branch (ConB $ (fmap . fmap) (mergeNested f (NotNested x)) rhs) (Just $ mergeDefaultL f x rhsDef)
    -- is this right? should we also merge the default case into the branches?
    (Branch lhs lhsDef) (Branch rhs rhsDef) -> Branch (mergeNE f (lhs, lhsDef) (rhs, rhsDef)) mergedDefaults
      where
        mergedDefaults = case (lhsDef, rhsDef) of
            (Just lhsDef, Just rhsDef) -> Just $ f lhsDef rhsDef
            (lhsDef, Nothing) -> lhsDef
            (Nothing, rhsDef) -> rhsDef

mergeNE :: (a -> a -> a) -> (CaseTreeNE a, Maybe a) -> (CaseTreeNE a, Maybe a) -> CaseTreeNE a
mergeNE f (ConB lhs, lhsDef) (ConB rhs, rhsDef) =
    ConB $
        IdMap.merge
            (leftBiasedArg $ mergeNested f)
            (fmap $ \l -> mergeDefaultL (mergeNested f) l (fmap NotNested rhsDef))
            (fmap $ \r -> mergeDefaultR (mergeNested f) (fmap NotNested lhsDef) r)
            lhs
            rhs
  where
    leftBiasedArg :: (a -> a -> a) -> (b, a) -> (b, a) -> (b, a)
    leftBiasedArg f (arg, l) (_, r) = (arg, f l r)

mergeDefaultL :: (a -> b -> a) -> a -> Maybe b -> a
mergeDefaultL = foldl'

mergeDefaultR :: (a -> b -> b) -> Maybe a -> b -> b
mergeDefaultR f = flip (foldr f)

mergeNested :: (a -> a -> a) -> Nested a -> Nested a -> Nested a
mergeNested f = \cases
    (NotNested lhs) (NotNested rhs) -> NotNested $ f lhs rhs
    (Nested lhs) (NotNested x) -> Nested $ merge (mergeNested f) lhs (Leaf (NotNested x))
    (NotNested x) (Nested rhs) -> Nested $ merge (mergeNested f) (Leaf (NotNested x)) rhs
    (Nested lhs) (Nested rhs) -> Nested $ merge (mergeNested f) lhs rhs
