{-# LANGUAGE ImplicitParams #-}

module Desugar where

import Common
import Data.Foldable1 (foldl1')
import Data.IdMap qualified as IdMap
import Data.IdMap qualified as Map
import Data.Row (ExtRow, OpenName)
import LangPrelude
import Syntax
import Syntax.Core qualified as C
import Syntax.Elaborated (EBinding)
import Syntax.Elaborated qualified as E

if_ :: CoreTerm -> CoreTerm -> CoreTerm -> CoreTerm
if_ cond true false =
    C.Case cond $
        C.CaseWD
            { branches =
                ( C.ConCase $
                    IdMap.fromList
                        [ (TrueName, (C.ConstructorP TrueName [], true))
                        , (FalseName, (C.ConstructorP FalseName [], false))
                        ]
                )
            , def = Nothing
            }

case_ :: AdjConstructors -> CoreTerm -> [(EPattern, CoreTerm)] -> CoreTerm
case_ _ arg [] = C.Case arg C.CaseWD{branches = C.ConCase Map.empty, def = Nothing}
case_ adjConstructors arg (m : rest) =
    let ?adjConstructors = adjConstructors
     in fromTree' arg $ foldl1' (merge const) $ fmap (uncurry toTree) (m :| rest)

match :: AdjConstructors -> [(NonEmpty (Typed EPattern), CoreTerm)] -> CoreTerm
match _ [] = error "empty match"
match adjConstructors (m@(pats, _) : rest) =
    let ?adjConstructors = adjConstructors
     in let len = length pats
            types = toList $ fmap (\(_ ::: ty) -> ty) pats
            mkBranch (pats, body) = toTreeNested (toList $ fmap E.unTyped pats) body
            tree = foldl1' (mergeNested const) $ fmap mkBranch (m :| rest)
            body = fromNested (\_ term -> term) (Level len) (fmap Level [0 .. pred len]) tree
         in foldr (\(i, ty) -> C.Lambda Visible (Name' $ "x" <> show @_ @Int i) ty) body (zip [0 ..] types)

list :: CoreTerm -> [CoreTerm] -> CoreTerm
list ty =
    foldr
        (\x xs -> C.Con ConsName $ fromList [(Implicit, ty), (Visible, x), (Visible, xs)])
        (C.Con NilName $ fromList [(Implicit, ty)])

let_ :: EBinding -> CoreTerm -> CoreTerm
let_ binding expr = case binding of
    E.ValueB name body -> C.Let (toSimpleName_ name) body expr
    E.FunctionB name args body -> C.Let (toSimpleName_ name) asLambda expr
      where
        asLambda = foldr (\(vis, name) -> C.Lambda vis name (error "todo: let arg types?")) body (fmap (second toSimpleName_) args)

variant :: OpenName -> CoreType -> CoreTerm
variant name argType = C.Lambda Visible "x" argType $ C.Variant name (C.Var $ Index 0)

variantType :: ExtRow CoreType -> CoreTerm
variantType row = C.TyCon VariantName $ (Visible, C.Row row) :< Nil

recordType :: ExtRow CoreType -> CoreTerm
recordType row = C.TyCon RecordName $ (Visible, C.Row row) :< Nil

data Nested a
    = NotNested a
    | Nested (CaseTree (Nested a))
    deriving (Show)

data CaseTree a
    = Leaf a -- do we need something akin to as-patterns? if we merge a var-branch with a con-branch,
    -- we'd have to shift indices in both
    -- although we'd have to shift indices either way
    -- when merging a var-branch with different con-branches (e.g. Just and Nothing)
    | Branch (CaseTreeNE a) (Maybe a)
    deriving (Show)

-- here, visibilities and names are only preserved for pretty-printing
data Args = Args Int [(Visibility, SimpleName_)] deriving (Show)

newtype CaseTreeNE a
    = ConB (IdMap Name_ (Args, Nested a))
    -- we don't really need 'Nested', because branches for a specific constructor always have the same amount of arguments
    -- and when merging a Branch with a wildcard, we also know how many subbranches to skip
    deriving (Show)

-- todo: all branch bodies should be extracted to outer scoped let-bound lambdas
-- that way, we'd be able to avoid renaming shenanigans
-- extracting their types may prove to be... complicated

toTree :: EPattern -> a -> CaseTree a
toTree pat body = case pat of
    E.VarP _ -> Leaf body
    E.WildcardP _ -> Leaf body
    E.ConstructorP con args -> Branch (ConB $ IdMap.one con (mkArgs args, toTreeNested (snd <$> toList args) body)) Nothing
    _ -> error "desugar other patterns: todo"
  where
    mkArgs args = Args (length args) (zipWith (\i (vis, argPat) -> (vis, argName i argPat)) [0 ..] args)
    argName (i :: Int) = \case
        E.VarP name -> name
        E.WildcardP txt -> Wildcard' txt
        _ -> Name' $ "x" <> show i

toTreeNested :: [EPattern] -> a -> Nested a
toTreeNested [] x = NotNested x
toTreeNested (pat : pats) x = Nested $ toTree pat (toTreeNested pats x)

fromTree' :: (?adjConstructors :: AdjConstructors) => CoreTerm -> CaseTree CoreTerm -> CoreTerm
fromTree' arg = fromTree (\_ term -> term) arg (Level 0)

type AdjConstructors =
    IdMap
        Name_ -- any constructor of a type
        (IdMap Name_ ())

fromTree :: (?adjConstructors :: AdjConstructors) => (Level -> a -> CoreTerm) -> CoreTerm -> Level -> CaseTree a -> CoreTerm
fromTree toTerm arg lvl = \case
    Leaf body -> toTerm lvl body
    Branch (ConB cases) Nothing -> C.Case arg $ C.CaseWD (mkBranches cases) Nothing
    -- ideally, we should drop the catch-all case when all patterns are covered,
    -- and turn the catch-all case into a normal case when all but one are covered
    --
    -- e.g.
    -- `match True -> 1; False -> 2; _ -> 3`
    -- should turn into
    -- `match True -> 1; False -> 2`
    --
    -- `match True -> 1; _ -> 2`
    -- `match True -> 1; False -> 2`
    Branch (ConB cases) (Just def) ->
        let mbConstrs = do
                anyCon <- listToMaybe $ IdMap.keys cases
                IdMap.lookup anyCon ?adjConstructors
         in case mbConstrs of
                Just constrs
                    | IdMap.size cases == IdMap.size constrs ->
                        C.Case arg $ C.CaseWD (mkBranches cases) Nothing
                -- this case needs an arg count to construct the proper Nested
                {-
                  | IdMap.size cases == IdMap.size constrs - 1 ->
                    let lastCase = _ <$ IdMap.difference constrs cases
                    in C.Case arg $ C.CaseWD (mkBranches $ cases <> lastCase) Nothing
                -}
                _ -> C.Case arg $ C.CaseWD (mkBranches cases) (Just (Wildcard' "_", toTerm lvl def))
  where
    mkBranches cases =
        C.ConCase $
            cases & Map.mapWithKey \name (Args n args, nested) -> (C.ConstructorP name args, fromNested toTerm (lvl `incLevel` n) [lvl .. lvl `incLevel` pred n] nested)

-- this should pass the indexes
{-
  case _ of
    (x, y, z) -> case x@2 of
      w -> case x@3 of
        _ -> _
-}
fromNested :: (?adjConstructors :: AdjConstructors) => (Level -> a -> CoreTerm) -> Level -> [Level] -> Nested a -> CoreTerm
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
    -- probably not, because the per-constructor branches are always at least as specific as the fallback branch
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
