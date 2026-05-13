{-# LANGUAGE ImplicitParams #-}

module Desugar where

import Common
import Data.Foldable1 (foldl1')
import Data.IdMap qualified as IdMap
import Data.IdMap qualified as Map
import Data.Row (ExtRow, OpenName)
import Data.Vector qualified as Vec
import LangPrelude
import Syntax
import Syntax.Core qualified as C
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
     in let caseTree = foldl1' merge $ fmap (\(pat, body) -> toTree [pat] body) (m :| rest)
         in fromTree [const arg] (Level 0) caseTree

match :: AdjConstructors -> [(NonEmpty (Typed EPattern), CoreTerm)] -> CoreTerm
match _ [] = error "empty match"
match adjConstructors (m@(pats, _) : rest) =
    let ?adjConstructors = adjConstructors
     in let len = length pats
            types = toList $ fmap (\(_ ::: ty) -> ty) pats
            mkBranch (pats, body) = toTree (toList $ fmap E.unTyped pats) body
            tree = foldl1' merge $ fmap mkBranch (m :| rest)
            args = (\argLvl newLvl -> C.Var $ levelToIndex newLvl (Level argLvl)) <$> [0 .. pred len]
            body = fromTree args (Level len) tree
         in foldr (\(i, ty) -> C.Lambda Visible (Name' $ "x" <> show @_ @Int i) ty) body (zip [0 ..] types)

list :: CoreTerm -> [CoreTerm] -> CoreTerm
list ty =
    foldr
        (\x xs -> C.Con ConsName $ fromList [(Implicit, ty), (Visible, x), (Visible, xs)])
        (C.Con NilName $ fromList [(Implicit, ty)])

let_ :: Name_ -> CoreTerm -> CoreTerm -> CoreTerm
let_ name body expr = C.Let (toSimpleName_ name) body expr

variant :: OpenName -> CoreType -> CoreTerm
variant name argType = C.Lambda Visible "x" argType $ C.Variant name (C.Var $ Index 0)

variantType :: ExtRow CoreType -> CoreTerm
variantType row = C.TyCon VariantName $ (Visible, C.Row row) :< Nil

recordType :: ExtRow CoreType -> CoreTerm
recordType row = C.TyCon RecordName $ (Visible, C.Row row) :< Nil

data CaseTree a
    = Leaf a
    | Var (Maybe SimpleName_) (CaseTree a) -- var patterns are separate from CaseBranch, because they can't have a default case nor any branching
    | Branch (CaseBranch a) (Maybe (CaseTree a))
    deriving (Show)

-- here, visibilities and names are only preserved for pretty-printing
data Args = Args Int [(Visibility, SimpleName_)] deriving (Show)

newtype CaseBranch a
    = ConB (IdMap Name_ (Args, CaseTree a))
    deriving (Show)

-- todo: all branch bodies should be extracted to outer scoped let-bound lambdas
-- that way, we'd be able to avoid renaming shenanigans
-- extracting their types may prove to be... complicated

type AdjConstructors =
    IdMap
        Name_ -- any constructor of a type
        (IdMap Name_ (Vector (Visibility, CoreType)))

toTree :: [EPattern] -> a -> CaseTree a
toTree [] body = Leaf body
toTree (pat : pats) body = case pat of
    E.VarP name -> Var (Just name) (toTree pats body)
    E.WildcardP name -> Var (Just $ Wildcard' name) (toTree pats body)
    E.ConstructorP con args ->
        let conPats = snd <$> toList args
            subtree = toTree (conPats <> pats) body
         in Branch (ConB $ IdMap.one con (mkArgs args, subtree)) Nothing
    _ -> error "desugar other patterns: todo"
  where
    mkArgs args = Args (length args) (zipWith (\i (vis, argPat) -> (vis, argName i argPat)) [0 ..] args)
    argName (i :: Int) = \case
        E.VarP name -> name
        E.WildcardP txt -> Wildcard' txt
        _ -> Name' $ "y" <> show i

fromTree :: (?adjConstructors :: AdjConstructors) => [Level -> CoreTerm] -> Level -> CaseTree CoreTerm -> CoreTerm
fromTree [] _lvl (Leaf body) = body
fromTree [] _lvl _ = error "fromTree: tree requires more arguments than given"
fromTree (mkArg : args) lvl tree = case tree of
    Leaf body -> body -- short-circuit case. Do we need to do something with the index?
    Var (Just name) subtree -> C.Let name arg (fromTree args (succ lvl) subtree)
    Var Nothing subtree -> fromTree args lvl subtree
    Branch (ConB cases) Nothing -> C.Case arg $ C.CaseWD (mkBranches cases) Nothing
    -- we drop the catch-all case when all patterns are covered,
    -- and turn the catch-all case into a normal case when all but one are covered
    -- see `test/nested-pattern-matching/three-bools` for an example of how this works in practice
    --
    -- e.g.
    -- `match True -> 1; False -> 2; _ -> 3`
    -- ==>
    -- `match True -> 1; False -> 2`
    --
    -- `match True -> 1; _ -> 2`
    -- ==>
    -- `match True -> 1; False -> 2`
    Branch (ConB cases) (Just def) ->
        let mbConstrs = do
                anyCon <- listToMaybe $ IdMap.keys cases
                IdMap.lookup anyCon ?adjConstructors
         in case mbConstrs of
                Just constrs
                    | IdMap.size cases == IdMap.size constrs ->
                        C.Case arg $ C.CaseWD (mkBranches cases) Nothing
                    | IdMap.size cases == IdMap.size constrs - 1 ->
                        let lastCase = (\vises -> (mkArgs vises, wrapInVars (Vec.length vises) def)) <$> IdMap.difference constrs cases
                         in C.Case arg $ C.CaseWD (mkBranches $ cases <> lastCase) Nothing
                _ -> C.Case arg $ C.CaseWD (mkBranches cases) (Just (Wildcard' "_", fromTree args (succ lvl) def))
  where
    arg = mkArg lvl

    mkBranches cases =
        C.ConCase $
            cases & Map.mapWithKey \name (Args n argNames, subtree) ->
                let conArgs = (\argLvl newLvl -> C.Var $ levelToIndex newLvl argLvl) <$> [lvl .. lvl `incLevel` pred n]
                 in (C.ConstructorP name argNames, fromTree (conArgs <> args) (lvl `incLevel` n) subtree)

    mkArgs vises = Args (Vec.length vises) $ ((,Wildcard' "_") . fst) <$> toList vises

wrapInVars :: Int -> CaseTree a -> CaseTree a
wrapInVars 0 subtree = subtree
wrapInVars n subtree = Var Nothing (wrapInVars (pred n) subtree)

merge :: CaseTree a -> CaseTree a -> CaseTree a
merge = \cases
    leaf@Leaf{} _ -> leaf
    lhs _ | isCovering lhs -> lhs
    (Var lhsName lhs) (Var rhsName rhs) -> Var (lhsName <|> rhsName) (merge lhs rhs)
    (Var name lhs) leaf@Leaf{} -> Var name (merge lhs leaf) -- may cause a level mismatch
    (Branch (ConB lhs) lhsDef) leaf@Leaf{} ->
        let cases = lhs & (fmap . fmap) (`merge` leaf)
         in Branch (ConB cases) (Just $ mergeDefaultR merge lhsDef leaf)
    -- these two cases may cause a level mismatch, I'm not sure
    (Branch (ConB lhs) lhsDef) (Var _ rhs) ->
        let cases = lhs & (fmap . fmap) (`merge` rhs)
         in Branch (ConB cases) (Just $ mergeDefaultR merge lhsDef rhs)
    (Var _ lhs) (Branch (ConB rhs) rhsDef) ->
        let cases = rhs & (fmap . fmap) (merge lhs)
         in Branch (ConB cases) (Just $ mergeDefaultL merge lhs rhsDef)
    (Branch lhs lhsDef) (Branch rhs rhsDef) -> Branch (mergeBranch (lhs, lhsDef) (rhs, rhsDef)) mergedDefaults
      where
        mergedDefaults = case (lhsDef, rhsDef) of
            (Just lhsDef, Just rhsDef)
                | isCovering lhsDef -> Just lhsDef
                | otherwise -> Just $ merge lhsDef rhsDef
            (lhsDef, Nothing) -> lhsDef
            (Nothing, rhsDef) -> rhsDef
  where
    isCovering = \case
        Leaf{} -> True
        Var _ subtree -> isCovering subtree
        Branch _ (Just def) -> isCovering def
        _ -> False

mergeBranch :: (CaseBranch a, Maybe (CaseTree a)) -> (CaseBranch a, Maybe (CaseTree a)) -> CaseBranch a
mergeBranch (ConB lhs, lhsDef) (ConB rhs, rhsDef) =
    ConB $
        Map.merge
            (leftBiasedArg merge)
            (\(args@(Args n _), l) -> (args, mergeDefaultL merge l (wrapInVars n <$> rhsDef)))
            (\(args@(Args n _), r) -> (args, mergeDefaultR merge (wrapInVars n <$> lhsDef) r))
            lhs
            rhs
  where
    leftBiasedArg :: (a -> a -> a) -> (b, a) -> (b, a) -> (b, a)
    leftBiasedArg f (arg, l) (_, r) = (arg, f l r)

mergeDefaultL :: (a -> b -> a) -> a -> Maybe b -> a
mergeDefaultL = foldl'

mergeDefaultR :: (a -> b -> b) -> Maybe a -> b -> b
mergeDefaultR f = flip (foldr f)
