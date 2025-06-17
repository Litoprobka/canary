module TypeChecker.Exhaustiveness where

import LangPrelude

{-
-- | a tree of unmatched patterns
newtype MatchTree = SumMatch (IdMap Name MatchTree)

allMatched :: MatchTree -> Bool
allMatched (SumMatch tree) = all allMatched tree

data Pat'
    = Var
    | Con Name Pat' -- multi-arg patterns are treated as `Pat name (Product [arg1, arg2])`
    | Prod [Pat']

prune :: Pat' -> MatchTree -> MatchTree
prune Var _ = SumMatch Map.empty
prune (Con name nested) (SumMatch tree) = SumMatch $ Map.adjust (prune nested) name tree
prune (Prod (pat : pats)) (SumMatch tree) = SumMatch $ adjustMatching pat (prune $ Prod pats) tree
prune (Prod []) tree = tree

adjustMatching :: Pat' -> (MatchTree -> MatchTree) -> IdMap Name MatchTree -> IdMap Name MatchTree
adjustMatching Var f = fmap f
adjustMatching (Con name nested) f = Map.mapWithKey \k (SumMatch matches) ->
    SumMatch if k == name then adjustMatching nested f matches else matches
adjustMatching (Prod (pat : pats)) f = adjustMatching pat (\(SumMatch tree) -> SumMatch $ adjustMatching (Prod pats) f tree)
adjustMatching (Prod []) _ = id

-- decay :: [Name] -> MatchTree -> MatchTree
-- decay names nested = SumMatch $ Map.fromList $ map (, nested) names

-}

data Type
    = Unit
    | Tuple [Type]
    | Either Type Type
    | List Type
    deriving (Show, Eq)

data Pattern
    = Var
    | MkTuple [Pattern]
    | L Pattern
    | R Pattern
    | Nil
    | Cons Pattern -- contains a tuple of (head, tail) inside
    deriving (Show, Eq)

data CaseTree a
    = UnitCase ~a
    | TupleCase ~(Nested a)
    | EitherCase ~(Maybe (CaseTree a)) ~(Maybe (CaseTree a))
    | ListCase ~(Maybe (CaseTree a)) ~(Maybe a)
    | NotVisited (forall b. b -> CaseTree b) ~a
    deriving (Functor)

data Nested a
    = Nested (CaseTree (Nested a))
    | NotNested a
    --  | NestedEmpty
    deriving (Functor)

buildCaseTree' :: Type -> Maybe (CaseTree ())
buildCaseTree' ty = Just case buildCaseTree ty () of
    NotVisited f x -> f x
    other -> other

buildCaseTree :: Type -> k -> CaseTree k
buildCaseTree = \case
    Unit -> UnitCase
    (Either l r) -> NotVisited (\k -> EitherCase (Just $ buildCaseTree l k) (Just $ buildCaseTree r k))
    (Tuple xs) -> TupleCase . buildProdTree xs
    (List x) -> NotVisited (\k -> ListCase (Just $ buildCaseTree (Tuple [x, List x]) k) (Just k))

buildProdTree :: [Type] -> k -> Nested k
buildProdTree [] = NotNested
buildProdTree (t : ts) = Nested . NotVisited (buildCaseTree t) . buildProdTree ts

prunePattern :: Pattern -> (a -> Maybe a) -> CaseTree a -> Maybe (CaseTree a)
prunePattern = \cases
    _ _ (EitherCase Nothing Nothing) -> Nothing
    _ _ (ListCase Nothing Nothing) -> Nothing
    Var k (NotVisited f x) -> NotVisited f <$> k x
    pat k (NotVisited f x) -> prunePattern pat k $ f x
    Var k tree -> mapMaybeTree k tree
    (L l) k (EitherCase lTree rTree) -> Just $ EitherCase (prunePattern l k =<< lTree) rTree
    (R r) k (EitherCase lTree rTree) -> Just $ EitherCase lTree (prunePattern r k =<< rTree)
    (MkTuple pats) k (TupleCase nested) -> TupleCase <$> pruneProduct pats k nested
    (Cons inner) k (ListCase cons nil) -> Just $ ListCase (prunePattern inner k =<< cons) nil
    Nil k (ListCase cons nil) -> Just $ ListCase cons (k =<< nil)
    _ _ _ -> error "mismatch"

pruneProduct :: [Pattern] -> (a -> Maybe a) -> Nested a -> Maybe (Nested a)
pruneProduct [] k (NotNested x) = NotNested <$> k x
pruneProduct (pat : pats) k (Nested nested) = Nested <$> prunePattern pat (pruneProduct pats k) nested
pruneProduct _ _ _ = error "pruneProduct: length mismatch"

-- this looks like an instance of Filterable
mapMaybeTree :: (a -> Maybe b) -> CaseTree a -> Maybe (CaseTree b)
mapMaybeTree f = \case
    UnitCase x -> UnitCase <$> f x
    TupleCase nested -> TupleCase <$> mapMaybeNested f nested
    EitherCase l r -> Just $ EitherCase (mapMaybeTree f =<< l) (mapMaybeTree f =<< r)
    ListCase cons nil -> Just $ ListCase (mapMaybeTree f =<< cons) (f =<< nil)
    NotVisited build x -> NotVisited build <$> f x

mapMaybeNested :: (a -> Maybe b) -> Nested a -> Maybe (Nested b)
mapMaybeNested f = \case
    NotNested x -> NotNested <$> f x
    Nested nested -> Nested <$> mapMaybeTree (mapMaybeNested f) nested

-- >>> checkCase (List (Either Unit Unit)) [Cons (MkTuple [L Var, Var])]
-- [Nil,Cons (MkTuple [R Var,Var])]
-- >>> checkCase (Tuple [Either Unit Unit, Either Unit Unit, Unit]) [MkTuple [L Var, R Var, Var]]
-- [MkTuple [L Var,L Var,Var],MkTuple [R Var,Var,Var]]
checkCase :: Type -> [Pattern] -> [Pattern]
checkCase t = missingPatterns (\_ x -> x) . foldr (\pat tree -> prunePattern pat (const Nothing) =<< tree) (buildCaseTree' t)

missingPatterns :: (a -> [Pattern] -> [Pattern]) -> Maybe (CaseTree a) -> [Pattern]
missingPatterns _ Nothing = []
missingPatterns k (Just tree) = case tree of
    (UnitCase x) -> k x [Var]
    (NotVisited _ x) -> k x [Var]
    (EitherCase l r) ->
        missingPatterns (\x -> k x . fmap L) l
            <> missingPatterns (\x -> k x . fmap R) r
    (TupleCase nested) -> missingProducts k nested
    (ListCase cons nil) -> maybe [] (`k` [Nil]) nil <> fmap Cons (missingPatterns k cons)

missingProducts :: (a -> [Pattern] -> [Pattern]) -> Nested a -> [Pattern]
missingProducts k (NotNested x) = k x [MkTuple []]
missingProducts k (Nested tree) = missingPatterns (\nested lhs -> missingProducts (nestedCont lhs) nested) (Just tree)
  where
    -- (\x -> k x . fmap UnTuple . liftA2 (:) lhs . fmap fromTuple)
    nestedCont lhs x tailPats = k x do
        head' <- lhs
        tailPat' <- tailPats
        pure $ MkTuple (head' : fromTuple tailPat')

    fromTuple (MkTuple pats) = pats
    fromTuple _ = error "missingProducts: length mismatch"
