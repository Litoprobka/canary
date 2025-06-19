{-# LANGUAGE DerivingVia #-}

module TypeChecker.Exhaustiveness (
    checkExhaustiveness,
    checkExhaustiveness',
    ConstructorTable (..),
    simplifyPatternType,
    simplifyPatternTypeWith,
    checkCompletePattern,
) where

import Common hiding (Wildcard)
import Data.HashMap.Strict qualified as HashMap
import Data.IntMap qualified as IntMap
import Diagnostic
import Effectful.State.Static.Local (get)
import Error.Diagnose (Note (..), Report (..))
import Error.Diagnose qualified as M
import IdMap qualified as Map
import LangPrelude
import Prettyprinter (hsep, parens, vsep)
import Syntax.Elaborated (EPattern, Typed (..))
import Syntax.Elaborated qualified as E
import Syntax.Row (ExtRow (..), OpenName, Row, prettyRecord)
import Syntax.Row qualified as Row
import Syntax.Value qualified as V
import TypeChecker.Backend
import Prelude qualified (show)

checkCompletePattern :: InfEffs es => EPattern -> Eff es ()
checkCompletePattern pat@(_ :@ loc ::: ty) = checkExhaustiveness loc ty [pat]

checkExhaustiveness :: InfEffs es => Loc -> TypeDT_ -> [EPattern] -> Eff es ()
checkExhaustiveness loc ty branches = checkExhaustiveness' loc [ty] (map one branches)

checkExhaustiveness' :: InfEffs es => Loc -> [TypeDT_] -> [[EPattern]] -> Eff es ()
checkExhaustiveness' loc ty branches = do
    conMap <- get @ConstructorTable
    patternTypes <- traverse simplifyPatternType ty
    let branches' = (fmap . fmap) simplifyPattern branches
        nested = buildProdTree conMap patternTypes
        unmatched = checkMatch nested branches'
    unless (null unmatched) do
        nonFatal $
            Err
                Nothing
                "non-exhaustive patterns"
                (mkNotes [(loc, M.This "when checking these patterns")])
                [Note $ vsep ("patterns not matched:" : map (hsep . map pretty) unmatched)]

checkMatch :: Nested () -> [[Pattern]] -> [[Pattern]]
checkMatch initTree = maybe [] (missingPatternsNested const) . foldl' (\tree pats -> pruneNested pats (const Nothing) =<< tree) (Just initTree)

simplifyPattern :: EPattern -> Pattern
simplifyPattern (p :@ _ ::: _) = case p of
    E.VarP{} -> Wildcard
    E.WildcardP{} -> Wildcard
    E.ConstructorP name pats -> Con (unLoc name) $ fmap simplifyPattern pats
    E.ListP pats -> foldr (\x xs -> Con ConsName [simplifyPattern x, xs]) (Con NilName []) pats
    E.VariantP name arg -> VariantP (unLoc name) $ simplifyPattern arg
    E.RecordP row -> RecordP $ fmap simplifyPattern row
    E.LiteralP lit -> LiteralP $ unLoc lit

-- anything fancy gets converted into an OpaqueTy
-- however, most constructs cannot appear in a value of type Type at all,
-- so it might make more sense to just throw an error if it happens
simplifyPatternType :: forall es. InfEffs es => TypeDT_ -> Eff es ExType
simplifyPatternType ty = ($ Map.empty) <$> simplifyPatternTypeWith ty

simplifyPatternTypeWith :: forall es. InfEffs es => TypeDT_ -> Eff es (IdMap Name ExType -> ExType)
simplifyPatternTypeWith = \case
    V.Var name -> pure $ Map.lookupDefault OpaqueTy name
    V.TyCon name -> pure $ const $ TyCon (unLoc name) []
    V.VariantT row -> do
        row' <- compress Variant Inv row
        fnRow <- traverse simplifyPatternTypeWith row'
        pure \args -> ExVariant (fmap ($ args) fnRow)
    V.RecordT row -> do
        row' <- compress Record Inv row
        fnRow <- traverse simplifyPatternTypeWith row'
        pure \args -> ExRecord (fmap ($ args) fnRow.row)
    V.App lhs rhs -> do
        lhsFn <- simplifyPatternTypeWith lhs
        rhsFn <- simplifyPatternTypeWith rhs
        pure \env -> case lhsFn env of
            TyCon name args -> TyCon name (args <> [rhsFn env])
            _ -> OpaqueTy
    V.UniVar uni ->
        lookupUniVar uni >>= \case
            Left{} -> pure $ const OpaqueTy
            Right body -> simplifyPatternTypeWith $ unLoc $ unMono body
    _ -> pure $ const OpaqueTy

data Pattern
    = Con Name_ [Pattern]
    | VariantP SimpleName_ Pattern
    | RecordP (Row Pattern)
    | LiteralP Literal_
    | Wildcard

instance Show Pattern where
    show = show . pretty
instance Pretty Pattern where
    pretty = \case
        Con name [] -> pretty name
        Con name args -> parens $ hsep (pretty name : map pretty args)
        VariantP name arg -> parens $ pretty name <+> pretty arg
        LiteralP lit -> pretty lit
        Wildcard -> "_"
        RecordP row -> prettyRecord "=" pretty pretty (NoExtRow row)

-- in normal branches and variant branches, the map contains
-- all unmatched children, and NotVisited is used when all of the children branches are full
--
-- Variant branches also contain a catchall case for a row extension
--
-- TextBranch and IntBranch cannot ever be matched fully without a catch-all case,
-- so they contain a fallback case and the map of all children *that have been matched on*
-- I don't really *need* the maps until I implement the check for redundant patterns,
-- but I'm going to do it at some point
data CaseTree a
    = Branch (IdMap Name_ (Nested a))
    | VariantBranch (HashMap SimpleName_ (CaseTree a)) (Maybe a)
    | TextBranch (HashMap Text a) a
    | CharBranch (HashMap Text a) a
    | IntBranch (IntMap a) a
    | RecordBranch (RecordBranch a)
    | Opaque a -- can be matched only by a wildcard
    | NotVisited (forall b. b -> CaseTree b) a

data Nested a
    = NotNested a
    | Nested (CaseTree (Nested a))

-- with normal products, we know how much to descend based on the type
-- when it comes to records, though, a pattern may match on a subset of the fields
data RecordBranch a
    = None a
    | Field SimpleName (CaseTree (RecordBranch a))

mapMaybeTree :: (a -> Maybe b) -> CaseTree a -> Maybe (CaseTree b)
mapMaybeTree f = \case
    Branch tree -> Branch <$> Map.mapMaybe (mapMaybeProd f) tree
    VariantBranch tree fallback -> Just $ VariantBranch (HashMap.mapMaybe (mapMaybeTree f) tree) (f =<< fallback)
    TextBranch tree fallback -> TextBranch (HashMap.mapMaybe f tree) <$> f fallback
    CharBranch tree fallback -> CharBranch (HashMap.mapMaybe f tree) <$> f fallback
    IntBranch tree fallback -> IntBranch (IntMap.mapMaybe f tree) <$> f fallback
    RecordBranch branch -> RecordBranch <$> mapMaybeRecordBranch f branch
    Opaque x -> Opaque <$> f x
    NotVisited build x -> NotVisited build <$> f x

mapMaybeProd :: (a -> Maybe b) -> Nested a -> Maybe (Nested b)
mapMaybeProd f = \case
    NotNested x -> NotNested <$> f x
    Nested nested -> Nested <$> mapMaybeTree (mapMaybeProd f) nested

mapMaybeRecordBranch :: (a -> Maybe b) -> RecordBranch a -> Maybe (RecordBranch b)
mapMaybeRecordBranch f = \case
    None x -> None <$> f x
    Field name nested -> Field name <$> mapMaybeTree (mapMaybeRecordBranch f) nested

prune :: Pattern -> (a -> Maybe a) -> CaseTree a -> Maybe (CaseTree a)
prune = \cases
    Wildcard k tree -> mapMaybeTree k tree
    pat k (NotVisited f x) -> prune pat k $ f x
    (Con name args) k (Branch tree) -> Branch <$> guarded (not . Map.null) (Map.update (pruneNested args k) name tree)
    -- when we have a variant type with no fallback, we can eliminate the whole branch if the map is empty
    (VariantP name arg) k (VariantBranch tree Nothing) -> VariantBranch <$> guarded (not . HashMap.null) (HashMap.update (prune arg k) name tree) <*> pure Nothing
    -- when we *do* have a fallback though, only a Wilcard can eliminate this branch
    (VariantP name arg) k (VariantBranch tree (Just fallback)) -> Just $ VariantBranch (HashMap.update (prune arg k) name tree) (Just fallback)
    (LiteralP (IntLiteral n)) k (IntBranch tree fallback) -> Just $ IntBranch (IntMap.update k n tree) fallback
    (LiteralP (TextLiteral t)) k (TextBranch tree fallback) -> Just $ TextBranch (HashMap.alter (k . fromMaybe fallback) t tree) fallback
    (LiteralP (CharLiteral c)) k (CharBranch tree fallback) -> Just $ CharBranch (HashMap.alter (k . fromMaybe fallback) c tree) fallback
    (RecordP row) k (RecordBranch branch) -> RecordBranch <$> pruneRecord row k branch
    _ _ (Opaque x) -> Just $ Opaque x
    _ _ _ -> error "pattern type mismatch (shouldn't happen for well-typed code)"

pruneNested :: [Pattern] -> (a -> Maybe a) -> Nested a -> Maybe (Nested a)
pruneNested [] k (NotNested x) = NotNested <$> k x
pruneNested (pat : pats) k (Nested nested) = Nested <$> prune pat (pruneNested pats k) nested
pruneNested _ _ _ = error "pruneNested: length mismatch"

pruneRecord :: Row Pattern -> (a -> Maybe a) -> RecordBranch a -> Maybe (RecordBranch a)
pruneRecord row k = \case
    None x -> None <$> k x
    Field name nested ->
        Field name <$> case Row.takeField name row of
            Just (pat, row') -> prune pat (pruneRecord row' k) nested
            Nothing -> mapMaybeTree (pruneRecord row k) nested

missingPatterns :: ([Pattern] -> a -> [r]) -> Maybe (CaseTree a) -> [r]
missingPatterns _ Nothing = []
missingPatterns k (Just tree) = case tree of
    NotVisited _ x -> k [Wildcard] x
    Opaque x -> k [Wildcard] x
    Branch branches -> do
        (con, argTree) <- Map.toList branches
        missingPatternsNested (k . fmap (Con con)) argTree
    VariantBranch branches fallback ->
        ( do
            (con, argBranch) <- HashMap.toList branches
            missingPatterns (k . fmap (VariantP con)) (Just argBranch)
        )
            <> concatMap (k [Wildcard]) fallback
    IntBranch branches fallback -> IntMap.foldMapWithKey (\n -> k [LiteralP (IntLiteral n)]) branches <> k [Wildcard] fallback
    TextBranch branches fallback -> HashMap.foldMapWithKey (\t -> k [LiteralP (TextLiteral t)]) branches <> k [Wildcard] fallback
    CharBranch branches fallback -> HashMap.foldMapWithKey (\c -> k [LiteralP (CharLiteral c)]) branches <> k [Wildcard] fallback
    RecordBranch branches -> missingPatternsRecord (k . fmap RecordP) branches

missingPatternsNested :: ([[Pattern]] -> a -> [r]) -> Nested a -> [r]
missingPatternsNested k (NotNested x) = k [[]] x
missingPatternsNested k (Nested tree) =
    missingPatterns (\lhses -> missingPatternsNested (k . liftA2 (:) lhses)) (Just tree)

missingPatternsRecord :: ([Row Pattern] -> a -> [r]) -> RecordBranch a -> [r]
missingPatternsRecord k = \case
    None x -> k [Row.empty] x
    Field name nested -> missingPatterns (\fieldVals -> missingPatternsRecord (k . addField name fieldVals)) (Just nested)
  where
    addField :: OpenName -> [Pattern] -> [Row Pattern] -> [Row Pattern]
    addField name vals rows = do
        val <- vals
        row <- rows
        pure $ one (name, val) <> row

buildProdTree :: ConstructorTable -> [ExType] -> Nested ()
buildProdTree conMap types = case buildProdTree' conMap types () of
    Nested (NotVisited f x) -> Nested $ f x
    other -> other

buildCaseTree :: ConstructorTable -> ExType -> a -> CaseTree a
buildCaseTree conMap = \cases
    OpaqueTy -> Opaque
    (TyCon IntName _) -> IntBranch IntMap.empty
    (TyCon NatName _) -> IntBranch IntMap.empty
    (TyCon CharName _) -> CharBranch HashMap.empty
    (TyCon TextName _) -> TextBranch HashMap.empty
    -- todo: NotVisited nodes should never be empty, but these two cases may produce an empty branch
    -- perhaps it would be cleaner to change NotVisited to `NotVisited (forall b. b -> Maybe (CaseTree b)) a`
    (TyCon name args) -> NotVisited \k -> maybe (Opaque k) (Branch . fmap (flip (buildProdTree' conMap) k . ($ args))) (Map.lookup name conMap.table)
    (ExVariant row) -> NotVisited \k ->
        VariantBranch
            (fmap (\t -> buildCaseTree conMap t k) $ HashMap.fromList $ map (first unLoc) $ Row.sortedRow row.row)
            (k <$ Row.extension row)
    (ExRecord row) -> NotVisited $ RecordBranch . buildRecordTree conMap (Row.sortedRow row)

buildProdTree' :: ConstructorTable -> [ExType] -> b -> Nested b
buildProdTree' _ [] = NotNested
buildProdTree' conMap (ty : types) = Nested . NotVisited (buildCaseTree conMap ty) . buildProdTree' conMap types

buildRecordTree :: ConstructorTable -> [(OpenName, ExType)] -> a -> RecordBranch a
buildRecordTree _ [] = None
buildRecordTree conMap ((name, ty) : rest) = Field name . NotVisited (buildCaseTree conMap ty) . buildRecordTree conMap rest
