module TypeChecker.Exhaustiveness (checkExhaustiveness, checkExhaustiveness', ConstructorTable (..), simplifyPatternType, simplifyPatternTypeWith) where

import Common hiding (Wildcard)
import Diagnostic
import Effectful.State.Static.Local (get)
import Error.Diagnose (Note (..), Report (..))
import Error.Diagnose qualified as M
import IdMap qualified as Map
import LangPrelude
import Prettyprinter (hsep, parens, vsep)
import Syntax.Elaborated hiding (Name)
import Syntax.Value qualified as V
import TypeChecker.Backend

checkExhaustiveness :: InfEffs es => Loc -> TypeDT_ -> [EPattern] -> Eff es ()
checkExhaustiveness loc ty branches = do
    conMap <- get @ConstructorTable
    branches' <- traverse simplifyPattern branches
    patternType <- simplifyPatternType ty
    let tree = buildCaseTree conMap patternType
        unmatched = checkCaseTree tree branches'
    unless (null unmatched) do
        nonFatal $
            Err
                Nothing
                "non-exhaustive patterns"
                (mkNotes [(loc, M.This "when checking this expression")])
                [Note $ vsep ("patterns not matched:" : map pretty unmatched)]

checkExhaustiveness' :: InfEffs es => Loc -> [TypeDT_] -> [[EPattern]] -> Eff es ()
checkExhaustiveness' loc ty branches = do
    conMap <- get @ConstructorTable
    branches' <- (traverse . traverse) simplifyPattern branches
    patternTypes <- traverse simplifyPatternType ty
    let nested = buildProdTree conMap patternTypes
        unmatched = checkMatch nested branches'
    unless (null unmatched) do
        nonFatal $
            Err
                Nothing
                "non-exhaustive patterns"
                (mkNotes [(loc, M.This "when checking this expression")])
                [Note $ vsep ("patterns not matched:" : map (hsep . map pretty) unmatched)]

checkCaseTree :: Maybe (CaseTree ()) -> [Pattern] -> [Pattern]
checkCaseTree initTree = missingPatterns const . foldr (\pat tree -> prune pat (const Nothing) =<< tree) initTree

checkMatch :: Nested () -> [[Pattern]] -> [[Pattern]]
checkMatch initTree = maybe [] (missingPatternsNested const) . foldr (\pats tree -> pruneNested pats (const Nothing) =<< tree) (Just initTree)

simplifyPattern :: Diagnose :> es => EPattern -> Eff es Pattern
simplifyPattern (p :@ loc ::: _) = case p of
    VarP{} -> pure Wildcard
    WildcardP{} -> pure Wildcard
    ConstructorP name pats -> Con (unLoc name) <$> traverse simplifyPattern pats
    ListP pats -> foldr (\x xs -> Con ConsName [x, xs]) (Con NilName []) <$> traverse simplifyPattern pats
    VariantP{} -> internalError loc "variants are not supported by exhaustiveness checker yet"
    RecordP{} -> internalError loc "record patterns are not supported by exhaustiveness checker yet"
    LiteralP{} -> internalError loc "literal patterns are not supported by exhaustiveness checker yet"

-- anything fancy gets converted into an OpaqueTy
-- however, most constructs cannot appear in a value of type Type at all,
-- so it might make more sense to just throw an error if it happens
simplifyPatternType :: forall es. InfEffs es => TypeDT_ -> Eff es ExType
simplifyPatternType ty = ($ Map.empty) <$> simplifyPatternTypeWith ty

simplifyPatternTypeWith :: forall es. InfEffs es => TypeDT_ -> Eff es (IdMap Name ExType -> ExType)
simplifyPatternTypeWith = \case
    V.Var name -> pure $ Map.lookupDefault OpaqueTy name
    V.TyCon name -> pure $ const $ TyCon (unLoc name) []
    V.App lhs rhs -> do
        lhsFn <- simplifyPatternTypeWith lhs
        rhsFn <- simplifyPatternTypeWith rhs
        pure \env -> case lhsFn env of
            TyCon name args -> TyCon name (args <> [rhsFn env])
            OpaqueTy -> OpaqueTy
    V.UniVar uni ->
        lookupUniVar uni >>= \case
            Left{} -> pure $ const OpaqueTy
            Right body -> simplifyPatternTypeWith $ unLoc $ unMono body
    _ -> pure $ const OpaqueTy

data CaseTree a
    = Branch (IdMap Name_ (Nested a))
    | Opaque a -- can be matched only by a wildcard
    | NotVisited (forall b. b -> CaseTree b) a

-- todo: variants, records and primitives

data Nested a
    = NotNested a
    | Nested (CaseTree (Nested a))

mapMaybeTree :: (a -> Maybe b) -> CaseTree a -> Maybe (CaseTree b)
mapMaybeTree f = \case
    Branch tree -> Branch <$> Map.mapMaybe (mapMaybeProd f) tree
    Opaque x -> Opaque <$> f x
    NotVisited build x -> NotVisited build <$> f x

mapMaybeProd :: (a -> Maybe b) -> Nested a -> Maybe (Nested b)
mapMaybeProd f = \case
    NotNested x -> NotNested <$> f x
    Nested nested -> Nested <$> mapMaybeTree (mapMaybeProd f) nested

data Pattern
    = Con Name_ [Pattern]
    | Wildcard
    deriving (Show)
instance Pretty Pattern where
    pretty (Con name []) = pretty name
    pretty (Con name args) = parens $ hsep (pretty name : map pretty args)
    pretty Wildcard = "_"

prune :: Pattern -> (a -> Maybe a) -> CaseTree a -> Maybe (CaseTree a)
prune = \cases
    Wildcard k tree -> mapMaybeTree k tree
    pat k (NotVisited f x) -> prune pat k $ f x
    (Con name args) k (Branch tree) -> Branch <$> guarded (not . Map.null) (Map.update (pruneNested args k) name tree)
    Con{} _ (Opaque x) -> Just $ Opaque x

pruneNested :: [Pattern] -> (a -> Maybe a) -> Nested a -> Maybe (Nested a)
pruneNested [] k (NotNested x) = NotNested <$> k x
pruneNested (pat : pats) k (Nested nested) = Nested <$> prune pat (pruneNested pats k) nested
pruneNested _ _ _ = error "pruneNested: length mismatch"

missingPatterns :: ([Pattern] -> a -> [r]) -> Maybe (CaseTree a) -> [r]
missingPatterns _ Nothing = []
missingPatterns k (Just tree) = case tree of
    NotVisited _ x -> k [Wildcard] x
    Opaque x -> k [Wildcard] x
    Branch branches -> do
        (con, argTree) <- Map.toList branches
        missingPatternsNested (k . fmap (Con con)) argTree

missingPatternsNested :: ([[Pattern]] -> a -> [r]) -> Nested a -> [r]
missingPatternsNested k (NotNested x) = k [[]] x
missingPatternsNested k (Nested tree) =
    missingPatterns (\lhses -> missingPatternsNested (k . liftA2 (:) lhses)) (Just tree)

buildCaseTree :: ConstructorTable -> ExType -> Maybe (CaseTree ())
buildCaseTree conMap ty = Just case buildCaseTree' conMap ty () of
    NotVisited f x -> f x
    other -> other

buildProdTree :: ConstructorTable -> [ExType] -> Nested ()
buildProdTree conMap types = case buildProdTree' conMap types () of
    Nested (NotVisited f x) -> Nested $ f x
    other -> other

buildCaseTree' :: ConstructorTable -> ExType -> a -> CaseTree a
buildCaseTree' _ OpaqueTy = Opaque
buildCaseTree' conMap (TyCon name args) = NotVisited \k -> maybe (Opaque k) (Branch . fmap (flip (buildProdTree' conMap) k . ($ args))) constrs
  where
    constrs = Map.lookup name conMap.table

buildProdTree' :: ConstructorTable -> [ExType] -> b -> Nested b
buildProdTree' _ [] = NotNested
buildProdTree' conMap (t : types) = Nested . NotVisited (buildCaseTree' conMap t) . buildProdTree' conMap types
