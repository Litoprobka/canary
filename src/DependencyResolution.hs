{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE RecordWildCards #-}

module DependencyResolution where

import Common
import Data.IdMap qualified as Map
import Data.Poset (Poset)
import Data.Poset qualified as Poset
import Diagnostic (Diagnose, fatal, internalError', nonFatal)
import Effectful.State.Static.Local
import Effectful.Writer.Static.Local (Writer, runWriter)
import Error.Diagnose (Marker (..), Report (..))
import LangPrelude
import Prettyprinter (comma, hsep, punctuate)
import Syntax
import Syntax.AstTraversal
import Syntax.Declaration qualified as D

-- once we've done name resolution, all sorts of useful information may be collected into tables
-- this pass gets rid of the old [Declaration] shape of the AST and transforms it into something more structured

data Output = Output
    { fixityMap :: FixityMap
    -- ^ operator fixities extracted from Infix declarations
    , operatorPriorities :: Poset Op
    -- ^ operator priorities extracted from Infix declarations and converted to a Poset
    , orderedDeclarations :: [[Decl]]
    -- ^ mutually recursive groups of declarations in processing order
    , signatures :: Signatures
    }

type Decl = Declaration 'DependencyRes
type FixityMap = IdMap Op Fixity
type Signatures = HashMap Name (Type 'DependencyRes)

data Op = Op Name | AppOp
    deriving (Eq)
    deriving (Pretty) via (UnAnnotate Op)
instance PrettyAnsi Op where
    prettyAnsi = \case
        Op name -> prettyAnsi name
        AppOp -> "function application"
instance Map.HasId Op where
    toId = \case
        AppOp -> -1
        Op name -> Map.toId name

{-
nameDependencies :: Diagnose :> es => [Declaration 'NameRes] -> Eff es (Poset Name)
nameDependencies = execState Poset.empty . traverse_ resolve
  where
    resolve :: Diagnose :> es => Declaration 'NameRes -> Eff (State (Poset Name) : es) ()
    resolve = \case
        D.Value _ binding _ -> case binding of
            ValueBinding pat body -> do
                for_ (P.collectNames pat) \declName ->
                    for_ (P.collectReferencedNames pat) \refName ->
                        modifyM $ Poset.reportError . Poset.addGteRel refName declName
            FunctionBinding name args body -> do
                for_ (foldMap P.collectReferencedNames args) \refName ->
                    modifyM $ Poset.reportError . Poset.addGteRel refName name
        D.Type _ name vars constrs -> _
        D.GADT{} -> _todo
        D.Signature _ name ty -> _
        _ -> pass

resolveDependencies :: forall es. Diagnose :> es => [Declaration 'NameRes] -> Eff es Output
resolveDependencies decls = do
    (((((signatures, declarations), nameOrigins), fixityMap), operatorPriorities), declDeps) <-
        runNameGen
            . runState @(Poset Name) Poset.empty
            . runState @(Poset Op) Poset.empty
            . runState @FixityMap HashMap.empty
            . execState @Signatures HashMap.empty
            $ traverse_ go decls
    let danglingSigs = HashMap.difference signatures $ HashMap.compose declarations nameOrigins
    for_ danglingSigs danglingSigError

    let orderedDeclarations = (map . mapMaybe) (`HashMap.lookup` declarations) $ Poset.ordered declDeps

    pure Output{..}
  where
    -- go :: Declaration 'NameRes -> Eff es ()
    go = \case
        D.Fixity loc fixity op rels -> do
            modify @FixityMap $ HashMap.insert (Just op) fixity
            modifyM @(Poset Op) $ updatePrecedence loc op rels
        D.Value loc binding locals -> do
            -- I'm not sure how to handle locals here, since they may contain mutual recursion
            -- and all of the same complications
            -- seems like we have to run dependency resolution on these bindings locally
            let (binding', dependencies) = collectBindingDependencies binding
            declId <- addDecl (D.Value loc (cast binding) _processedLocals)
            -- traverse the binding body and add a dependency between declarations
            linkNamesToDecl declId $ collectNamesInBinding binding
        D.Type loc name vars constrs -> do
            declId <- addDecl (D.Type loc name (map cast vars) $ map castCon constrs)
            linkNamesToDecl declId $ name : map (.name) constrs
        -- traverse all constructor arguments and add dependencies
        -- these dependencies are only needed for kind checking
        D.GADT{} -> _todo
        D.Signature _ name ty -> do
            modify @Signatures $ HashMap.insert name $ cast ty

    castCon :: Constructor 'NameRes -> Constructor 'DependencyRes
    castCon D.Constructor{loc, name, args} =
        D.Constructor loc (coerce name) $ map cast args

collectBindingDependencies :: Binding 'NameRes -> (Binding 'DependencyRes, HashSet Name)
collectBindingDependencies = runPureEff . runState @(HashSet Name) HashSet.empty . go
  where
    go = todo
-}

data SimpleOutput = SimpleOutput
    { fixityMap :: FixityMap
    -- ^ operator fixities extracted from Infix declarations
    , operatorPriorities :: Poset Op
    , declarations :: [Declaration 'DependencyRes]
    }

resolveDependenciesSimplified
    :: forall es
     . Diagnose :> es
    => [Declaration 'NameRes]
    -> Eff es SimpleOutput
resolveDependenciesSimplified = resolveDependenciesSimplified' initFixity initPoset
  where
    initFixity = Map.one AppOp InfixL
    (_, initPoset) = Poset.eqClass AppOp Poset.empty

resolveDependenciesSimplified'
    :: forall es. Diagnose :> es => FixityMap -> Poset Op -> [Declaration 'NameRes] -> Eff es SimpleOutput
resolveDependenciesSimplified' initFixity initPoset = fmap packOutput . runState @FixityMap initFixity . runState @(Poset Op) initPoset . mapMaybeM go
  where
    packOutput ((declarations, operatorPriorities), fixityMap) = SimpleOutput{..}
    go :: Declaration 'NameRes -> Eff (State (Poset Op) : State FixityMap : es) (Maybe (Declaration 'DependencyRes))
    go (Located loc decl) = fmap (fmap $ Located loc) case decl of
        D.Fixity fixity op rels -> do
            fixity' <-
                if isInfixConstructor op && fixity == InfixChain
                    then Infix <$ colonOpChainfixWarning op
                    else pure fixity
            modify @FixityMap $ Map.insert (Op op) fixity'
            modifyM @(Poset Op) $ updatePrecedence loc op rels
            pure Nothing
        other -> Just . unLoc <$> partialTravDeclaration cast (other :@ loc)

cast :: Diagnose :> es => AstTraversal 'NameRes 'DependencyRes (Eff es)
cast = tie $ mkTrav defTravTerm defTravPattern (\_ _ -> internalError' "depResTrav: shouldn't reach declaration") (const pure)

reportCycleWarnings :: (State (Poset Op) :> es, Diagnose :> es) => Loc -> Eff (Writer (Seq (Poset.Cycle Op)) : es) a -> Eff es a
reportCycleWarnings loc action = do
    (x, warnings) <- runWriter action
    poset <- get @(Poset Op)
    for_ warnings \(Poset.Cycle lhsClass rhsClass) -> do
        cycleWarning loc (Poset.items lhsClass poset) (Poset.items rhsClass poset)
    pure x

updatePrecedence :: Diagnose :> es => Loc -> Name -> PriorityRelation 'NameRes -> Poset Op -> Eff es (Poset Op)
updatePrecedence loc op rels poset = execState poset $ Poset.reportError $ reportCycleWarnings loc do
    traverse_ (addRelation GT . maybe AppOp Op) rels.above
    traverse_ (addRelation LT) below
    traverse_ (addRelation EQ . Op) rels.equal
  where
    -- all operators implicitly have a lower precedence than function application, unless stated otherwise
    below
        | Nothing `notElem` rels.above = AppOp : map Op rels.below
        | otherwise = map Op rels.below

    addRelation _ op2
        | Op op == op2 = selfRelationError op
    addRelation rel op2 = do
        modifyM @(Poset Op) $ Poset.addRelationLenient (Op op) op2 rel

-- errors

danglingSigError :: Diagnose :> es => Type 'DependencyRes -> Eff es ()
danglingSigError ty =
    nonFatal $
        Err
            Nothing
            "Signature lacks an accompanying binding"
            (mkNotes [(getLoc ty, This "this")])
            []

colonOpChainfixWarning :: Diagnose :> es => Name -> Eff es ()
colonOpChainfixWarning op =
    nonFatal
        ( Warn
            Nothing
            "infix constructors cannot be chainfix, defaulting to non-associative"
            (mkNotes [(getLoc op, This "in this fixity declaration")])
            []
        )

cycleWarning :: Diagnose :> es => Loc -> [Op] -> [Op] -> Eff es ()
cycleWarning loc ops ops2 =
    nonFatal $
        Warn
            Nothing
            ( "priority cycle between" <+> hsep (punctuate comma $ map mbPretty ops) <+> "and" <+> hsep (punctuate comma $ map mbPretty ops2)
            )
            (mkNotes [(loc, This "occured at this declaration")])
            []
  where
    mbPretty AppOp = "function application"
    mbPretty (Op op) = prettyDef op

selfRelationError :: Diagnose :> es => Name -> Eff es ()
selfRelationError op =
    fatal . one $
        Err
            Nothing
            ("self-reference in fixity declaration" <+> prettyDef op)
            (mkNotes [(getLoc op, This "is referenced in its own fixity declaration")])
            []
