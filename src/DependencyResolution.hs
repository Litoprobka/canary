{-# LANGUAGE RecordWildCards #-}
module DependencyResolution where

import Common
import Data.HashMap.Strict qualified as HashMap
import Diagnostic (Diagnose, fatal, nonFatal)
import Effectful.State.Static.Local
import Effectful.Writer.Static.Local (Writer, runWriter)
import Error.Diagnose (Marker (..), Report (..))
import LangPrelude
import NameGen (runNameGen, freshId)
import Poset (Poset)
import Poset qualified
import Prettyprinter (comma, hsep, punctuate)
import Syntax
import Syntax.Declaration qualified as D
import LensyUniplate (uniplateCast, cast)

-- once we've done name resolution, all sorts of useful information may be collected into tables
-- this pass gets rid of the old [Declaration] shape of the AST and transforms it into something more structured

newtype DeclId = DeclId Id

data Output = Output
    { fixityMap :: FixityMap
    -- ^ operator fixities extracted from Infix declarations
    , operatorPriorities :: Poset Op
    -- ^ operator priorities extracted from Infix declarations and converted to a Poset
    , dependencyOrder :: [[DeclId]]
    -- ^ the order in which declarations may be processed
    , declarations :: HashMap DeclId Decl -- since a declaration may yield multiple names, direct name-to-declaration mapping is a no go
    -- given the many-to-one nature of declarations, we need some way to relate them to names
    , nameOrigins :: NameOrigins
    , signatures :: Signatures
    }

type Decl = Declaration 'DependencyRes
type Op = Maybe Name
type FixityMap = HashMap Op Fixity
type DeclSet = Poset Decl
type NameOrigins = HashMap Name DeclId
type Declarations = HashMap DeclId Decl
type Signatures = HashMap Name Type

danglingSigError :: Diagnose :> es => Type -> Eff es ()
danglingSigError ty = nonFatal $
    Err
    Nothing
    "Signature lacks an accompanying binding"
    (mkNotes [(getLoc ty, This "this")])
    []

resolveDependencies :: [Declaration 'NameRes] -> Eff es Output
resolveDependencies decls = do
    --(declDeps, (operatorPriorities, (fixityMap, (nameOrigins, (declarations, signatures))))) 
    (((((signatures, declarations), nameOrigins), fixityMap), operatorPriorities), declDeps)
      <- runNameGen
        . runState @DeclSet Poset.empty
        . runState @(Poset Op) Poset.empty
        . runState @FixityMap HashMap.empty
        . runState @NameOrigins HashMap.empty
        . runState @Declarations HashMap.empty
        . execState @Signatures HashMap.empty
        $ traverse_ go decls
    let danglingSigs = HashMap.difference signatures $ HashMap.compose declarations nameOrigins
    for_ danglingSigs danglingSigError
    pure Output{dependencyOrder = todo, ..}
  where
    go :: Declaration 'NameRes -> Eff es ()
    go = \case
        D.Fixity loc fixity op rels -> do
            modify @FixityMap $ HashMap.insert (Just op) fixity
            modifyM @(Poset Op) $ updatePrecedence loc op rels
        D.Value loc binding locals -> do
            declId <- addDecl (D.Value loc binding locals)
            linkNamesToDecl declId $ collectNames binding
        D.Type loc name vars constrs -> do
            declId <- addDecl (D.Type loc name vars constrs)
            linkNamesToDecl declId $ name : map (.name) constrs
        D.Signature _ name ty -> do
            modify @Signatures $ HashMap.insert name $ cast uniplateCast ty

    addDecl :: Declaration 'DependencyRes -> Eff es DeclId
    addDecl decl = do
        declId <- DeclId <$> freshId
        modify @Declarations $ HashMap.insert declId decl
        pure declId
    linkNamesToDecl :: DeclId -> [Name] -> Eff es ()
    linkNamesToDecl declId names =
        modify @NameOrigins \origs -> foldl' (\acc n -> HashMap.insert n declId acc) origs names

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
    mbPretty Nothing = "function application"
    mbPretty (Just op) = pretty op

selfRelationError :: Diagnose :> es => Name -> Eff es ()
selfRelationError op =
    fatal . one $
        Err
            Nothing
            ("self-reference in fixity declaration" <+> pretty op)
            (mkNotes [(getLoc op, This "is referenced in its own fixity declaration")])
            []

reportCycleWarnings :: (State (Poset Op) :> es, Diagnose :> es) => Loc -> Eff (Writer (Seq (Poset.Cycle Op)) : es) a -> Eff es a
reportCycleWarnings loc action = do
    (x, warnings) <- runWriter action
    poset <- get @(Poset Op)
    for_ warnings \(Poset.Cycle lhsClass rhsClass) -> do
        cycleWarning loc (Poset.items lhsClass poset) (Poset.items rhsClass poset)
    pure x

updatePrecedence :: Diagnose :> es => Loc -> Name -> PriorityRelation 'NameRes -> Poset Op -> Eff es (Poset Op)
updatePrecedence loc op rels poset = execState poset $ Poset.reportError $ reportCycleWarnings loc do
    traverse_ (addRelation GT) rels.above
    traverse_ (addRelation LT) below
    traverse_ (addRelation EQ . Just) rels.equal
  where
    -- all operators implicitly have a lower precedence than function application, unless stated otherwise
    below
        | Nothing `notElem` rels.above = Nothing : map Just rels.below
        | otherwise = map Just rels.below

    addRelation _ op2
        | Just op == op2 = selfRelationError op
    addRelation rel op2 = do
        lhsClass <- state $ Poset.eqClass (Just op)
        rhsClass <- state $ Poset.eqClass op2
        modifyM @(Poset Op) $ Poset.addRelationLenient lhsClass rhsClass rel

