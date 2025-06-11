{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoFieldSelectors #-}

module Syntax.AstTraversal where

import Common
import Data.Type.Ord (type (<))
import LangPrelude
import Syntax
import Syntax.Declaration qualified as D
import Syntax.Term
import Syntax.Term qualified as T

data AstTraversal (p :: Pass) (q :: Pass) m = AstTraversal
    { term :: Term p -> m (Term q)
    , pattern_ :: Pattern p -> m (Pattern q)
    , declaration :: Declaration p -> m (Declaration q)
    , name :: NameAt p -> m (NameAt q)
    , binding :: Binding p -> m (Binding q)
    , binder :: VarBinder p -> m (VarBinder q)
    , statement :: DoStatement p -> m (DoStatement q)
    -- do we need a separate function for PriorityRelation? probably not
    }

tie :: UntiedTraversal p q m -> AstTraversal p q m
tie UntiedTraversal{..} = self
  where
    self =
        AstTraversal
            { term = term self
            , pattern_ = pattern_ self
            , declaration = declaration self
            , name = name self
            , binding = binding self
            , binder = binder self
            , statement = statement self
            }

data UntiedTraversal (p :: Pass) (q :: Pass) m = UntiedTraversal
    { term :: AstTraversal p q m -> Term p -> m (Term q)
    , pattern_ :: AstTraversal p q m -> Pattern p -> m (Pattern q)
    , declaration :: AstTraversal p q m -> Declaration p -> m (Declaration q)
    , name :: AstTraversal p q m -> NameAt p -> m (NameAt q)
    , binding :: AstTraversal p q m -> Binding p -> m (Binding q)
    , binder :: AstTraversal p q m -> VarBinder p -> m (VarBinder q)
    , statement :: AstTraversal p q m -> DoStatement p -> m (DoStatement q)
    -- do we need a separate function for PriorityRelation? probably not
    }

defTravTerm
    :: forall p q m. (FixityAgrees p q, NameAt p ~ NameAt q, Applicative m) => AstTraversal p q m -> Term p -> m (Term q)
defTravTerm trav (term' :@ loc) =
    Located loc <$> case term' of
        ImplicitVar name -> ImplicitVar <$> trav.name name
        Parens term -> Parens <$> trav.term term
        InfixE pairs term -> castInfix @p <$> traverse (bitraverse trav.term (traverse trav.name)) pairs <*> trav.term term
        other -> unLoc <$> partialTravTerm trav (other :@ loc)

-- | caution: this traversal doesn't handle ImplicitName, Parens and InfixE
partialTravTerm :: Applicative m => AstTraversal p q m -> Term p -> m (Term q)
partialTravTerm trav (term' :@ loc) =
    Located loc <$> case term' of
        T.Name name -> T.Name <$> trav.name name
        Literal lit -> pure $ Literal lit
        Annotation term ty -> Annotation <$> trav.term term <*> trav.term ty
        App lhs rhs -> App <$> trav.term lhs <*> trav.term rhs
        Lambda pat body -> Lambda <$> trav.pattern_ pat <*> trav.term body
        WildcardLambda names body -> WildcardLambda <$> traverse trav.name names <*> trav.term body
        Let binding body -> Let <$> trav.binding binding <*> trav.term body
        LetRec bindings body -> LetRec <$> traverse trav.binding bindings <*> trav.term body
        TypeApp expr ty -> TypeApp <$> trav.term expr <*> trav.term ty
        Case term matches -> Case <$> trav.term term <*> traverse (bitraverse trav.pattern_ trav.term) matches
        Match matches -> Match <$> traverse (bitraverse (traverse trav.pattern_) trav.term) matches
        If cond true false -> If <$> trav.term cond <*> trav.term true <*> trav.term false
        T.Variant oname -> pure $ T.Variant oname
        Record row -> Record <$> traverse trav.term row
        Sigma x y -> Sigma <$> trav.term x <*> trav.term y
        List terms -> List <$> traverse trav.term terms
        Do statements term -> Do <$> traverse trav.statement statements <*> trav.term term
        Function from to -> Function <$> trav.term from <*> trav.term to
        Q q v e binder body -> Q q v e <$> trav.binder binder <*> trav.term body
        VariantT row -> VariantT <$> traverse trav.term row
        RecordT row -> RecordT <$> traverse trav.term row
        ImplicitVar{} -> error "partialTravTerm: encountered ImplicitVar"
        Parens{} -> error "partialTravTerm: encountered Parens"
        InfixE{} -> error "partialTravTerm: encountered InfixE"

defTravPattern :: forall p q m. (FixityAgrees p q, Applicative m) => AstTraversal p q m -> Pattern p -> m (Pattern q)
defTravPattern trav (pat' :@ loc) =
    Located loc <$> case pat' of
        InfixP pairs pat -> castInfixP @p <$> traverse (bitraverse trav.pattern_ trav.name) pairs <*> trav.pattern_ pat
        other -> unLoc <$> partialTravPattern trav (other :@ loc)

-- | same as 'partialTravTerm'. Doesn't handle InfixP
partialTravPattern :: Applicative m => AstTraversal p q m -> Pattern p -> m (Pattern q)
partialTravPattern trav (pat' :@ loc) =
    Located loc <$> case pat' of
        VarP name -> VarP <$> trav.name name
        WildcardP text -> pure $ WildcardP text
        AnnotationP pat ty -> AnnotationP <$> trav.pattern_ pat <*> trav.term ty
        ConstructorP name pats -> ConstructorP <$> trav.name name <*> traverse trav.pattern_ pats
        VariantP oname pat -> VariantP oname <$> trav.pattern_ pat
        RecordP row -> RecordP <$> traverse trav.pattern_ row
        ListP pats -> ListP <$> traverse trav.pattern_ pats
        LiteralP lit -> pure $ LiteralP lit
        InfixP{} -> error "partialTravPattern: encountered InfixP"

defTravDeclaration
    :: forall p q m. (DepResAgrees p q, Applicative m) => AstTraversal p q m -> Declaration p -> m (Declaration q)
defTravDeclaration trav = traverse \case
    D.Value binding locals -> D.Value <$> trav.binding binding <*> traverse trav.declaration locals -- does a reversed order make more sense?
    D.Type name binders constrs -> D.Type <$> trav.name name <*> traverse trav.binder binders <*> traverse (travConstructor trav) constrs
    D.GADT name mbSig constrs -> D.GADT <$> trav.name name <*> traverse trav.term mbSig <*> traverse (travGadtConstructor trav) constrs
    D.Signature name ty -> D.Signature <$> trav.name name <*> trav.term ty
    D.Fixity fixity op relations -> castFixity @p fixity <$> trav.name op <*> traverse trav.name relations

-- | doesn't handle Fixity
partialTravDeclaration :: Applicative m => AstTraversal p q m -> Declaration p -> m (Declaration q)
partialTravDeclaration trav (decl :@ loc) =
    Located loc <$> case decl of
        D.Value binding locals -> D.Value <$> trav.binding binding <*> traverse trav.declaration locals -- does a reversed order make more sense?
        D.Type name binders constrs -> D.Type <$> trav.name name <*> traverse trav.binder binders <*> traverse (travConstructor trav) constrs
        D.GADT name mbSig constrs -> D.GADT <$> trav.name name <*> traverse trav.term mbSig <*> traverse (travGadtConstructor trav) constrs
        D.Signature name ty -> D.Signature <$> trav.name name <*> trav.term ty
        D.Fixity{} -> error "partialTravDeclaration: encountered Fixity"

travConstructor :: Applicative m => AstTraversal p q m -> Constructor p -> m (Constructor q)
travConstructor trav con = D.Constructor con.loc <$> trav.name con.name <*> traverse trav.term con.args

travGadtConstructor :: Applicative m => AstTraversal p q m -> GadtConstructor p -> m (GadtConstructor q)
travGadtConstructor trav con = D.GadtConstructor con.loc <$> trav.name con.name <*> trav.term con.sig

-- do constructors even need a separate function in an AstTraversal? I feel like the default implementation is always what you want
-- whenever you add some logic for constructors, you probably want to do so for the type declarations as well

defTravBinding :: Applicative m => AstTraversal p q m -> Binding p -> m (Binding q)
defTravBinding trav = \case
    ValueB{pat, body} -> ValueB <$> trav.pattern_ pat <*> trav.term body
    FunctionB{name, args, body} -> FunctionB <$> trav.name name <*> traverse trav.pattern_ args <*> trav.term body

defTravBinder :: Applicative m => AstTraversal p q m -> VarBinder p -> m (VarBinder q)
defTravBinder trav VarBinder{var, kind} = VarBinder <$> trav.name var <*> traverse trav.term kind

defTravStatement :: Applicative m => AstTraversal p q m -> DoStatement p -> m (DoStatement q)
defTravStatement trav = traverse \case
    Bind pat body -> Bind <$> trav.pattern_ pat <*> trav.term body
    With pat body -> With <$> trav.pattern_ pat <*> trav.term body
    DoLet binding -> DoLet <$> trav.binding binding
    Action term -> Action <$> trav.term term

defTrav :: (FixityAgrees p q, DepResAgrees p q, NameAt p ~ NameAt q, Applicative m) => UntiedTraversal p q m
defTrav =
    UntiedTraversal
        { term = defTravTerm
        , pattern_ = defTravPattern
        , declaration = defTravDeclaration
        , name = const pure
        , binding = defTravBinding
        , binder = defTravBinder
        , statement = defTravStatement
        }

mkTrav
    :: Applicative m
    => (AstTraversal p q m -> Term p -> m (Term q))
    -- ^ term traversal
    -> (AstTraversal p q m -> Pattern p -> m (Pattern q))
    -- ^ pattern traversal
    -> (AstTraversal p q m -> Declaration p -> m (Declaration q))
    -- ^ declaration traversal
    -> (AstTraversal p q m -> NameAt p -> m (NameAt q))
    -- ^ name traversal
    -> UntiedTraversal p q m
mkTrav term pattern_ declaration name =
    UntiedTraversal
        { term
        , pattern_
        , declaration
        , name
        , binding = defTravBinding
        , binder = defTravBinder
        , statement = defTravStatement
        }

-- some type-level trickery to make default traversals work with more passes

-- now that I think about it, another solution would have been a Pass singleton

class FixityAgrees (p :: Pass) (q :: Pass) where
    castInfix :: p < 'Fixity => [(Expr q, Maybe (NameAt q))] -> Expr q -> Expr_ q
    castInfixP :: p < 'Fixity => [(Pattern q, NameAt q)] -> Pattern q -> Pattern_ q
instance {-# OVERLAPPABLE #-} q < 'Fixity => FixityAgrees p q where
    castInfix = InfixE
    castInfixP = InfixP
instance FixityAgrees 'Fixity q where
    castInfix = error "unsatisfiable"
    castInfixP = error "unsatisfiable"

class DepResAgrees (p :: Pass) (q :: Pass) where
    castFixity :: p < 'DependencyRes => Fixity -> NameAt q -> PriorityRelation q -> Declaration_ q

instance {-# OVERLAPPABLE #-} q < 'DependencyRes => DepResAgrees p q where
    castFixity = D.Fixity

instance DepResAgrees 'DependencyRes q where
    castFixity = error "unsatisfiable"
