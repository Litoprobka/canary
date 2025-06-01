{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-partial-fields #-}

module Syntax.Term where

import Common (Skolem, UniVar)
import Common hiding (Name, Skolem, UniVar)
import Common qualified as C
import Data.List.NonEmpty qualified as NE
import Data.Type.Ord (type (<))
import Error.Diagnose (Position (..))
import LangPrelude hiding (show)
import Prettyprinter
import Syntax.Row
import Prelude (show)

type Term p = Located (Term_ p)
type Type p = Term p
type Expr p = Term p
type Type_ = Term_
type Expr_ = Term_

data Term_ (p :: Pass) where
    -- terminal constructors
    Name :: NameAt p -> Term_ p
    -- | 'a
    -- | type variables with an inferred forall binder
    ImplicitVar :: NameAt p ~ SimpleName => NameAt p -> Term_ p
    Parens :: NameAt p ~ SimpleName => Term p -> Term_ p
    UniVar :: UniVar -> Type_ 'DuringTypecheck
    Skolem :: Skolem -> Type_ 'DuringTypecheck
    Literal :: Literal -> Expr_ p
    -- shared between Expr and Type

    -- | value : Type
    Annotation :: Term p -> Type p -> Term_ p
    App :: Term p -> Term p -> Term_ p
    -- expression-only stuff
    Lambda :: Pattern p -> Expr p -> Expr_ p -- it's still unclear to me whether I want to desugar multi-arg lambdas while parsing

    -- | (f _ x + _ y)
    WildcardLambda :: NonEmpty (NameAt p) -> Expr p -> Expr_ p
    Let :: Binding p -> Expr p -> Expr_ p
    LetRec :: NonEmpty (Binding p) -> Expr p -> Expr_ p
    TypeApp :: Expr p -> Type p -> Expr_ p
    Case :: Expr p -> [(Pattern p, Expr p)] -> Expr_ p
    -- | Haskell's \cases
    Match :: [([Pattern p], Expr p)] -> Expr_ p
    If :: Expr p -> Expr p -> Expr p -> Expr_ p
    -- | .field.otherField.thirdField
    RecordLens :: NonEmpty OpenName -> Expr_ p
    -- | 'Constructor
    -- unlike the rest of the cases, variant tags and record fields
    -- don't need any kind of name resolution
    Variant :: OpenName -> Expr_ p
    Record :: Row (Expr p) -> Expr_ p
    List :: [Expr p] -> Expr_ p
    Do :: [DoStatement p] -> Expr p -> Expr_ p
    -- | an unresolved expression with infix / prefix operators
    InfixE :: p < 'Fixity => [(Expr p, Maybe (NameAt p))] -> Expr p -> Expr_ p
    -- type-only stuff
    Function :: Type p -> Type p -> Type_ p
    Q :: Quantifier -> Visibility -> Erased -> VarBinder p -> Type p -> Type_ p
    VariantT :: ExtRow (Type p) -> Type_ p
    RecordT :: ExtRow (Type p) -> Type_ p

data Quantifier = Forall | Exists deriving (Eq, Show)
data Visibility = Visible | Implicit | Hidden deriving (Eq, Show)
data Erased = Retained | Erased deriving (Eq, Show)

data Binding (p :: Pass)
    = ValueB {pat :: Pattern p, body :: Expr p}
    | FunctionB {name :: NameAt p, args :: NonEmpty (Pattern p), body :: Expr p}

data VarBinder p = VarBinder {var :: NameAt p, kind :: Maybe (Type p)}

plainBinder :: NameAt p -> VarBinder p
plainBinder = flip VarBinder Nothing

binderKind :: NameAt p ~ C.Name => VarBinder p -> Type p
binderKind binder = fromMaybe (Located (getLoc binder) $ Name $ Located (getLoc binder) TypeName) binder.kind

type DoStatement p = Located (DoStatement_ p)
data DoStatement_ (p :: Pass)
    = Bind (Pattern p) (Expr p)
    | With (Pattern p) (Expr p)
    | DoLet (Binding p)
    | Action (Expr p)

deriving instance Eq (Term_ 'DuringTypecheck)
deriving instance Eq (Term_ 'Parse)
deriving instance Eq (VarBinder 'DuringTypecheck)
deriving instance Eq (VarBinder 'Parse)
deriving instance Eq (DoStatement_ 'DuringTypecheck)
deriving instance Eq (DoStatement_ 'Parse)
deriving instance Eq (Binding 'DuringTypecheck)
deriving instance Eq (Binding 'Parse)

-- unfortunately, Term and Pattern are mutually recursive, so I had to copypaste
-- the entire pattern module here

type Pattern p = Located (Pattern_ p)
data Pattern_ (p :: Pass)
    = VarP (NameAt p)
    | WildcardP Text
    | AnnotationP (Pattern p) (Type p)
    | ConstructorP (NameAt p) [Pattern p]
    | VariantP OpenName (Pattern p)
    | RecordP (Row (Pattern p))
    | ListP [Pattern p]
    | LiteralP Literal

deriving instance Eq (Pattern_ 'DuringTypecheck)
deriving instance Eq (Pattern_ 'Parse)

instance Pretty (NameAt p) => Show (Pattern_ p) where
    show = show . pretty

instance Pretty (NameAt p) => Pretty (Binding p) where
    pretty = \case
        ValueB pat body -> pretty pat <+> "=" <+> pretty body
        FunctionB name args body -> pretty name <+> concatWith (<+>) (pretty <$> args) <+> "=" <+> pretty body

instance Pretty (NameAt p) => Pretty (Expr_ p) where
    pretty = go (0 :: Int) . Located dummyLoc
      where
        go n (L e) = case e of
            Lambda arg body -> parensWhen 1 $ "λ" <> pretty arg <+> compressLambda body
            WildcardLambda _ l@(L List{}) -> pretty l
            WildcardLambda _ r@(L Record{}) -> pretty r
            WildcardLambda _ body -> "(" <> pretty body <> ")"
            App lhs rhs -> parensWhen 3 $ go 2 lhs <+> go 3 rhs
            TypeApp f ty -> parensWhen 3 $ go 2 f <+> "@" <> go 3 ty
            Let binding body -> "let" <+> pretty binding <> ";" <+> pretty body
            LetRec bindings body -> "let rec" <+> sep ((<> ";") . pretty <$> NE.toList bindings) <+> pretty body
            Case arg matches -> nest 4 (vsep $ ("case" <+> pretty arg <+> "of" :) $ matches <&> \(pat, body) -> pretty pat <+> "->" <+> pretty body)
            Match matches -> nest 4 (vsep $ ("match" :) $ matches <&> \(pats, body) -> sep (parens . pretty <$> pats) <+> "->" <+> pretty body)
            If cond true false -> "if" <+> pretty cond <+> "then" <+> pretty true <+> "else" <+> pretty false
            Annotation expr ty -> parensWhen 1 $ pretty expr <+> ":" <+> pretty ty
            Name name -> pretty name
            ImplicitVar var -> pretty var
            Parens expr -> parens $ pretty expr
            RecordLens fields -> encloseSep "." "" "." $ toList $ pretty <$> fields
            Variant name -> pretty name
            Record row -> braces . sep . punctuate comma . map recordField $ sortedRow row
            List xs -> brackets . sep . punctuate comma $ pretty <$> xs
            Do stmts lastAction -> nest 2 $ vsep ("do" : fmap pretty stmts <> [pretty lastAction])
            Literal lit -> pretty lit
            InfixE pairs last' -> "?(" <> sep (concatMap (\(lhs, op) -> go 3 lhs : maybe [] (pure . pretty) op) pairs <> [pretty last']) <> ")"
            Skolem skolem -> pretty skolem
            UniVar uni -> pretty uni
            Function from to -> parensWhen 2 $ go 2 from <+> "->" <+> pretty to
            Q q vis er binder body -> parensWhen 2 $ kw q er <+> prettyBinder binder <+> compressQ q vis er body
            VariantT row -> brackets . withExt row . sep . punctuate comma . map variantItem $ sortedRow row.row
            RecordT row -> braces . withExt row . sep . punctuate comma . map recordTyField $ sortedRow row.row
          where
            parensWhen minPrec
                | n >= minPrec = parens
                | otherwise = id
            recordField (name, body) = pretty name <+> "=" <+> pretty body
            withExt row = maybe id (\r doc -> doc <+> "|" <+> pretty r) (extension row)

            kw Forall Erased = "∀"
            kw Forall Retained = "Π"
            kw Exists Erased = "∃"
            kw Exists Retained = "Σ"

            compressLambda (L term) = case term of
                Lambda pat body -> pretty pat <+> compressLambda body
                other -> "->" <+> pretty other

            compressQ q vis er (L term) = case term of
                Q q' vis' er' binder body
                    | q == q' && vis == vis' && er == er' ->
                        parens (prettyBinder binder) <+> compressQ q vis er body
                other -> arrOrDot q vis <+> pretty other

            arrOrDot Forall Visible = "->"
            arrOrDot Exists Visible = "**"
            arrOrDot _ _ = "."

            -- todo: a special case for unit
            variantItem (name, ty) = pretty name <+> pretty ty
            recordTyField (name, ty) = pretty name <+> ":" <+> pretty ty

dummyLoc :: Loc
dummyLoc = C.Loc Position{file = "<none>", begin = (0, 0), end = (0, 0)}

instance Pretty (NameAt pass) => Pretty (VarBinder pass) where
    pretty = prettyBinder

prettyBinder :: Pretty (NameAt pass) => VarBinder pass -> Doc ann
prettyBinder (VarBinder var Nothing) = pretty var
prettyBinder (VarBinder var (Just kind)) = parens $ pretty var <+> ":" <+> pretty kind

instance Pretty (NameAt p) => Pretty (DoStatement_ p) where
    pretty = \case
        Bind pat expr -> pretty pat <+> "<-" <+> pretty expr
        With pat expr -> "with" <+> pretty pat <+> "<-" <+> pretty expr
        DoLet binding -> pretty binding
        Action expr -> pretty expr

instance Pretty (NameAt p) => Show (Expr_ p) where
    show = show . pretty

instance HasLoc (NameAt p) => HasLoc (Binding p) where
    getLoc = \case
        ValueB pat body -> zipLocOf pat body
        FunctionB name _ body -> zipLocOf name body

instance HasLoc (NameAt pass) => HasLoc (VarBinder pass) where
    getLoc VarBinder{var, kind = Nothing} = getLoc var
    getLoc VarBinder{var, kind = Just ty} = zipLocOf var ty

instance Pretty (NameAt pass) => Pretty (Pattern_ pass) where
    pretty = go 0 . Located dummyLoc
      where
        go :: Int -> Pattern pass -> Doc ann
        go n (L p) = case p of
            VarP name -> pretty name
            WildcardP txt -> pretty txt
            AnnotationP pat ty -> parens $ pretty pat <+> ":" <+> pretty ty
            ConstructorP name args -> parensWhen 1 $ sep (pretty name : map (go 1) args)
            VariantP name body -> parensWhen 1 $ pretty name <+> go 1 body -- todo: special case for unit?
            RecordP row -> braces . sep . punctuate comma . map recordField $ sortedRow row
            ListP items -> brackets . sep $ map pretty items
            LiteralP lit -> pretty lit
          where
            parensWhen minPrec
                | n >= minPrec = parens
                | otherwise = id

            recordField (name, pat) = pretty name <+> "=" <+> pretty pat

class FixityAgrees (p :: Pass) (q :: Pass) where
    castInfix :: p < 'Fixity => [(Expr q, Maybe (NameAt q))] -> Expr q -> Expr_ q
instance {-# OVERLAPPABLE #-} q < 'Fixity => FixityAgrees p q where
    castInfix = InfixE
instance FixityAgrees 'Fixity q where
    castInfix = error "unsatisfiable"
instance FixityAgrees 'DuringTypecheck q where
    castInfix = error "unsatisfiable"

class TcAgrees (p :: Pass) (q :: Pass) where
    castUni :: p ~ 'DuringTypecheck => UniVar -> Type_ q
    castSkolem :: p ~ 'DuringTypecheck => Skolem -> Type_ q
instance TcAgrees p 'DuringTypecheck where
    castUni = UniVar
    castSkolem = Skolem
instance {-# OVERLAPPABLE #-} p != 'DuringTypecheck => TcAgrees p q where
    castUni = error "unsatisfiable"
    castSkolem = error "unsatisfiable"

instance
    ( NameAt p ~ NameAt q
    , FixityAgrees p q
    , TcAgrees p q
    )
    => Cast Expr_ p q
    where
    cast = \case
        Lambda pat body -> Lambda (cast' pat) (cast' body)
        WildcardLambda args body -> WildcardLambda args (cast' body)
        App lhs rhs -> App (cast' lhs) (cast' rhs)
        TypeApp func ty -> TypeApp (cast' func) (cast' ty)
        Let binding expr -> Let (cast binding) (cast' expr)
        LetRec bindings expr -> LetRec (fmap cast bindings) (cast' expr)
        Case arg matches -> Case (cast' arg) (fmap (bimap cast' cast') matches)
        Match matches -> Match (fmap (bimap (fmap cast') cast') matches)
        If cond true false -> If (cast' cond) (cast' true) (cast' false)
        Annotation expr ty -> Annotation (cast' expr) (cast' ty)
        Record row -> Record (fmap cast' row)
        List exprs -> List (fmap cast' exprs)
        Do stmts ret -> Do (fmap cast' stmts) (cast' ret)
        InfixE pairs l -> castInfix @p (fmap (first cast') pairs) (cast' l)
        Name name -> Name name
        RecordLens oname -> RecordLens oname
        Variant oname -> Variant oname
        Literal lit -> Literal lit
        Function lhs rhs -> Function (cast' lhs) (cast' rhs)
        Q q dep vis binder body -> Q q dep vis (cast binder) (cast' body)
        VariantT row -> VariantT (fmap cast' row)
        RecordT row -> RecordT (fmap cast' row)
        ImplicitVar var -> ImplicitVar var
        Parens expr -> Parens (cast' expr)
        UniVar uni -> castUni uni
        Skolem skolem -> castSkolem skolem
      where
        cast' :: (Functor f, Cast con p q) => f (con p) -> f (con q)
        cast' = fmap cast

instance (NameAt p ~ NameAt q, Cast Pattern_ p q, Cast Expr_ p q) => Cast Binding p q where
    cast = \case
        ValueB pat body -> ValueB (fmap cast pat) (fmap cast body)
        FunctionB name args body -> FunctionB name ((fmap . fmap) cast args) (fmap cast body)
instance (Cast Expr_ p q, Cast Pattern_ p q, Cast Binding p q) => Cast DoStatement_ p q where
    cast = \case
        Bind pat expr -> Bind (fmap cast pat) (fmap cast expr)
        With pat expr -> With (fmap cast pat) (fmap cast expr)
        DoLet binding -> DoLet (cast binding)
        Action expr -> Action (fmap cast expr)

instance (NameAt p ~ NameAt q, Cast Term_ p q) => Cast VarBinder p q where
    cast VarBinder{var, kind} = VarBinder{var, kind = (fmap . fmap) cast kind}

instance (NameAt p ~ NameAt q, Cast Term_ p q) => Cast Pattern_ p q where
    cast = \case
        VarP name -> VarP name
        WildcardP name -> WildcardP name
        AnnotationP pat ty -> AnnotationP (fmap cast pat) (fmap cast ty)
        ConstructorP name pats -> ConstructorP name ((fmap . fmap) cast pats)
        VariantP name pat -> VariantP name (fmap cast pat)
        RecordP row -> RecordP ((fmap . fmap) cast row)
        ListP pats -> ListP ((fmap . fmap) cast pats)
        LiteralP lit -> LiteralP lit

-- one place where recursion schemes would come in handy
--
-- this should probably be moved to the NameRes pass, since we
-- have to keep track of local variables here
collectReferencedNames :: Type p -> [NameAt p]
collectReferencedNames = go
  where
    go (L inner) = case inner of
        Name name -> [name]
        ImplicitVar var -> [var]
        Parens expr -> go expr
        UniVar{} -> []
        Skolem _ -> []
        Literal _ -> []
        RecordLens{} -> []
        Variant{} -> []
        Let{} -> error "collectReferencedNames: local bindings are not supported yet"
        LetRec{} -> error "collectReferencedNames: local bindings are not supported yet"
        Case{} -> error "collectReferencedNames: local bindings are not supported yet"
        Match{} -> error "collectReferencedNames: local bindings are not supported yet"
        If cond true false -> go cond <> go true <> go false
        List xs -> foldMap go xs
        Lambda pat body -> collectReferencedNamesInPat pat <> go body
        WildcardLambda _pats body -> go body
        Annotation e ty -> go e <> go ty
        App lhs rhs -> go lhs <> go rhs
        TypeApp e ty -> go e <> go ty
        Function fn args -> go fn <> go args
        Q _ _ _ binder body -> case binder.kind of
            Nothing -> go body
            Just ty -> go ty <> go body
        VariantT row -> foldMap go $ toList row
        RecordT row -> foldMap go $ toList row
        Record row -> foldMap go $ toList row
        InfixE pairs lastE -> foldMap (\(e, mbName) -> go e <> maybeToList mbName) pairs <> go lastE
        Do _stmts _action -> error "collectReferencedNames: local bindings are not supported yet"

-- | collects all to-be-declared names in a pattern
collectNamesInPat :: Pattern p -> [NameAt p]
collectNamesInPat (L p) = case p of
    VarP name -> [name]
    WildcardP{} -> []
    AnnotationP pat _ -> collectNamesInPat pat
    VariantP _ pat -> collectNamesInPat pat
    ConstructorP _ pats -> foldMap collectNamesInPat pats
    ListP pats -> foldMap collectNamesInPat pats
    RecordP row -> foldMap collectNamesInPat $ toList row
    LiteralP _ -> []

collectReferencedNamesInPat :: Pattern p -> [NameAt p]
collectReferencedNamesInPat = go
  where
    go (L p) = case p of
        VarP _ -> []
        WildcardP{} -> []
        AnnotationP pat ty -> go pat <> collectReferencedNames ty
        VariantP _ pat -> go pat
        ConstructorP con pats -> con : foldMap go pats
        ListP pats -> foldMap go pats
        RecordP row -> foldMap go $ toList row
        LiteralP _ -> []

collectNamesInBinding :: Binding p -> [NameAt p]
collectNamesInBinding = \case
    FunctionB name _ _ -> [name]
    ValueB pat _ -> collectNamesInPat pat

{-
-- >>> pretty $ Function (Var "a") (Record (fromList [("x", Name "Int"), ("x", Name "a")]) Nothing)
-- >>> pretty $ Forall "a" $ Forall "b" $ Forall "c" $ Name "a" `Function` (Name "b" `Function` Name "c")
-- >>> pretty $ Forall "a" $ (Forall "b" $ Name "b" `Function` Name "a") `Function` Name "a"
-- >>> pretty $ App (Forall "f" $ Name "f") (Name "b") `Function` (App (App (Name "c") (Name "a")) $ App (Name "d") (Name "e"))
-- >>> pretty $ Record (fromList [("x", Name "Bool")]) (Just "r")
-- >>> pretty $ Variant (fromList [("E", Name "Unit")]) (Just "v")
-- a -> {x : Int, x : a}
-- ∀a. ∀b. ∀c. a -> b -> c
-- ∀a. (∀b. b -> a) -> a
-- (∀f. f) b -> c a (d e)
-- {x : Bool | r}
-- [E Unit | v]
-}
