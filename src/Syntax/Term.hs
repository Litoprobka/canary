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
import LangPrelude hiding (show)
import LensyUniplate (SelfTraversal, Traversal')
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
    Forall :: VarBinder p -> Type p -> Type_ p
    Exists :: VarBinder p -> Type p -> Type_ p
    VariantT :: ExtRow (Type p) -> Type_ p
    RecordT :: ExtRow (Type p) -> Type_ p

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

data Pattern (p :: Pass)
    = VarP (NameAt p)
    | WildcardP Loc Text
    | AnnotationP (Pattern p) (Type p)
    | ConstructorP (NameAt p) [Pattern p]
    | VariantP OpenName (Pattern p)
    | RecordP Loc (Row (Pattern p))
    | ListP Loc [Pattern p]
    | LiteralP Literal

deriving instance Eq (Pattern 'DuringTypecheck)
deriving instance Eq (Pattern 'Parse)

instance Pretty (NameAt p) => Show (Pattern p) where
    show = show . pretty

instance Pretty (NameAt p) => Pretty (Binding p) where
    pretty = \case
        ValueB pat body -> pretty pat <+> "=" <+> pretty body
        FunctionB name args body -> pretty name <+> concatWith (<+>) (pretty <$> args) <+> "=" <+> pretty body

instance Pretty (NameAt p) => Pretty (Expr_ p) where
    pretty = go (0 :: Int) . Located Blank
      where
        go n (Located _ e) = case e of
            Lambda arg body -> parensWhen 1 $ "λ" <> pretty arg <+> "->" <+> pretty body
            WildcardLambda _ l@(Located _ List{}) -> pretty l
            WildcardLambda _ r@(Located _ Record{}) -> pretty r
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
            InfixE pairs last' -> "?(" <> sep (concatMap (\(lhs, op) -> pretty lhs : maybe [] (pure . pretty) op) pairs <> [pretty last']) <> ")"
            Skolem skolem -> pretty skolem
            UniVar uni -> pretty uni
            Function from to -> parensWhen 2 $ go 2 from <+> "->" <+> pretty to
            Forall var body -> parensWhen 1 $ "∀" <> prettyBinder var <> "." <+> pretty body
            Exists var body -> parensWhen 1 $ "∃" <> prettyBinder var <> "." <+> pretty body
            VariantT row -> brackets . withExt row . sep . punctuate comma . map variantItem $ sortedRow row.row
            RecordT row -> braces . withExt row . sep . punctuate comma . map recordTyField $ sortedRow row.row
          where
            parensWhen minPrec
                | n >= minPrec = parens
                | otherwise = id
            recordField (name, body) = pretty name <+> "=" <+> pretty body
            withExt row = maybe id (\r doc -> doc <+> "|" <+> pretty r) (extension row)

            -- todo: a special case for unit
            variantItem (name, ty) = pretty name <+> pretty ty
            recordTyField (name, ty) = pretty name <+> ":" <+> pretty ty

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

instance HasLoc (NameAt p) => HasLoc (Pattern p) where
    getLoc = \case
        VarP name -> getLoc name
        WildcardP loc _ -> loc
        AnnotationP pat ty -> zipLocOf pat ty
        ConstructorP name args -> case listToMaybe $ reverse args of
            Nothing -> getLoc name
            Just lastArg -> zipLocOf name lastArg
        VariantP name arg -> zipLocOf name arg
        RecordP loc _ -> loc
        ListP loc _ -> loc
        LiteralP lit -> getLoc lit

instance HasLoc (NameAt pass) => HasLoc (VarBinder pass) where
    getLoc VarBinder{var, kind = Nothing} = getLoc var
    getLoc VarBinder{var, kind = Just ty} = zipLocOf var ty

instance Pretty (NameAt pass) => Pretty (Pattern pass) where
    pretty = go 0
      where
        go :: Int -> Pattern pass -> Doc ann
        go n = \case
            VarP name -> pretty name
            WildcardP _ txt -> pretty txt
            AnnotationP pat ty -> parens $ pretty pat <+> ":" <+> pretty ty
            ConstructorP name args -> parensWhen 1 $ sep (pretty name : map (go 1) args)
            VariantP name body -> parensWhen 1 $ pretty name <+> go 1 body -- todo: special case for unit?
            RecordP _ row -> braces . sep . punctuate comma . map recordField $ sortedRow row
            ListP _ items -> brackets . sep $ map pretty items
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
        Lambda pat body -> Lambda (cast pat) (cast' body)
        WildcardLambda args body -> WildcardLambda args (cast' body)
        App lhs rhs -> App (cast' lhs) (cast' rhs)
        TypeApp func ty -> TypeApp (cast' func) (cast' ty)
        Let binding expr -> Let (cast binding) (cast' expr)
        LetRec bindings expr -> LetRec (fmap cast bindings) (cast' expr)
        Case arg matches -> Case (cast' arg) (fmap (bimap cast cast') matches)
        Match matches -> Match (fmap (bimap (fmap cast) cast') matches)
        If cond true false -> If (cast' cond) (cast' true) (cast' false)
        Annotation expr ty -> Annotation (cast' expr) (cast' ty)
        Record row -> Record (fmap cast' row)
        List exprs -> List (fmap cast' exprs)
        Do stmts ret -> Do ((fmap . fmap) cast stmts) (cast' ret)
        InfixE pairs l -> castInfix @p (fmap (first cast') pairs) (cast' l)
        Name name -> Name name
        RecordLens oname -> RecordLens oname
        Variant oname -> Variant oname
        Literal lit -> Literal lit
        Function lhs rhs -> Function (cast' lhs) (cast' rhs)
        Forall var body -> Forall (cast var) (cast' body)
        Exists var body -> Exists (cast var) (cast' body)
        VariantT row -> VariantT (fmap cast' row)
        RecordT row -> RecordT (fmap cast' row)
        ImplicitVar var -> ImplicitVar var
        Parens expr -> Parens (cast' expr)
        UniVar uni -> castUni uni
        Skolem skolem -> castSkolem skolem
      where
        cast' = fmap cast

instance (NameAt p ~ NameAt q, Cast Pattern p q, Cast Expr_ p q) => Cast Binding p q where
    cast = \case
        ValueB pat body -> ValueB (cast pat) (fmap cast body)
        FunctionB name args body -> FunctionB name (fmap cast args) (fmap cast body)
instance (Cast Expr_ p q, Cast Pattern p q, Cast Binding p q) => Cast DoStatement_ p q where
    cast = \case
        Bind pat expr -> Bind (cast pat) (fmap cast expr)
        With pat expr -> With (cast pat) (fmap cast expr)
        DoLet binding -> DoLet (cast binding)
        Action expr -> Action (fmap cast expr)

instance (NameAt p ~ NameAt q, Cast Term_ p q) => Cast VarBinder p q where
    cast VarBinder{var, kind} = VarBinder{var, kind = (fmap . fmap) cast kind}

instance (NameAt p ~ NameAt q, Cast Term_ p q) => Cast Pattern p q where
    cast = \case
        VarP name -> VarP name
        WildcardP loc name -> WildcardP loc name
        AnnotationP pat ty -> AnnotationP (cast pat) (fmap cast ty)
        ConstructorP name pats -> ConstructorP name (fmap cast pats)
        VariantP name pat -> VariantP name (cast pat)
        RecordP loc row -> RecordP loc (fmap cast row)
        ListP loc pats -> ListP loc (fmap cast pats)
        LiteralP lit -> LiteralP lit

-- one place where recursion schemes would come in handy
--
-- this should probably be moved to the NameRes pass, since we
-- have to keep track of local variables here
collectReferencedNames :: Type p -> [NameAt p]
collectReferencedNames = go
  where
    go (Located _ inner) = case inner of
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
        Forall _ body -> go body
        Exists _ body -> go body
        VariantT row -> foldMap go $ toList row
        RecordT row -> foldMap go $ toList row
        Record row -> foldMap go $ toList row
        InfixE pairs lastE -> foldMap (\(e, mbName) -> go e <> maybeToList mbName) pairs <> go lastE
        Do _stmts _action -> error "collectReferencedNames: local bindings are not supported yet"

-- | collects all to-be-declared names in a pattern
collectNamesInPat :: Pattern p -> [NameAt p]
collectNamesInPat = \case
    VarP name -> [name]
    WildcardP{} -> []
    AnnotationP pat _ -> collectNamesInPat pat
    VariantP _ pat -> collectNamesInPat pat
    ConstructorP _ pats -> foldMap collectNamesInPat pats
    ListP _ pats -> foldMap collectNamesInPat pats
    RecordP _ row -> foldMap collectNamesInPat $ toList row
    LiteralP _ -> []

collectReferencedNamesInPat :: Pattern p -> [NameAt p]
collectReferencedNamesInPat = go
  where
    go = \case
        VarP _ -> []
        WildcardP{} -> []
        AnnotationP pat ty -> go pat <> collectReferencedNames ty
        VariantP _ pat -> go pat
        ConstructorP con pats -> con : foldMap go pats
        ListP _ pats -> foldMap go pats
        RecordP _ row -> foldMap go $ toList row
        LiteralP _ -> []

collectNamesInBinding :: Binding p -> [NameAt p]
collectNamesInBinding = \case
    FunctionB name _ _ -> [name]
    ValueB pat _ -> collectNamesInPat pat

-- | at the moment, uniplate works properly only for types
uniplate :: SelfTraversal Type p p
uniplate f = traverse \case
    Lambda pat body -> Lambda pat <$> f body -- for now, we're ignoring the pattern arguments
    WildcardLambda args body -> WildcardLambda args <$> f body -- same
    App lhs rhs -> App <$> f lhs <*> f rhs
    TypeApp func ty -> TypeApp <$> f func <*> f ty
    Let binding expr -> Let <$> plateBinding f binding <*> f expr
    LetRec bindings expr -> LetRec <$> traverse (plateBinding f) bindings <*> f expr
    Case arg matches -> Case <$> f arg <*> traverse (traverse f) matches
    Match matches -> Match <$> traverse (traverse f) matches
    If cond true false -> If <$> f cond <*> f true <*> f false
    Annotation expr ty -> Annotation <$> f expr <*> f ty
    Record row -> Record <$> traverse f row
    List exprs -> List <$> traverse f exprs
    Do stmts ret -> Do <$> traverse (plateStmt f) stmts <*> f ret
    InfixE pairs l -> InfixE <$> traverse (\(e, op) -> (,op) <$> f e) pairs <*> f l
    Function lhs rhs -> Function <$> f lhs <*> f rhs
    Forall var body -> Forall <$> plateBinder f var <*> f body
    Exists var body -> Exists <$> plateBinder f var <*> f body
    VariantT row -> VariantT <$> traverse f row
    RecordT row -> RecordT <$> traverse f row
    Parens expr -> Parens <$> f expr
    u@UniVar{} -> pure u
    s@Skolem{} -> pure s
    n@Name{} -> pure n
    i@ImplicitVar{} -> pure i
    r@RecordLens{} -> pure r
    v@Variant{} -> pure v
    l@Literal{} -> pure l
  where
    -- v@Var{} -> pure v

    plateStmt :: Traversal' (DoStatement p) (Term p)
    plateStmt f' = traverse \case
        Bind pat expr -> Bind pat <$> uniplate f' expr
        With pat expr -> With pat <$> uniplate f' expr
        DoLet binding -> DoLet <$> plateBinding f' binding
        Action expr -> Action <$> uniplate f' expr

    plateBinding :: Traversal' (Binding p) (Term p)
    plateBinding f' = \case
        -- todo: once dependent types land, we wouldn't be able to ignore patterns-in-types
        ValueB pat body -> ValueB pat <$> uniplate f' body
        FunctionB name args body -> FunctionB name args <$> uniplate f' body

    plateBinder :: Traversal' (VarBinder p) (Term p)
    plateBinder f' binder = VarBinder binder.var <$> traverse (uniplate f') binder.kind

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

uniplate :: Traversal' (Type' p) (Type' p)
uniplate = uniplate' id UniVar Skolem

instance {-# OVERLAPPING #-} NameAt p ~ CT.Name => UniplateCast (Type' p) (Type' DuringTypecheck) where
    uniplateCast = uniplate' id UniVar Skolem

instance (NameAt p ~ NameAt q, p != DuringTypecheck, q != DuringTypecheck) => UniplateCast (Type' p) (Type' q) where
    uniplateCast = uniplate' id undefined undefined -- we need some kind of `absurd` here

instance (Cast Type' p q, NameAt p ~ NameAt q) => Cast VarBinder p q where
    cast VarBinder{var, kind} = VarBinder{var, kind = fmap cast kind}

-- type-changing uniplate
uniplate'
    :: (NameAt p -> NameAt q)
    -> (p ~ DuringTypecheck => Loc -> CT.UniVar -> Type' q)
    -> (p ~ DuringTypecheck => CT.Skolem -> Type' q)
    -> SelfTraversal Type' p q
uniplate' castName castUni castSkolem recur = \case
    App lhs rhs -> App <$> recur lhs <*> recur rhs
    Function loc lhs rhs -> Function loc <$> recur lhs <*> recur rhs
    Forall loc var body -> Forall loc <$> castBinder var <*> recur body
    Exists loc var body -> Exists loc <$> castBinder var <*> recur body
    Variant loc row -> Variant loc <$> traverse recur row
    Record loc row -> Record loc <$> traverse recur row
    Name name -> pure $ Name $ castName name
    Var name -> pure $ Var $ castName name
    UniVar loc uni -> pure $ castUni loc uni
    Skolem skolem -> pure $ castSkolem skolem
  where
    castBinder (VarBinder name mbK) = VarBinder (castName name) <$> traverse recur mbK
-}
