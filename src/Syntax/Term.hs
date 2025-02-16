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

type Type = Term
type Expr = Term

data Term (p :: Pass) where
    -- terminal constructors
    Name :: NameAt p -> Term p
    -- | 'a
    -- | type variables with an inferred forall binder
    ImplicitVar :: NameAt p ~ SimpleName => NameAt p -> Term p
    UniVar :: Loc -> UniVar -> Type 'DuringTypecheck
    Skolem :: Skolem -> Type 'DuringTypecheck
    Literal :: Literal -> Expr p
    -- shared between Expr and Type

    -- | value : Type
    Annotation :: Term p -> Type p -> Term p
    Application :: Term p -> Term p -> Term p
    -- expression-only stuff
    Lambda :: Loc -> Pattern p -> Expr p -> Expr p -- it's still unclear to me whether I want to desugar multi-arg lambdas while parsing

    -- | (f _ x + _ y)
    WildcardLambda :: Loc -> NonEmpty (NameAt p) -> Expr p -> Expr p
    Let :: Loc -> Binding p -> Expr p -> Expr p
    LetRec :: Loc -> NonEmpty (Binding p) -> Expr p -> Expr p
    TypeApplication :: Expr p -> Type p -> Expr p
    Case :: Loc -> Expr p -> [(Pattern p, Expr p)] -> Expr p
    -- | Haskell's \cases
    Match :: Loc -> [([Pattern p], Expr p)] -> Expr p
    If :: Loc -> Expr p -> Expr p -> Expr p -> Expr p
    -- | .field.otherField.thirdField
    RecordLens :: Loc -> NonEmpty OpenName -> Expr p
    -- | 'Constructor
    -- unlike the rest of the cases, variant tags and record fields
    -- don't need any kind of name resolution
    Variant :: OpenName -> Expr p
    Record :: Loc -> Row (Expr p) -> Expr p
    List :: Loc -> [Expr p] -> Expr p
    Do :: Loc -> [DoStatement p] -> Expr p -> Expr p
    -- | an unresolved expression with infix / prefix operators
    InfixE :: p < 'Fixity => [(Expr p, Maybe (NameAt p))] -> Expr p -> Expr p
    -- type-only stuff
    Function :: Loc -> Type p -> Type p -> Type p -- doesn't need a Loc, unless it's used in an infix position
    Forall :: Loc -> VarBinder p -> Type p -> Type p
    Exists :: Loc -> VarBinder p -> Type p -> Type p
    VariantT :: Loc -> ExtRow (Type p) -> Type p
    RecordT :: Loc -> ExtRow (Type p) -> Type p

data Binding (p :: Pass)
    = ValueB {pat :: Pattern p, body :: Expr p}
    | FunctionB {name :: NameAt p, args :: NonEmpty (Pattern p), body :: Expr p}

data VarBinder p = VarBinder {var :: NameAt p, kind :: Maybe (Type p)}

plainBinder :: NameAt p -> VarBinder p
plainBinder = flip VarBinder Nothing

binderKind :: NameAt p ~ C.Name => VarBinder p -> Type p
binderKind binder = fromMaybe (Name $ Located (getLoc binder) TypeName) binder.kind

data DoStatement (p :: Pass)
    = Bind (Pattern p) (Expr p)
    | With Loc (Pattern p) (Expr p) -- with and let have leading keywords, so
    | DoLet Loc (Binding p) -- their locations are not derivable from argument locations
    | Action (Expr p)

deriving instance Eq (Term 'DuringTypecheck)
deriving instance Eq (Term 'Parse)
deriving instance Eq (VarBinder 'DuringTypecheck)
deriving instance Eq (VarBinder 'Parse)
deriving instance Eq (DoStatement 'DuringTypecheck)
deriving instance Eq (DoStatement 'Parse)
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

instance Pretty (NameAt p) => Pretty (Expr p) where
    pretty = go (0 :: Int)
      where
        go n = \case
            Lambda _ arg body -> parensWhen 1 $ "λ" <> pretty arg <+> "->" <+> pretty body
            WildcardLambda _ _ l@List{} -> pretty l
            WildcardLambda _ _ r@Record{} -> pretty r
            WildcardLambda _ _ body -> "(" <> pretty body <> ")"
            Application lhs rhs -> parensWhen 3 $ go 2 lhs <+> go 3 rhs
            TypeApplication f ty -> parensWhen 3 $ go 2 f <+> "@" <> go 3 ty
            Let _ binding body -> "let" <+> pretty binding <> ";" <+> pretty body
            LetRec _ bindings body -> "let rec" <+> sep ((<> ";") . pretty <$> NE.toList bindings) <+> pretty body
            Case _ arg matches -> nest 4 (vsep $ ("case" <+> pretty arg <+> "of" :) $ matches <&> \(pat, body) -> pretty pat <+> "->" <+> pretty body)
            Match _ matches -> nest 4 (vsep $ ("match" :) $ matches <&> \(pats, body) -> sep (parens . pretty <$> pats) <+> "->" <+> pretty body)
            If _ cond true false -> "if" <+> pretty cond <+> "then" <+> pretty true <+> "else" <+> pretty false
            Annotation expr ty -> parensWhen 1 $ pretty expr <+> ":" <+> pretty ty
            Name name -> pretty name
            ImplicitVar var -> pretty var
            RecordLens _ fields -> encloseSep "." "" "." $ toList $ pretty <$> fields
            Variant name -> pretty name
            Record _ row -> braces . sep . punctuate comma . map recordField $ sortedRow row
            List _ xs -> brackets . sep . punctuate comma $ pretty <$> xs
            Do _ stmts lastAction -> nest 2 $ vsep ("do" : fmap pretty stmts <> [pretty lastAction])
            Literal lit -> pretty lit
            InfixE pairs last' -> "?(" <> sep (concatMap (\(lhs, op) -> pretty lhs : maybe [] (pure . pretty) op) pairs <> [pretty last']) <> ")"
            -- Var name -> pretty name
            Skolem skolem -> pretty skolem
            UniVar _ uni -> pretty uni
            Function _ from to -> parensWhen 2 $ go 2 from <+> "->" <+> pretty to
            Forall _ var body -> parensWhen 1 $ "∀" <> prettyBinder var <> "." <+> pretty body
            Exists _ var body -> parensWhen 1 $ "∃" <> prettyBinder var <> "." <+> pretty body
            VariantT _ row -> brackets . withExt row . sep . punctuate comma . map variantItem $ sortedRow row.row
            RecordT _ row -> braces . withExt row . sep . punctuate comma . map recordTyField $ sortedRow row.row
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

instance Pretty (NameAt p) => Pretty (DoStatement p) where
    pretty = \case
        Bind pat expr -> pretty pat <+> "<-" <+> pretty expr
        With _ pat expr -> "with" <+> pretty pat <+> "<-" <+> pretty expr
        DoLet _ binding -> pretty binding
        Action expr -> pretty expr

instance Pretty (NameAt p) => Show (Expr p) where
    show = show . pretty

instance HasLoc (NameAt p) => HasLoc (Expr p) where
    getLoc = \case
        Lambda loc _ _ -> loc
        WildcardLambda loc _ _ -> loc
        Application lhs rhs -> zipLocOf lhs rhs
        TypeApplication f ty -> zipLocOf f ty
        Let loc _ _ -> loc
        LetRec loc _ _ -> loc
        Case loc _ _ -> loc
        Match loc _ -> loc
        If loc _ _ _ -> loc
        Annotation expr ty -> zipLocOf expr ty
        Name name -> getLoc name
        ImplicitVar var -> getLoc var
        RecordLens loc _ -> loc
        Variant name -> getLoc name
        Record loc _ -> loc
        List loc _ -> loc
        Do loc _ _ -> loc
        Literal lit -> getLoc lit
        InfixE ((e, _) : _) l -> zipLocOf e l
        InfixE [] l -> getLoc l
        -- Var name -> getLoc name
        Skolem skolem -> getLoc skolem
        UniVar loc _ -> loc
        Function loc _ _ -> loc
        Forall loc _ _ -> loc
        Exists loc _ _ -> loc
        VariantT loc _ -> loc
        RecordT loc _ -> loc

instance HasLoc (NameAt p) => HasLoc (DoStatement p) where
    getLoc = \case
        Bind pat body -> zipLocOf pat body
        With loc _ _ -> loc
        DoLet loc _ -> loc
        Action expr -> getLoc expr

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
    castInfix :: p < 'Fixity => [(Expr q, Maybe (NameAt q))] -> Expr q -> Expr q
instance {-# OVERLAPPABLE #-} q < 'Fixity => FixityAgrees p q where
    castInfix = InfixE
instance FixityAgrees 'Fixity q where
    castInfix = error "unsatisfiable"
instance FixityAgrees 'DuringTypecheck q where
    castInfix = error "unsatisfiable"

class TcAgrees (p :: Pass) (q :: Pass) where
    castUni :: p ~ 'DuringTypecheck => Loc -> UniVar -> Type q
    castSkolem :: p ~ 'DuringTypecheck => Skolem -> Type q
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
    => Cast Expr p q
    where
    cast = \case
        Lambda loc pat body -> Lambda loc (cast pat) (cast body)
        WildcardLambda loc args body -> WildcardLambda loc args (cast body)
        Application lhs rhs -> Application (cast lhs) (cast rhs)
        TypeApplication func ty -> TypeApplication (cast func) (cast ty)
        Let loc binding expr -> Let loc (cast binding) (cast expr)
        LetRec loc bindings expr -> LetRec loc (fmap cast bindings) (cast expr)
        Case loc arg matches -> Case loc (cast arg) (fmap (bimap cast cast) matches)
        Match loc matches -> Match loc (fmap (bimap (fmap cast) cast) matches)
        If loc cond true false -> If loc (cast cond) (cast true) (cast false)
        Annotation expr ty -> Annotation (cast expr) (cast ty)
        Record loc row -> Record loc (fmap cast row)
        List loc exprs -> List loc (fmap cast exprs)
        Do loc stmts ret -> Do loc (fmap cast stmts) (cast ret)
        InfixE pairs l -> castInfix @p (fmap (first cast) pairs) (cast l)
        Name name -> Name name
        RecordLens loc oname -> RecordLens loc oname
        Variant oname -> Variant oname
        Literal lit -> Literal lit
        Function loc lhs rhs -> Function loc (cast lhs) (cast rhs)
        Forall loc var body -> Forall loc (cast var) (cast body)
        Exists loc var body -> Exists loc (cast var) (cast body)
        VariantT loc row -> VariantT loc (fmap cast row)
        RecordT loc row -> RecordT loc (fmap cast row)
        ImplicitVar var -> ImplicitVar var
        UniVar loc uni -> castUni loc uni
        Skolem skolem -> castSkolem skolem

instance (NameAt p ~ NameAt q, Cast Pattern p q, Cast Expr p q) => Cast Binding p q where
    cast = \case
        ValueB pat body -> ValueB (cast pat) (cast body)
        FunctionB name args body -> FunctionB name (fmap cast args) (cast body)
instance (Cast Expr p q, Cast Pattern p q, Cast Binding p q) => Cast DoStatement p q where
    cast = \case
        Bind pat expr -> Bind (cast pat) (cast expr)
        With loc pat expr -> With loc (cast pat) (cast expr)
        DoLet loc binding -> DoLet loc (cast binding)
        Action expr -> Action (cast expr)

instance (NameAt p ~ NameAt q, Cast Term p q) => Cast VarBinder p q where
    cast VarBinder{var, kind} = VarBinder{var, kind = fmap cast kind}

instance (NameAt p ~ NameAt q, Cast Term p q) => Cast Pattern p q where
    cast = \case
        VarP name -> VarP name
        WildcardP loc name -> WildcardP loc name
        AnnotationP pat ty -> AnnotationP (cast pat) (cast ty)
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
    go = \case
        Name name -> [name]
        ImplicitVar var -> [var]
        UniVar{} -> []
        Skolem _ -> []
        Literal _ -> []
        RecordLens{} -> []
        Variant{} -> []
        Let{} -> error "collectReferencedNames: local bindings are not supported yet"
        LetRec{} -> error "collectReferencedNames: local bindings are not supported yet"
        Case{} -> error "collectReferencedNames: local bindings are not supported yet"
        Match{} -> error "collectReferencedNames: local bindings are not supported yet"
        If _ cond true false -> go cond <> go true <> go false
        List _ xs -> foldMap go xs
        Lambda _ pat body -> collectReferencedNamesInPat pat <> go body
        WildcardLambda _ _pats body -> go body
        Annotation e ty -> go e <> go ty
        Application lhs rhs -> go lhs <> go rhs
        TypeApplication e ty -> go e <> go ty
        Function _ fn args -> go fn <> go args
        Forall _ _ body -> go body
        Exists _ _ body -> go body
        VariantT _ row -> foldMap go $ toList row
        RecordT _ row -> foldMap go $ toList row
        Record _ row -> foldMap go $ toList row
        InfixE pairs lastE -> foldMap (\(e, mbName) -> go e <> maybeToList mbName) pairs <> go lastE
        Do _ _stmts _action -> error "collectReferencedNames: local bindings are not supported yet"

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
uniplate f = \case
    Lambda loc pat body -> Lambda loc pat <$> f body -- for now, we're ignoring the pattern arguments
    WildcardLambda loc args body -> WildcardLambda loc args <$> f body -- same
    Application lhs rhs -> Application <$> f lhs <*> f rhs
    TypeApplication func ty -> TypeApplication <$> f func <*> f ty
    Let loc binding expr -> Let loc <$> plateBinding f binding <*> f expr
    LetRec loc bindings expr -> LetRec loc <$> traverse (plateBinding f) bindings <*> f expr
    Case loc arg matches -> Case loc <$> f arg <*> traverse (traverse f) matches
    Match loc matches -> Match loc <$> traverse (traverse f) matches
    If loc cond true false -> If loc <$> f cond <*> f true <*> f false
    Annotation expr ty -> Annotation <$> f expr <*> f ty
    Record loc row -> Record loc <$> traverse f row
    List loc exprs -> List loc <$> traverse f exprs
    Do loc stmts ret -> Do loc <$> traverse (plateStmt f) stmts <*> f ret
    InfixE pairs l -> InfixE <$> traverse (\(e, op) -> (,op) <$> f e) pairs <*> f l
    Function loc lhs rhs -> Function loc <$> f lhs <*> f rhs
    Forall loc var body -> Forall loc <$> plateBinder f var <*> f body
    Exists loc var body -> Exists loc <$> plateBinder f var <*> f body
    VariantT loc row -> VariantT loc <$> traverse f row
    RecordT loc row -> RecordT loc <$> traverse f row
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
    plateStmt f' = \case
        Bind pat expr -> Bind pat <$> uniplate f' expr
        With loc pat expr -> With loc pat <$> uniplate f' expr
        DoLet loc binding -> DoLet loc <$> plateBinding f' binding
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
-- >>> pretty $ Application (Forall "f" $ Name "f") (Name "b") `Function` (Application (Application (Name "c") (Name "a")) $ Application (Name "d") (Name "e"))
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
    Application lhs rhs -> Application <$> recur lhs <*> recur rhs
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
