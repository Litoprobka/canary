{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-partial-fields #-}

module Syntax.Term where

import Common hiding (Name, Skolem, UniVar)
import Common qualified as C
import Data.List.NonEmpty qualified as NE
import Data.Type.Ord (type (<))
import Error.Diagnose (Position (..))
import LangPrelude hiding (show)
import Prettyprinter
import Prettyprinter.Render.Terminal (AnsiStyle)
import Syntax.Row
import Prelude (show)

type Term p = Located (Term_ p)
type Type p = Term p
type Expr p = Term p
type Type_ = Term_
type Expr_ = Term_

data Term_ p
    = -- terminal constructors
      Name (NameAt p)
    | -- | 'a
      -- | type variables with an inferred forall binder
      NameAt p ~ SimpleName => ImplicitVar (NameAt p)
    | NameAt p ~ SimpleName => Parens (Term p)
    | Literal Literal
    | -- shared between Expr and Type

      -- | value : Type
      Annotation (Term p) (Type p)
    | App (Term p) (Term p)
    | -- expression-only stuff
      Lambda (Pattern p) (Expr p) -- it's still unclear to me whether I want to desugar multi-arg lambdas while parsing
    | -- | (f _ x + _ y)
      WildcardLambda (NonEmpty (NameAt p)) (Expr p)
    | Let (Binding p) (Expr p)
    | LetRec (NonEmpty (Binding p)) (Expr p)
    | TypeApp (Expr p) (Type p)
    | Case (Expr p) [(Pattern p, Expr p)]
    | -- | Haskell's \cases
      Match [([Pattern p], Expr p)]
    | If (Expr p) (Expr p) (Expr p)
    | -- | .field.otherField.thirdField
      RecordLens (NonEmpty OpenName)
    | -- | 'Constructor
      -- unlike the rest of the cases, variant tags and record fields
      -- don't need any kind of name resolution
      Variant OpenName
    | Record (Row (Expr p))
    | -- | unlike lambdas, which may have a normal function type as well as a pi type, dependent pairs are distinct from records
      Sigma (Expr p) (Expr p)
    | List [Expr p]
    | Do [DoStatement p] (Expr p)
    | -- | an unresolved expression with infix / prefix operators
      p < 'Fixity => InfixE [(Expr p, Maybe (NameAt p))] (Expr p)
    | -- type-only stuff
      Function (Type p) (Type p)
    | Q Quantifier Visibility Erasure (VarBinder p) (Type p)
    | VariantT (ExtRow (Type p))
    | RecordT (ExtRow (Type p))

data Quantifier = Forall | Exists deriving (Eq, Show)
data Visibility = Visible | Implicit | Hidden deriving (Eq, Show)
data Erasure = Retained | Erased deriving (Eq, Show)

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

deriving instance Eq (Term_ 'Fixity)
deriving instance Eq (Term_ 'Parse)
deriving via (UnAnnotate (Term_ p)) instance PrettyAnsi (Term_ p) => Pretty (Term_ p)
deriving instance Eq (VarBinder 'Fixity)
deriving instance Eq (VarBinder 'Parse)
deriving instance Eq (DoStatement_ 'Fixity)
deriving instance Eq (DoStatement_ 'Parse)
deriving instance Eq (Binding 'Fixity)
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
    | -- infix constructors cannot have a higher-than-pattern precedence
      p < 'Fixity => InfixP [(Pattern p, NameAt p)] (Pattern p)

deriving instance Eq (Pattern_ 'Fixity)
deriving instance Eq (Pattern_ 'Parse)
deriving via (UnAnnotate (Pattern_ p)) instance PrettyAnsi (Pattern_ p) => Pretty (Pattern_ p)

instance Pretty (Pattern_ p) => Show (Pattern_ p) where
    show = show . pretty

instance PrettyAnsi (NameAt p) => PrettyAnsi (Binding p) where
    prettyAnsi opts = \case
        ValueB pat body -> prettyAnsi opts pat <+> "=" <+> prettyAnsi opts body
        FunctionB name args body -> prettyAnsi opts name <+> concatWith (<+>) (prettyAnsi opts <$> args) <+> "=" <+> prettyAnsi opts body

instance PrettyAnsi (NameAt p) => PrettyAnsi (Expr_ p) where
    prettyAnsi opts = go 0 . Located dummyLoc
      where
        go :: Int -> Expr p -> Doc AnsiStyle
        go n (L e) = case e of
            Lambda arg body -> parensWhen 1 $ "λ" <> prettyAnsi opts arg <+> compressLambda body
            WildcardLambda _ l@(L List{}) -> go 0 l
            WildcardLambda _ r@(L Record{}) -> go 0 r
            WildcardLambda _ body -> "(" <> go 0 body <> ")"
            App lhs rhs -> parensWhen 3 $ go 2 lhs <+> go 3 rhs
            TypeApp f ty -> parensWhen 3 $ go 2 f <+> "@" <> go 3 ty
            Let binding body -> "let" <+> prettyAnsi opts binding <> ";" <+> go 0 body
            LetRec bindings body -> "let rec" <+> sep ((<> ";") . prettyAnsi opts <$> NE.toList bindings) <+> go 0 body
            Case arg matches -> nest 4 (vsep $ ("case" <+> go 0 arg <+> "of" :) $ matches <&> \(pat, body) -> prettyAnsi opts pat <+> "->" <+> go 0 body)
            Match matches -> nest 4 (vsep $ ("match" :) $ matches <&> \(pats, body) -> sep (parens . prettyAnsi opts <$> pats) <+> "->" <+> go 0 body)
            If cond true false -> "if" <+> go 0 cond <+> "then" <+> go 0 true <+> "else" <+> go 0 false
            Annotation expr ty -> parensWhen 1 $ go 0 expr <+> ":" <+> go 0 ty
            Name name -> prettyAnsi opts name
            ImplicitVar var -> prettyAnsi opts var
            Parens expr -> parens $ go 0 expr
            RecordLens fields -> encloseSep "." "" "." $ toList $ prettyAnsi opts <$> fields
            Variant name -> prettyAnsi opts name
            Record row -> braces . sep . punctuate comma . map recordField $ sortedRow row
            Sigma x y -> parensWhen 1 $ go 0 x <+> "**" <+> go 0 y
            List xs -> brackets . sep . punctuate comma $ go 0 <$> xs
            Do stmts lastAction -> nest 2 $ vsep ("do" : fmap (prettyAnsi opts) stmts <> [go 0 lastAction])
            Literal lit -> prettyAnsi opts lit
            InfixE pairs last' -> "?(" <> sep (concatMap (\(lhs, op) -> go 3 lhs : maybe [] (pure . prettyAnsi opts) op) pairs <> [go 0 last']) <> ")"
            Function from to -> parensWhen 2 $ go 2 from <+> "->" <+> go 0 to
            Q q vis er binder body -> parensWhen 2 $ kw q er <+> prettyBinder opts binder <+> compressQ q vis er body
            VariantT row -> brackets . withExt row . sep . punctuate comma . map variantItem $ sortedRow row.row
            RecordT row -> braces . withExt row . sep . punctuate comma . map recordTyField $ sortedRow row.row
          where
            parensWhen minPrec
                | n >= minPrec = parens
                | otherwise = id
            recordField (name, body) = prettyAnsi opts name <+> "=" <+> go 0 body
            withExt row = maybe id (\r doc -> doc <+> "|" <+> go 0 r) (extension row)

            kw Forall Erased = "∀"
            kw Forall Retained = "Π"
            kw Exists Erased = "∃"
            kw Exists Retained = "Σ"

            compressLambda (term :@ loc) = case term of
                Lambda pat body -> prettyAnsi opts pat <+> compressLambda body
                _ -> "->" <+> go 0 (term :@ loc)

            compressQ q vis er (L term) = case term of
                Q q' vis' er' binder body
                    | q == q' && vis == vis' && er == er' ->
                        parens (prettyBinder opts binder) <+> compressQ q vis er body
                other -> arrOrDot q vis <+> pretty other

            arrOrDot Forall Visible = "->"
            arrOrDot Exists Visible = "**"
            arrOrDot _ _ = "."

            -- todo: a special case for unit
            variantItem (name, ty) = prettyAnsi opts name <+> go 0 ty
            recordTyField (name, ty) = prettyAnsi opts name <+> ":" <+> go 0 ty

dummyLoc :: Loc
dummyLoc = C.Loc Position{file = "<none>", begin = (0, 0), end = (0, 0)}

instance PrettyAnsi (NameAt pass) => PrettyAnsi (VarBinder pass) where
    prettyAnsi = prettyBinder

prettyBinder :: PrettyAnsi (NameAt pass) => PrettyOptions -> VarBinder pass -> Doc AnsiStyle
prettyBinder opts (VarBinder var Nothing) = prettyAnsi opts var
prettyBinder opts (VarBinder var (Just kind)) = parens $ prettyAnsi opts var <+> ":" <+> prettyAnsi opts kind

instance PrettyAnsi (NameAt p) => PrettyAnsi (DoStatement_ p) where
    prettyAnsi opts = \case
        Bind pat expr -> prettyAnsi opts pat <+> "<-" <+> prettyAnsi opts expr
        With pat expr -> "with" <+> prettyAnsi opts pat <+> "<-" <+> prettyAnsi opts expr
        DoLet binding -> prettyAnsi opts binding
        Action expr -> prettyAnsi opts expr

instance Pretty (Expr_ p) => Show (Expr_ p) where
    show = show . pretty

instance HasLoc (NameAt p) => HasLoc (Binding p) where
    getLoc = \case
        ValueB pat body -> zipLocOf pat body
        FunctionB name _ body -> zipLocOf name body

instance HasLoc (NameAt pass) => HasLoc (VarBinder pass) where
    getLoc VarBinder{var, kind = Nothing} = getLoc var
    getLoc VarBinder{var, kind = Just ty} = zipLocOf var ty

instance PrettyAnsi (NameAt pass) => PrettyAnsi (Pattern_ pass) where
    prettyAnsi opts = go 0 . Located dummyLoc
      where
        go :: Int -> Pattern pass -> Doc AnsiStyle
        go n (L p) = case p of
            VarP name -> prettyAnsi opts name
            WildcardP txt -> pretty txt
            AnnotationP pat ty -> parens $ go 0 pat <+> ":" <+> prettyAnsi opts ty
            ConstructorP name args -> parensWhen 1 $ sep (prettyAnsi opts name : map (go 1) args)
            VariantP name body -> parensWhen 1 $ prettyAnsi opts name <+> go 1 body -- todo: special case for unit?
            RecordP row -> braces . sep . punctuate comma . map recordField $ sortedRow row
            ListP items -> brackets . sep $ map (go 0) items
            LiteralP lit -> prettyAnsi opts lit
            InfixP pairs last' -> "?(" <> sep (concatMap (\(lhs, op) -> go 3 lhs : (pure . prettyAnsi opts) op) pairs <> [go 0 last']) <> ")"
          where
            parensWhen minPrec
                | n >= minPrec = parens
                | otherwise = id

            recordField (name, pat) = prettyAnsi opts name <+> "=" <+> go 0 pat

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
        Literal _ -> []
        RecordLens{} -> []
        Variant{} -> []
        Let{} -> error "collectReferencedNames: local bindings are not supported yet"
        LetRec{} -> error "collectReferencedNames: local bindings are not supported yet"
        Case{} -> error "collectReferencedNames: local bindings are not supported yet"
        Match{} -> error "collectReferencedNames: local bindings are not supported yet"
        If cond true false -> go cond <> go true <> go false
        List xs -> foldMap go xs
        Sigma x y -> go x <> go y
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
    InfixP pairs l -> foldMap (collectNamesInPat . fst) pairs <> collectNamesInPat l

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
        InfixP pairs l -> foldMap (\(pat, conOp) -> go pat <> [conOp]) pairs <> go l

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
