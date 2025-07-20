{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-partial-fields #-}

module Syntax.Term where

import Common hiding (Name, UniVar)
import Common qualified as C
import Data.List.NonEmpty qualified as NE
import Data.Row
import Data.Type.Ord (type (<))
import Error.Diagnose (Position (..))
import LangPrelude hiding (show)
import Prettyprinter
import Prettyprinter.Render.Terminal (AnsiStyle)
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
    | App Visibility (Term p) (Term p)
    | -- expression-only stuff
      Lambda Visibility (Pattern p) (Expr p) -- it's still unclear to me whether I want to desugar multi-arg lambdas while parsing
    | -- | (f _ x + _ y)
      WildcardLambda (NonEmpty (NameAt p)) (Expr p)
    | Let (Binding p) (Expr p)
    | LetRec (NonEmpty (Binding p)) (Expr p)
    | Case (Expr p) [(Pattern p, Expr p)]
    | -- | Haskell's \cases
      Match [(NonEmpty (Pattern p), Expr p)]
    | If (Expr p) (Expr p) (Expr p)
    | -- | 'Constructor
      -- unlike the rest of the cases, variant tags and record fields
      -- don't need any kind of name resolution
      Variant OpenName
    | Record (Row (Expr p))
    | RecordAccess (Expr p) OpenName
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
    | FunctionB {name :: NameAt p, args :: NonEmpty (Visibility, Pattern p), body :: Expr p}

data VarBinder p = VarBinder {var :: NameAt p, kind :: Maybe (Type p)}

plainBinder :: NameAt p -> VarBinder p
plainBinder = flip VarBinder Nothing

binderKind :: NameAt p ~ C.Name => VarBinder p -> Type p
binderKind binder = fromMaybe (Name (TypeName :@ getLoc binder) :@ getLoc binder) binder.kind

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
    | ConstructorP (NameAt p) [(Visibility, Pattern p)]
    | VariantP OpenName (Pattern p)
    | RecordP (Row (Pattern p))
    | SigmaP Visibility (Pattern p) (Pattern p)
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
        FunctionB name args body ->
            prettyAnsi opts name
                <+> concatWith (<+>) (args <&> \(vis, pat) -> withVis vis (prettyAnsi opts pat))
                <+> "="
                <+> prettyAnsi opts body

instance PrettyAnsi (NameAt p) => PrettyAnsi (Expr_ p) where
    prettyAnsi opts = go 0 . Located dummyLoc
      where
        go :: Int -> Expr p -> Doc AnsiStyle
        go n (e :@ loc) = case e of
            lambda@Lambda{} -> parensWhen 1 $ "λ" <> compressLambda lambda
            WildcardLambda _ l@(L List{}) -> go 0 l
            WildcardLambda _ r@(L Record{}) -> go 0 r
            WildcardLambda _ body -> "(" <> go 0 body <> ")"
            App vis lhs rhs -> parensWhen 3 $ go 2 lhs <+> withVis vis (go 3 rhs)
            Let binding body -> "let" <+> prettyAnsi opts binding <> ";" <+> go 0 body
            LetRec bindings body -> "let rec" <+> sep ((<> ";") . prettyAnsi opts <$> NE.toList bindings) <+> go 0 body
            Case arg matches -> nest 4 (vsep $ ("case" <+> go 0 arg <+> "of" :) $ matches <&> \(pat, body) -> prettyAnsi opts pat <+> "->" <+> go 0 body)
            Match matches ->
                nest
                    4
                    (vsep $ ("match" :) $ matches <&> \(pats, body) -> (sep . toList) (parens . prettyAnsi opts <$> pats) <+> "->" <+> go 0 body)
            If cond true false -> "if" <+> go 0 cond <+> "then" <+> go 0 true <+> "else" <+> go 0 false
            Annotation expr ty -> parensWhen 1 $ go 0 expr <+> ":" <+> go 0 ty
            Name name -> prettyAnsi opts name
            ImplicitVar var -> prettyAnsi opts var
            Parens expr -> parens $ go 0 expr
            Variant name -> prettyAnsi opts name
            Record row -> prettyRecord "=" (prettyAnsi opts) (go 0) (NoExtRow row)
            RecordAccess record field -> go 4 record <> "." <> pretty field
            Sigma x y -> parensWhen 1 $ go 0 x <+> "**" <+> go 0 y
            List xs -> brackets . sep . punctuate comma $ go 0 <$> xs
            Do stmts lastAction -> nest 2 $ vsep ("do" : fmap (prettyAnsi opts) stmts <> [go 0 lastAction])
            Literal lit -> prettyAnsi opts lit
            InfixE pairs last' -> "?(" <> sep (concatMap (\(lhs, op) -> go 3 lhs : maybe [] (pure . prettyAnsi opts) op) pairs <> [go 0 last']) <> ")"
            Function from to -> parensWhen 2 $ go 2 from <+> "->" <+> go 0 to
            qq@(Q q vis er _ _) -> parensWhen 2 $ kw q er <+> compressQ q vis er qq
            VariantT row -> prettyVariant (prettyAnsi opts) (go 0) row
            RecordT row -> prettyRecord ":" (prettyAnsi opts) (go 0) row
          where
            parensWhen minPrec
                | n >= minPrec = parens
                | otherwise = id

            kw Forall Erased = "∀"
            kw Forall Retained = "Π"
            kw Exists Erased = "∃"
            kw Exists Retained = "Σ"

            compressLambda = \case
                Lambda vis pat body -> withVis vis (prettyAnsi opts pat) <+> compressLambda (unLoc body)
                other -> "->" <+> go 0 (other :@ loc)

            compressQ q vis er = \case
                Q q' vis' er' binder body
                    | q == q' && vis == vis' && er == er' ->
                        prettyBinder opts binder <+> compressQ q vis er (unLoc body)
                other -> arrOrDot q vis <+> pretty other

            arrOrDot Forall Visible = "->"
            arrOrDot Exists Visible = "**"
            arrOrDot _ _ = "."

-- withVis Visible  blah --> blah
-- withVis Implicit blah -> @blah
-- withVis Hidden   blah -> @{blah}
withVis :: Visibility -> Doc ann -> Doc ann
withVis = \case
    Visible -> id
    Implicit -> ("@" <>)
    Hidden -> ("@" <>) . braces

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
            ConstructorP name args -> parensWhen 1 $ sep (prettyAnsi opts name : map (\(vis, pat) -> withVis vis $ go 1 pat) args)
            VariantP name body -> parensWhen 1 $ prettyAnsi opts name <+> go 1 body -- todo: special case for unit?
            RecordP row -> braces . sep . punctuate comma . map recordField $ sortedRow row
            SigmaP vis lhs rhs -> parensWhen 1 $ withVis vis (go 0 lhs) <+> "**" <+> go 0 rhs
            ListP items -> brackets . sep $ map (go 0) items
            LiteralP lit -> prettyAnsi opts lit
            InfixP pairs last' -> "?(" <> sep (concatMap (\(lhs, op) -> go 3 lhs : (pure . prettyAnsi opts) op) pairs <> [go 0 last']) <> ")"
          where
            parensWhen minPrec
                | n >= minPrec = parens
                | otherwise = id

            recordField (name, pat) = prettyAnsi opts name <+> "=" <+> go 0 pat
