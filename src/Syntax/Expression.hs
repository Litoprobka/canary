{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

-- {-# OPTIONS_GHC -freduction-depth=0 #-}

module Syntax.Expression (Expression (..), DoStatement (..), Binding (..), uniplate, collectNamesInBinding) where

import Relude hiding (show)

import Common (Cast (..), HasLoc (..), Literal, Loc, NameAt, Pass (..), zipLocOf)
import Data.List.NonEmpty qualified as NE
import Data.Type.Ord (type (<))
import GHC.TypeError (ErrorMessage (..), TypeError)
import LensyUniplate hiding (cast)
import Prettyprinter (
    Pretty,
    braces,
    brackets,
    comma,
    concatWith,
    encloseSep,
    nest,
    parens,
    pretty,
    punctuate,
    sep,
    vsep,
    (<+>),
 )
import Syntax.Pattern (Pattern)
import Syntax.Pattern qualified as P
import Syntax.Row
import Syntax.Type (Type', prettyType)
import Prelude (show)

data Binding (p :: Pass)
    = ValueBinding (Pattern p) (Expression p)
    | FunctionBinding (NameAt p) (NonEmpty (Pattern p)) (Expression p)

deriving instance Eq (Binding 'Parse)

data Expression (p :: Pass)
    = Lambda Loc (Pattern p) (Expression p) -- it's still unclear to me whether I want to desugar multi-arg lambdas while parsing
    | -- | (f _ x + _ y)
      WildcardLambda Loc (NonEmpty (NameAt p)) (Expression p)
    | Application (Expression p) (Expression p)
    | TypeApplication (Expression p) (Type' p)
    | Let Loc (Binding p) (Expression p)
    | LetRec Loc (NonEmpty (Binding p)) (Expression p)
    | Case Loc (Expression p) [(Pattern p, Expression p)]
    | -- | Haskell's \cases
      Match Loc [([Pattern p], Expression p)]
    | If Loc (Expression p) (Expression p) (Expression p)
    | -- | value : Type
      Annotation (Expression p) (Type' p)
    | Name (NameAt p)
    | -- | .field.otherField.thirdField
      RecordLens Loc (NonEmpty OpenName)
    | Constructor (NameAt p)
    | -- | 'Constructor
      -- unlike the rest of the cases, variant tags and record fields
      -- don't need any kind of name resolution
      Variant OpenName
    | Record Loc (Row (Expression p))
    | List Loc [Expression p]
    | Do Loc [DoStatement p] (Expression p)
    | Literal Literal
    | -- | an unresolved expression with infix / prefix operators
      p < Fixity => Infix [(Expression p, Maybe (NameAt p))] (Expression p)

deriving instance Eq (Expression 'Parse)

data DoStatement (p :: Pass)
    = Bind (Pattern p) (Expression p)
    | With Loc (Pattern p) (Expression p) -- with and let have leading keywords, so
    | DoLet Loc (Binding p) -- their locations are not derivable from argument locations
    | Action (Expression p)

deriving instance Eq (DoStatement 'Parse)

instance Pretty (NameAt p) => Pretty (Binding p) where
    pretty = \case
        ValueBinding pat body -> pretty pat <+> "=" <+> pretty body
        FunctionBinding name args body -> pretty name <+> concatWith (<+>) (pretty <$> args) <+> "=" <+> pretty body

instance Pretty (NameAt p) => Pretty (Expression p) where
    pretty = go (0 :: Int)
      where
        go n = \case
            Lambda _ arg body -> parensWhen 1 $ "λ" <> pretty arg <+> "->" <+> pretty body
            WildcardLambda _ _ l@List{} -> pretty l
            WildcardLambda _ _ r@Record{} -> pretty r
            WildcardLambda _ _ body -> "(" <> pretty body <> ")"
            Application lhs rhs -> parensWhen 3 $ go 2 lhs <+> go 3 rhs
            TypeApplication f ty -> pretty f <+> "@" <> prettyType 3 ty
            Let _ binding body -> "let" <+> pretty binding <> ";" <+> pretty body
            LetRec _ bindings body -> "let rec" <+> sep ((<> ";") . pretty <$> NE.toList bindings) <+> pretty body
            Case _ arg matches -> nest 4 (vsep $ ("case" <+> pretty arg <+> "of" :) $ matches <&> \(pat, body) -> pretty pat <+> "->" <+> pretty body)
            Match _ matches -> nest 4 (vsep $ ("match" :) $ matches <&> \(pats, body) -> sep (parens . pretty <$> pats) <+> "->" <+> pretty body)
            If _ cond true false -> "if" <+> pretty cond <+> "then" <+> pretty true <+> "else" <+> pretty false
            Annotation expr ty -> parensWhen 1 $ pretty expr <+> ":" <+> pretty ty
            Name name -> pretty name
            RecordLens _ fields -> encloseSep "." "" "." $ toList $ pretty <$> fields
            Constructor name -> pretty name
            Variant name -> pretty name
            Record _ row -> braces . sep . punctuate comma . map recordField $ sortedRow row
            List _ xs -> brackets . sep . punctuate comma $ pretty <$> xs
            Do _ stmts lastAction -> nest 2 $ vsep ("do" : fmap pretty stmts <> [pretty lastAction])
            Literal lit -> pretty lit
            Infix pairs last' -> "?(" <> sep (concatMap (\(lhs, op) -> pretty lhs : maybe [] (pure . pretty) op) pairs <> [pretty last']) <> ")"
          where
            parensWhen minPrec
                | n >= minPrec = parens
                | otherwise = id
            recordField (name, body) = pretty name <+> "=" <+> pretty body

instance Pretty (NameAt p) => Pretty (DoStatement p) where
    pretty = \case
        Bind pat expr -> pretty pat <+> "<-" <+> pretty expr
        With _ pat expr -> "with" <+> pretty pat <+> "<-" <+> pretty expr
        DoLet _ binding -> pretty binding
        Action expr -> pretty expr

instance Pretty (NameAt p) => Show (Expression p) where
    show = show . pretty

instance HasLoc (NameAt p) => HasLoc (Expression p) where
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
        RecordLens loc _ -> loc
        Constructor name -> getLoc name
        Variant name -> getLoc name
        Record loc _ -> loc
        List loc _ -> loc
        Do loc _ _ -> loc
        Literal lit -> getLoc lit
        Infix ((e, _) : _) l -> zipLocOf e l
        Infix [] l -> getLoc l

instance HasLoc (NameAt p) => HasLoc (DoStatement p) where
    getLoc = \case
        Bind pat body -> zipLocOf pat body
        With loc _ _ -> loc
        DoLet loc _ -> loc
        Action expr -> getLoc expr

instance HasLoc (NameAt p) => HasLoc (Binding p) where
    getLoc = \case
        ValueBinding pat body -> zipLocOf pat body
        FunctionBinding name _ body -> zipLocOf name body

uniplate :: SelfTraversal Expression p p
uniplate f = \case
    Lambda loc pat body -> Lambda loc pat <$> f body
    WildcardLambda loc args body -> WildcardLambda loc args <$> f body
    Application lhs rhs -> Application <$> f lhs <*> f rhs
    TypeApplication func ty -> flip TypeApplication ty <$> f func
    Let loc binding expr -> Let loc <$> plateBinding f binding <*> f expr
    LetRec loc bindings expr -> LetRec loc <$> traverse (plateBinding f) bindings <*> f expr
    Case loc arg matches -> Case loc <$> f arg <*> traverse (traverse f) matches
    Match loc matches -> Match loc <$> traverse (traverse f) matches
    If loc cond true false -> If loc <$> f cond <*> f true <*> f false
    Annotation expr ty -> Annotation <$> f expr <*> pure ty
    Record loc row -> Record loc <$> traverse f row
    List loc exprs -> List loc <$> traverse f exprs
    Do loc stmts ret -> Do loc <$> traverse (plateStmt f) stmts <*> f ret
    Infix pairs l -> Infix <$> traverse (\(e, op) -> (,op) <$> f e) pairs <*> pure l
    Constructor name -> pure $ Constructor name
    n@Name{} -> pure n
    r@RecordLens{} -> pure r
    v@Variant{} -> pure v
    l@Literal{} -> pure l
  where
    plateStmt :: Traversal' (DoStatement p) (Expression p)
    plateStmt f' = \case
        Bind pat expr -> Bind pat <$> uniplate f' expr
        With loc pat expr -> With loc pat <$> uniplate f' expr
        DoLet loc binding -> DoLet loc <$> plateBinding f' binding
        Action expr -> Action <$> uniplate f' expr

    plateBinding :: Traversal' (Binding p) (Expression p)
    plateBinding f' = \case
        ValueBinding pat body -> ValueBinding pat <$> uniplate f' body
        FunctionBinding name args body -> FunctionBinding name args <$> uniplate f' body

class FixityAgrees (p :: Pass) (q :: Pass) where
    castInfix :: p < Fixity => [(Expression q, Maybe (NameAt q))] -> Expression q -> Expression q
instance {-# OVERLAPPABLE #-} q < Fixity => FixityAgrees p q where
    castInfix = Infix
instance FixityAgrees Fixity q where
    castInfix = error "unsatisfiable"
instance FixityAgrees DuringTypecheck q where
    castInfix = error "unsatisfiable"

instance (Cast Binding p q, Cast Pattern p q, Cast Type' p q, NameAt p ~ NameAt q, FixityAgrees p q) => Cast Expression p q where
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
        Infix pairs l -> castInfix @p (fmap (first cast) pairs) (cast l)
        Constructor name -> Constructor name
        Name name -> Name name
        RecordLens loc oname -> RecordLens loc oname
        Variant oname -> Variant oname
        Literal lit -> Literal lit

instance (NameAt p ~ NameAt q, Cast Pattern p q, Cast Expression p q) => Cast Binding p q where
    cast = \case
        ValueBinding pat body -> ValueBinding (cast pat) (cast body)
        FunctionBinding name args body -> FunctionBinding name (fmap cast args) (cast body)
instance (Cast Expression p q, Cast Pattern p q, Cast Binding p q) => Cast DoStatement p q where
    cast = \case
        Bind pat expr -> Bind (cast pat) (cast expr)
        With loc pat expr -> With loc (cast pat) (cast expr)
        DoLet loc binding -> DoLet loc (cast binding)
        Action expr -> Action (cast expr)

collectNamesInBinding :: Binding p -> [NameAt p]
collectNamesInBinding = \case
    FunctionBinding name _ _ -> [name]
    ValueBinding pat _ -> P.collectNames pat
