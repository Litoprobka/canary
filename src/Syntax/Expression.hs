{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Syntax.Expression (Expression (..), Binding (..), HasInfix(..), noInfix) where

import Relude

import Common (HasLoc (..), Loc, NameAt, Pass (..), zipLoc)
import Prettyprinter (
    Pretty,
    braces,
    brackets,
    comma,
    concatWith,
    dquotes,
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
import Syntax.Row
import Syntax.Type (Type')

data Binding (p :: Pass)
    = ValueBinding Loc (Pattern p) (Expression p)
    | FunctionBinding Loc (NameAt p) (NonEmpty (Pattern p)) (Expression p)

deriving instance (Show (NameAt pass), Show (HasInfix pass)) => Show (Binding pass)
deriving instance (Eq (NameAt pass), Eq (HasInfix pass)) => Eq (Binding pass)

-- todo: some nodes don't need to store an explicit Loc. Instead, getLoc may zip the child node locs
-- the only difference is whether outer parenthesis are inculded, but seems like that only makes a differenc
-- for wildcard lambdas
--
-- Application, Annotation and some others
data Expression (p :: Pass)
    = Lambda Loc (Pattern p) (Expression p)
    | Application Loc (Expression p) (Expression p)
    | Let Loc (Binding p) (Expression p)
    | Case Loc (Expression p) [(Pattern p, Expression p)]
    | -- | Haskell's \cases
      Match Loc [([Pattern p], Expression p)]
    | If Loc (Expression p) (Expression p) (Expression p)
    | -- | value : Type
      Annotation Loc (Expression p) (Type' p)
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
    | IntLiteral Loc Int
    | TextLiteral Loc Text
    | CharLiteral Loc Text
    | -- | an unresolved expression with infix / prefix operators
      Infix (HasInfix p) [(Expression p, NameAt p)] (Expression p)

deriving instance Show (NameAt pass) => Show (Expression pass)
deriving instance Eq (NameAt pass) => Eq (Expression pass)

-- unresolved infix operators may only appear before the fixity resolution pass
data HasInfix (pass :: Pass) where
    Yes :: HasInfix 'Parse
    Yup :: HasInfix 'NameRes

noInfix :: HasInfix 'Fixity -> a
noInfix = \case {}

deriving instance Eq (HasInfix pass)
deriving instance Show (HasInfix pass)

instance Pretty (NameAt p) => Pretty (Binding p) where
    pretty = \case
        ValueBinding _ pat body -> pretty pat <+> "=" <+> pretty body
        FunctionBinding _ name args body -> pretty name <+> concatWith (<+>) (pretty <$> args) <+> "=" <+> pretty body

instance Pretty (NameAt p) => Pretty (Expression p) where
    pretty = go (0 :: Int)
      where
        go n = \case
            Lambda _ arg body -> parensWhen 1 $ "λ" <> pretty arg <+> "->" <+> pretty body
            Application _ lhs rhs -> parensWhen 3 $ go 2 lhs <+> go 3 rhs
            Let _ binding body -> "let" <+> pretty binding <> ";" <+> pretty body
            Case _ arg matches -> nest 4 (vsep $ ("case" <+> pretty arg <+> "of" :) $ matches <&> \(pat, body) -> pretty pat <+> "->" <+> pretty body)
            Match _ matches -> nest 4 (vsep $ ("match" :) $ matches <&> \(pats, body) -> sep (parens . pretty <$> pats) <+> "->" <+> pretty body)
            If _ cond true false -> "if" <+> pretty cond <+> "then" <+> pretty true <+> "else" <+> pretty false
            Annotation _ expr ty -> parensWhen 1 $ pretty expr <+> ":" <+> pretty ty
            Name name -> pretty name
            RecordLens _ fields -> encloseSep "." "" "." $ toList $ pretty <$> fields
            Constructor name -> pretty name
            Variant name -> pretty name
            Record _ row -> braces . sep . punctuate comma . map recordField $ sortedRow row
            List _ xs -> brackets . sep . punctuate comma $ pretty <$> xs
            IntLiteral _ num -> pretty num
            TextLiteral _ txt -> dquotes $ pretty txt
            CharLiteral _ c -> "'" <> pretty c <> "'"
            Infix _ pairs last' -> "?(" <> sep (map (\(lhs, op) -> pretty lhs <+> pretty op) pairs <> [pretty last']) <> ")"
          where
            parensWhen minPrec
                | n >= minPrec = parens
                | otherwise = id
            recordField (name, body) = pretty name <+> "=" <+> pretty body

instance HasLoc (NameAt p) => HasLoc (Expression p) where
    getLoc = \case
        Lambda loc _ _ -> loc
        Application loc _ _ -> loc
        Let loc _ _ -> loc
        Case loc _ _ -> loc
        Match loc _ -> loc
        If loc _ _ _ -> loc
        Annotation loc _ _ -> loc
        Name name -> getLoc name
        RecordLens loc _ -> loc
        Constructor name -> getLoc name
        Variant name -> getLoc name
        Record loc _ -> loc
        List loc _ -> loc
        IntLiteral loc _ -> loc
        TextLiteral loc _ -> loc
        CharLiteral loc _ -> loc
        Infix _ ((e, _) : _) l -> zipLoc (getLoc e) (getLoc l)
        Infix _ [] l -> getLoc l
