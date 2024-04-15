module Syntax.Term (Term (..)) where

import Relude

import Syntax.Pattern
import Syntax.Type

data Term
    = Lambda (NonEmpty Pattern) Term
    | Application Term (NonEmpty Term)
    | Let (NonEmpty (Pattern, Term)) Term
    | Case Term [(Pattern, Term)]
    | Match [([Pattern], Term)]
    | -- | Haskell's \case
      If Term Term Term
    | -- | value : Type
      Annotation Term Type'
    | Name Name
    | -- | .field.otherField.thirdField
      RecordLens [Name]
    | Constructor Name
    | -- | 'Constructor
      Variant Name
    | Record (HashMap Name Term)
    | List [Term]
    | IntLiteral Int
    | TextLiteral Text
    | CharLiteral Text
    deriving (Show, Eq)