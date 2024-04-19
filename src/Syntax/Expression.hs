module Syntax.Expression (Expression (..)) where

import Relude

import Syntax.Pattern
import Syntax.Type

data Expression
    = Lambda (NonEmpty Pattern) Expression
    | Application Expression (NonEmpty Expression)
    | Let (NonEmpty (Pattern, Expression)) Expression
    | Case Expression [(Pattern, Expression)]
    | -- | Haskell's \case
      Match [([Pattern], Expression)]
    | If Expression Expression Expression
    | -- | value : Type
      Annotation Expression Type'
    | Name Name
    | -- | .field.otherField.thirdField
      RecordLens (NonEmpty Name)
    | Constructor Name
    | -- | 'Constructor
      Variant Name
    | Record (HashMap Name Expression)
    | List [Expression]
    | IntLiteral Int
    | TextLiteral Text
    | CharLiteral Text
    deriving (Show, Eq)