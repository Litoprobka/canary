module Syntax.Expression (Expression (..), Binding (..)) where

import Relude

import Syntax.Pattern
import Syntax.Type

type OpenName = Text

data Binding n
    = ValueBinding (Pattern n) (Expression n)
    | FunctionBinding n (NonEmpty (Pattern n)) (Expression n)
    deriving (Show, Eq)

data Expression n
    = Lambda (NonEmpty (Pattern n)) (Expression n)
    | Application (Expression n) (NonEmpty (Expression n))
    | Let (Binding n) (Expression n)
    | Case (Expression n) [(Pattern n, Expression n)]
    | -- | Haskell's \cases
      Match [([Pattern n], Expression n)]
    | If (Expression n) (Expression n) (Expression n)
    | -- | value : Type
      Annotation (Expression n) (Type' n)
    | Name n
    | -- | .field.otherField.thirdField
      RecordLens (NonEmpty OpenName)
    | Constructor n
    | -- | 'Constructor
      -- unlike the rest of the cases, variant tags and record fields
      -- don't need any kind of name resolution
      Variant OpenName
    | Record (HashMap OpenName (Expression n))
    | List [Expression n]
    | IntLiteral Int
    | TextLiteral Text
    | CharLiteral Text
    deriving (Show, Eq)