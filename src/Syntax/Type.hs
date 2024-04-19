module Syntax.Type (TypeVariable, Type' (..)) where

import Relude

type Name = Text
type TypeVariable = Text

data Type'
    = Name Name
    | Var TypeVariable
    | Application Type' (NonEmpty Type')
    | Forall [TypeVariable] Type'
    | Exists [TypeVariable] Type'
    | Variant (HashMap Name [Type'])
    | Record (HashMap Name Type')
    deriving (Show, Eq)