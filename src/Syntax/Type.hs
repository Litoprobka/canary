module Syntax.Type (Type' (..)) where

import Relude

type OpenName = Text

data Type' n
    = Name n
    | Var n
    | Application (Type' n) (Type' n)
    | Function (Type' n) (Type' n)
    | Forall (NonEmpty n) (Type' n)
    | Exists (NonEmpty n) (Type' n)
    | Variant (HashMap OpenName (Type' n))
    | Record (HashMap OpenName (Type' n))
    deriving (Show, Eq)