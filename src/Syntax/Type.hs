module Syntax.Type (Type' (..)) where

import Relude

type OpenName = Text

data Type' n
    = Name n
    | Var n
    | Application (Type' n) (NonEmpty (Type' n))
    | Forall [n] (Type' n)
    | Exists [n] (Type' n)
    | Variant (HashMap OpenName [Type' n])
    | Record (HashMap OpenName (Type' n))
    deriving (Show, Eq)