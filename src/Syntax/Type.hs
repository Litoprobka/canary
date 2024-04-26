module Syntax.Type (Type' (..)) where

import Relude
import Syntax.Row

--  Note: Functor-Foldable-Traversable instances don't do the right thing with `Forall` and `Exists`
data Type' n
    = Name n
    | Var n
    | Application (Type' n) (Type' n)
    | Function (Type' n) (Type' n)
    | Forall n (Type' n)
    | Exists n (Type' n)
    | Variant (Row (Type' n))
    | Record (Row (Type' n))
    deriving (Show, Eq, Functor, Foldable, Traversable)
