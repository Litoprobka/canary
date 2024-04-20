module Syntax.Declaration (Declaration (..)) where

import Relude
import Syntax.Expression (Expression)
import Syntax.Pattern
import Syntax.Type (Type')

data Declaration n
    = Value n [Pattern n] (Expression n) [Declaration n] -- todo: forbid local type declarations?
    | Type n [n] [(n, [Type' n])]
    | Alias n (Type' n)
    | Signature n (Type' n)
    deriving (Show, Eq)