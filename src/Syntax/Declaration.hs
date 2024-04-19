module Syntax.Declaration (Declaration (..)) where

import Relude
import Syntax.Pattern
import Syntax.Expression (Expression)
import Syntax.Type (Type', TypeVariable)

data Declaration
    = Value Name [Pattern] Expression [Declaration] -- todo: forbid local type declarations?
    | Type Name [TypeVariable] [(Name, [Type'])]
    | Alias Name Type'
    | Signature Name Type'
    deriving (Show, Eq)