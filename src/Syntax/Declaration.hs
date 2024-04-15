module Syntax.Declaration (Declaration (..)) where

import Syntax.Pattern
import Syntax.Term (Term)
import Syntax.Type (Type', TypeVariable)

data Declaration
    = Value Name [Pattern] Term [Declaration] -- todo: forbid local type declarations?
    | Type Name [TypeVariable] [(Name, [Type'])]
    | Alias Name Type'
    | Signature Name Type'