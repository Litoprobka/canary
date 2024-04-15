module Syntax.All (Name, Declaration, Pattern, Term, Type') where

-- a re-export of all AST types for convenience

import Relude

import Syntax.Declaration (Declaration)
import Syntax.Pattern (Pattern)
import Syntax.Term (Term)
import Syntax.Type (Type')

type Name = Text