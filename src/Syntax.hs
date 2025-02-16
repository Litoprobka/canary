module Syntax (module Export) where

-- a re-export of all AST types for convenience

import Prelude ()

import Syntax.Core as Export (CorePattern, CoreTerm)
import Syntax.Declaration as Export (Constructor, Declaration, GadtConstructor)
import Syntax.Row as Export (Row)
import Syntax.Term as Export (Binding, DoStatement, Expr, Pattern, Term, Type, VarBinder)
