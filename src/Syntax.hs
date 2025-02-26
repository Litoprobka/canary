module Syntax (module Export) where

-- a re-export of all AST types for convenience

import Prelude ()

import Syntax.Core as Export (CorePattern, CoreTerm)
import Syntax.Declaration as Export (Constructor, Declaration, Declaration_, GadtConstructor)
import Syntax.Row as Export (Row)
import Syntax.Term as Export (Binding, DoStatement, DoStatement_, Expr, Expr_, Pattern, Term, Term_, Type, VarBinder)
