module Syntax (module Export) where

-- a re-export of all AST types for convenience

import Prelude ()

import Syntax.Declaration as Export (Constructor, Declaration)
import Syntax.Expression as Export (Binding, Expression)
import Syntax.Pattern as Export (Pattern)
import Syntax.Row as Export (Row)
import Syntax.Type as Export (Type')
