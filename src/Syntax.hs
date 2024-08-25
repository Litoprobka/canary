module Syntax (module Export, Name) where

-- a re-export of all AST types for convenience

import Relude

import Syntax.Declaration as Export (Declaration)
import Syntax.Pattern as Export (Pattern)
import Syntax.Expression as Export (Expression, Binding)
import Syntax.Type as Export (Type')
import Syntax.Row as Export (Row)

type Name = Text