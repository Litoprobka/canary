module Syntax (module Export) where

-- a re-export of all AST types for convenience

import Prelude ()

import Syntax.Core as Export (CorePattern, CoreTerm, CoreType, Pruning (..), ReversedPruning (..))
import Syntax.Declaration as Export (Constructor, Declaration, Declaration_, GadtConstructor)
import Syntax.Elaborated as Export (EDeclaration, EPattern, ETerm, EType, Typed (..))
import Syntax.Row as Export (Row)
import Syntax.Term as Export (
    Binding,
    DoStatement,
    DoStatement_,
    Erasure (..),
    Expr,
    Expr_,
    Pattern,
    Quantifier (..),
    Term,
    Term_,
    Type,
    VarBinder,
    Visibility (..),
 )
import Syntax.Value as Export (VType, Value, ValueEnv)
