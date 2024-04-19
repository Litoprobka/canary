module Syntax.Pattern (Name, Pattern (..)) where

import Relude

type Name = Text -- I'm not sure where put it

data Pattern
    = Var Name
    | Constructor Name [Pattern]
    | Variant Name [Pattern]
    | Record (HashMap Name Pattern)
    | List [Pattern]
    | IntLiteral Int
    | TextLiteral Text
    | CharLiteral Text
    deriving (Show, Eq)
