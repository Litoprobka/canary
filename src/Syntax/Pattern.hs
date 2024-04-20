module Syntax.Pattern (Pattern (..)) where

import Relude

type OpenName = Text

data Pattern n
    = Var n
    | Constructor n [Pattern n]
    | Variant OpenName [Pattern n]
    | Record (HashMap OpenName (Pattern n))
    | List [Pattern n]
    | IntLiteral Int
    | TextLiteral Text
    | CharLiteral Text
    deriving (Show, Eq)