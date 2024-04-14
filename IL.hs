module IL where

import Relude

-- the AST and pretty printer of HVM-Lang

type Name = Text
type Pattern = Void -- todo

data Term
    = Lambda Name Term
    | ScopelessLambda Name Term
    | Var Name
    | ScopelessVar Name
    | Application Term [Term]
    | Let Pattern Term Term
    | Use Pattern Name Term
    | Match Name Term [(Pattern, Term)]
    | Switch Name Term [(Maybe Int, Term)]
    | List [Term]
    | Tuple (Term, Term)
    | Char Char
    | U60 Int
    | String Text