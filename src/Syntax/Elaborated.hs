{-# OPTIONS_GHC -Wno-partial-fields #-}

module Syntax.Elaborated where

import Common
import LangPrelude
import Syntax.Row
import Syntax.Term (Erasure, Quantifier, Visibility)
import Syntax.Value (Value)

{-
The elaborated AST is halfway between core and pre-typecheck passes
-}

infix 3 :::
data Typed a = a ::: ~Value

unTyped :: Typed a -> a
unTyped (x ::: _) = x

type ETerm = (Located ETerm_)

-- another thing I might want to add are big lambdas (or rather, implicit lambdas)
-- > id : forall a. a -> a
-- > id = Λa. λ(x : a). x
data ETerm_
    = Name Name
    | Literal Literal
    | App ETerm ETerm
    | Lambda (Typed EPattern) ETerm
    | Let EBinding ETerm
    | LetRec (NonEmpty EBinding) ETerm
    | Case ETerm [(EPattern, ETerm)]
    | Match [(NonEmpty (Typed EPattern), ETerm)]
    | If ETerm ETerm ETerm
    | Variant OpenName
    | Record (Row ETerm)
    | RecordAccess ETerm OpenName
    | List [ETerm]
    | Sigma ETerm ETerm
    | Do [EStatement] ETerm
    | Function ETerm ETerm
    | Q Quantifier Visibility Erasure Name Value ETerm
    | VariantT (ExtRow ETerm)
    | RecordT (ExtRow ETerm)

type EPattern = (Located EPattern_)
data EPattern_
    = VarP Name
    | WildcardP Text
    | ConstructorP Name [EPattern]
    | VariantP OpenName EPattern
    | RecordP (Row EPattern)
    | SigmaP EPattern EPattern
    | ListP [EPattern]
    | LiteralP Literal

-- where should the type info be?
data EBinding
    = ValueB {pat :: Typed EPattern, body :: ETerm}
    | FunctionB {name :: Name, args :: NonEmpty (Typed EPattern), body :: ETerm}

data EStatement
    = Bind EPattern ETerm
    | With EPattern ETerm
    | DoLet EBinding
    | Action ETerm

type EDeclaration = Located EDeclaration_
data EDeclaration_
    = ValueD EBinding -- no local bindings for now
    -- I'm not sure which representation for typechecked constructors makes more sense, this is the bare minimum
    | TypeD Name [(Name, Int)]
    | SignatureD Name Value

instance HasLoc a => HasLoc (Typed a) where
    getLoc (x ::: _) = getLoc x
