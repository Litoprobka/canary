{-# OPTIONS_GHC -Wno-partial-fields #-}

module Syntax.Elaborated where

import Common
import Data.Row
import LangPrelude
import Syntax.Core (CoreTerm)
import Syntax.Term (Erasure, Quantifier, Visibility)

{-x
The elaborated AST is halfway between core and pre-typecheck passes
-}

infix 3 :::
data Typed a = a ::: EType
type EType = ETerm

unTyped :: Typed a -> a
unTyped (x ::: _) = x

data ETerm
    = Var Index
    | Name Name -- top-level binding
    | Literal Literal
    | App Visibility ETerm ETerm
    | Lambda Visibility EPattern ETerm
    | Let EBinding ETerm
    | LetRec (NonEmpty EBinding) ETerm
    | Case ETerm [(EPattern, ETerm)]
    | Match [(NonEmpty (Typed EPattern), ETerm)]
    | If ETerm ETerm ETerm
    | Variant OpenName
    | Record (Row ETerm)
    | RecordAccess ETerm OpenName
    | List EType [ETerm]
    | Sigma ETerm ETerm
    | Do [EStatement] ETerm
    | Q Quantifier Visibility Erasure (Typed SimpleName_) ETerm
    | VariantT (ExtRow ETerm)
    | RecordT (ExtRow ETerm)
    | -- when inserting implicit applications, the inferred arg is usually already a CoreTerm
      -- the old solution was a 'resugar' function that transformed core term back into elaborated terms,
      -- but it makes more sense to just keep inserted core as is
      Core CoreTerm

data EPattern
    = VarP SimpleName_
    | WildcardP Text
    | ConstructorP Name [(Visibility, EPattern)]
    | VariantP OpenName EPattern
    | RecordP (Row EPattern)
    | SigmaP Visibility EPattern EPattern
    | ListP [EPattern]
    | LiteralP Literal

-- where should the type info be?
data EBinding
    = ValueB {name :: Name, body :: ETerm}
    | FunctionB {name :: Name, args :: NonEmpty (Visibility, EPattern), body :: ETerm}

data EStatement
    = Bind EPattern ETerm
    | With EPattern ETerm
    | DoLet EBinding
    | Action ETerm

data EDeclaration
    = ValueD EBinding -- no local bindings for now
    -- I'm not sure which representation for typechecked constructors makes more sense, this is the bare minimum
    | TypeD Name [(Name, Vector Visibility)]
    | SignatureD Name EType

instance HasLoc a => HasLoc (Typed a) where
    getLoc (x ::: _) = getLoc x

-- | How many new variables does a pattern bind?
patternArity :: EPattern -> Int
patternArity = go
  where
    go = \case
        VarP{} -> 1
        WildcardP{} -> 1 -- should it also be 0?
        ConstructorP _ args -> sum (map (go . snd) args)
        VariantP _ arg -> go arg
        RecordP row -> sum (fmap go row)
        SigmaP _ lhs rhs -> go lhs + go rhs
        ListP args -> sum (map go args)
        LiteralP{} -> 0
