{-# LANGUAGE ApplicativeDo #-}
{-# OPTIONS_GHC -Wno-partial-fields #-}

module Syntax.Elaborated where

import Common hiding (Name)
import Data.Row
import LangPrelude
import Syntax.Core (CoreTerm, CoreType)
import Syntax.Term (Visibility)

{-x
The elaborated AST is halfway between core and pre-typecheck passes
-}

infix 3 :::
data Typed a = a ::: CoreType deriving (Show)

unTyped :: Typed a -> a
unTyped (x ::: _) = x

data EPattern
    = VarP SimpleName_
    | WildcardP Text
    | ConstructorP Name_ [(Visibility, EPattern)]
    | TypeP Name_ [(Visibility, EPattern)]
    | VariantP OpenName EPattern
    | RecordP (Vector (OpenName, EPattern))
    | SigmaP Visibility EPattern EPattern
    | ListP [EPattern]
    | LiteralP Literal
    deriving (Show)

data EDeclaration
    = ValueD Name_ CoreTerm -- no local bindings for now
    -- I'm not sure which representation for typechecked constructors makes more sense, this is the bare minimum
    | TypeD Name_ [(Name_, Vector (Visibility, CoreType))]
    | SignatureD Name_ CoreType

instance HasLoc a => HasLoc (Typed a) where
    getLoc (x ::: _) = getLoc x

-- | How many new variables does a pattern bind?
patternArity :: EPattern -> Int
patternArity = go
  where
    go = \case
        VarP{} -> 1
        WildcardP{} -> 1 -- further types may still depend on the value of a wildcard, so it is treated as a variable here
        ConstructorP _ args -> sum (map (go . snd) args)
        TypeP _ args -> sum (map (go . snd) args)
        VariantP _ arg -> go arg
        RecordP row -> sum (fmap (go . snd) row)
        SigmaP _ lhs rhs -> go lhs + go rhs
        ListP args -> sum (map go args)
        LiteralP{} -> 0
