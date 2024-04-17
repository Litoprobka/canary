{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-missing-methods #-}
module TestPrelude (module Syntax.All) where

import Relude
import Syntax.All
import Syntax.Term qualified as E
import Syntax.Pattern qualified as P
import Syntax.Type qualified as T
import Data.Char (isUpperCase)

-- yes, this would have been absolutely awful in the actual code,
-- but it's fine for tests

matchCase :: (Text -> a) -> (Text -> a) -> String -> a
matchCase whenUpper whenLower str@(h:_)
    | isUpperCase h = whenUpper $ fromString str
    | otherwise = whenLower $ fromString str

instance IsString Term where
    fromString ('\'' : rest) = rest & matchCase (E.Variant . ("'" <>)) (error "type variable at value level")
    fromString str = str & matchCase E.Constructor E.Name

instance IsString Pattern where
    fromString = matchCase (error "don't use IsString for constructors") P.Var

instance IsString Type' where
    fromString ('\'' : _) = error "todo: type variables"
    fromString str = str & matchCase T.Name (error "type names shouldn't start with a lowercase letter")

instance Num Term where
    fromInteger = E.IntLiteral . fromInteger
