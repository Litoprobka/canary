{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-missing-methods #-}
module TestPrelude (module Syntax) where

import Relude
import Syntax hiding (Name)
import Syntax.Expression qualified as E
import Syntax.Pattern qualified as P
import Syntax.Type qualified as T
import CheckerTypes
import Data.Char (isUpperCase)

-- yes, this would have been absolutely awful in the actual code,
-- but it's fine for tests

matchCase :: (Text -> a) -> (Text -> a) -> String -> a
matchCase whenUpper whenLower str@(h:_)
    | isUpperCase h = whenUpper $ fromString str
    | otherwise = whenLower $ fromString str

instance IsString (Expression Text) where
    fromString ('\'' : rest) = rest & matchCase (E.Variant . ("'" <>)) (error $ "type variable " <> fromString rest <> " at value level")
    fromString str = str & matchCase E.Constructor E.Name

instance IsString (Pattern Text) where
    fromString = matchCase (`P.Constructor` []) P.Var

instance IsString (Type' Text) where
    fromString ('\'' : str) = T.Var $ fromString str -- I'm not sure whether the quote should be a part of a type var
    fromString str = str & matchCase T.Name (error $ "type name " <> fromString str <> " shouldn't start with a lowercase letter")

instance IsString Name where
    fromString ('\'' : rest) = flip Name 0 $ fromString rest
    fromString str = Name (fromString str) 0

instance IsString (Expression Name) where
    fromString ('\'' : rest) = rest & matchCase (E.Variant . ("'" <>)) (error $ "type variable " <> fromString rest <> " at value level")
    fromString str = str & matchCase (E.Constructor . flip Name 0) (E.Name . flip Name 0)

instance IsString (Pattern Name) where
    fromString = matchCase (flip P.Constructor [] . flip Name 0) (P.Var . flip Name 0)

instance IsString (Type' Name) where
    fromString ('\'' : str) = T.Var . flip Name 0 $ fromString str
    fromString str = str & matchCase (T.Name . flip Name 0) (error $ "type name " <> fromString str <> " shouldn't start with a lowercase letter")