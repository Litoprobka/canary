{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-missing-methods #-}
module SmallTestPrelude where

import Relude hiding (Type)
import Syntax
import SmallChecker
import Data.Char (isUpperCase)

-- yes, this would have been absolutely awful in the actual code,
-- but it's fine for tests

matchCase :: (Text -> a) -> (Text -> a) -> String -> a
matchCase whenUpper whenLower str@(h:_)
    | isUpperCase h = whenUpper $ fromString str
    | otherwise = whenLower $ fromString str

instance IsString Expr where
    --fromString ('\'' : rest) = rest & matchCase (E.Variant . ("'" <>)) (error "type variable at value level")
    fromString str = str & matchCase (ECon . flip Name 0) (EName . flip Name 0)

instance IsString Type where
    fromString ('\'' : str) = TVar . flip Name 0 $ fromString str
    fromString str = str & matchCase (TName . flip Name 0) (TName . flip Name 0)

