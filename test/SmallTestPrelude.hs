{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-missing-methods #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module SmallTestPrelude where

import Data.Char (isUpperCase)
import Relude hiding (Type)
import SmallChecker

-- yes, this would have been absolutely awful in the actual code,
-- but it's fine for tests

matchCase :: (Text -> a) -> (Text -> a) -> String -> a
matchCase whenUpper whenLower str@(h : _)
    | isUpperCase h = whenUpper $ fromString str
    | otherwise = whenLower $ fromString str

instance IsString Name where
    fromString ('\'' : rest) = flip Name 0 $ fromString rest
    fromString str = str & matchCase (flip Name 0) (error "IsString Name should only be used for type variables and constructor patterns")

instance IsString Expr where
    -- fromString ('\'' : rest) = rest & matchCase (E.Variant . ("'" <>)) (error "type variable at value level")
    fromString = matchCase (ECon . flip Name 0) (EName . flip Name 0)

instance IsString Pattern where
    fromString = matchCase (error "use explicit PCon for constructor patterns") (PVar . flip Name 0)

instance IsString Type where
    fromString ('\'' : str) = TVar . flip Name 0 $ fromString str
    fromString str = str & matchCase (TName . flip Name 0) (TName . flip Name 0)
