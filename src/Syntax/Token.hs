{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TemplateHaskellQuotes #-}

module Syntax.Token where

import Common (Literal_)
import Data.Char (isAlphaNum)
import LangPrelude
import Language.Haskell.TH.Syntax (Exp, Lift, Q)
import Prelude qualified

data Token
    = LowerName Text
    | UpperName Text
    | VariantName Text
    | ImplicitName Text
    | Wildcard Text
    | Keyword Keyword
    | BlockStart BlockKeyword
    | BlockEnd
    | SpecialSymbol SpecialSymbol
    | Op Text
    | Literal Literal_
    | LParen
    | RParen
    | LBrace
    | RBrace
    | LBracket
    | RBracket
    | Comma
    | Semicolon
    | Newline
    deriving (Eq, Ord)

-- 'above', 'below', 'equals' and 'application' are conditional keywords - that is, they are allowed to be used as identifiers
data Keyword = If | Then | Else | Type | Case | Let | Forall | Foreach | Exists | Some | With | Infix
    deriving (Eq, Ord, Enum, Bounded, Lift)

data BlockKeyword = Match | Of | Where | Do | Rec
    deriving (Eq, Ord, Enum, Bounded, Lift)

instance Show Keyword where
    show = \case
        If -> "if"
        Then -> "then"
        Else -> "else"
        Type -> "type"
        Case -> "case"
        Let -> "let"
        Forall -> "forall"
        Foreach -> "foreach"
        Exists -> "exists"
        Some -> "some"
        With -> "with"
        Infix -> "infix"

instance Show BlockKeyword where
    show = \case
        Match -> "match"
        Of -> "of"
        Where -> "where"
        Do -> "do"
        Rec -> "rec"

data SpecialSymbol = Eq | Bar | Colon | Dot | Lambda | Arrow | FatArrow | BackArrow | At | Tilde | DepPair
    deriving (Eq, Ord, Enum, Bounded, Lift)

instance Show SpecialSymbol where
    show = \case
        Eq -> "="
        Bar -> "|"
        Colon -> ":"
        Dot -> "."
        Lambda -> "λ"
        Arrow -> "->"
        FatArrow -> "=>"
        BackArrow -> "<-"
        At -> "@"
        Tilde -> "~"
        DepPair -> "**"

isOperatorChar :: Char -> Bool
isOperatorChar = (`elem` ("+-*/%^=><&.~!?|@#$:" :: String))

isIdentifierChar :: Char -> Bool
isIdentifierChar c = isAlphaNum c || c == '_' || c == '\''

-- make a switch table out of a datatype to use with `rawSwitchPost`
-- ideally, this would be put in the Lexer module, but it had to be
-- moved out because of the staging restriction
parseTable :: forall a. (Show a, Lift a, Bounded a, Enum a) => [(String, Q Exp)]
parseTable = map (\x -> (show x, [|pure x|])) (universe @a)
