{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE TemplateHaskellQuotes #-}

module Syntax.Token where

import Common (Literal, PrettyAnsi (..), UnAnnotate (..), prettyDef, pattern L)
import Data.Char (isAlphaNum)
import LangPrelude
import Language.Haskell.TH qualified as TH
import Language.Haskell.TH.Syntax (Exp, Lift, Q)
import Proto qualified
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
    | ColonOp Text
    | Literal Literal
    | LParen
    | RParen
    | TightLBrace -- a brace with no leading whitespace
    | LBrace
    | RBrace
    | LBracket
    | RBracket
    | Comma
    | Semicolon
    | Newline
    deriving (Eq, Ord)
    deriving (Pretty, Show) via (UnAnnotate Token)

instance PrettyAnsi Token where
    prettyAnsi = \case
        LowerName name -> pretty name
        UpperName name -> pretty name
        VariantName name -> pretty name
        ImplicitName name -> pretty name
        Wildcard text -> pretty text
        Keyword keyword -> pretty keyword
        BlockStart keyword -> pretty keyword
        BlockEnd -> "<end>"
        SpecialSymbol symbol -> pretty symbol
        Op operator -> pretty operator
        ColonOp operator -> pretty operator
        Literal literal -> prettyDef literal
        LParen -> "("
        RParen -> ")"
        TightLBrace -> "{"
        LBrace -> "{"
        RBrace -> "}"
        LBracket -> "["
        RBracket -> "]"
        Comma -> ","
        Semicolon -> ";"
        Newline -> "\\n"

-- 'above', 'below', 'equals' and 'application' are conditional keywords - that is, they are allowed to be used as identifiers
data Keyword = If | Then | Else | Type | Case | Let | Forall | Foreach | Exists | Some | With | Infix
    deriving (Eq, Ord, Enum, Bounded, Lift)

data BlockKeyword = Match | Of | Where | Do | Rec
    deriving (Eq, Ord, Enum, Bounded, Lift)

instance Show Keyword where
    show = show . pretty
instance Pretty Keyword where
    pretty = \case
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
    show = show . pretty
instance Pretty BlockKeyword where
    pretty = \case
        Match -> "match"
        Of -> "of"
        Where -> "where"
        Do -> "do"
        Rec -> "rec"

data SpecialSymbol = Eq | Bar | Colon | Dot | Lambda | Arrow | FatArrow | BackArrow | At | Tilde | DepPair
    deriving (Eq, Ord, Enum, Bounded, Lift)

instance Show SpecialSymbol where
    show = show . pretty
instance Pretty SpecialSymbol where
    pretty = \case
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

-- this also should have been in Lexer, but staging restriction

{- | matches a token pattern and returns its payload

tok :: Pattern (a -> Token) -> Parser a
-}
tok :: TH.Name -> TH.ExpQ
tok patName = do
    x <- TH.newName "x"
    [|
        do
            L $(TH.conP patName [TH.varP x]) <- Proto.anyToken
            pure $(TH.varE x)
        |]
