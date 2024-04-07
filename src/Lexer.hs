{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Lexer (Parser, Token (..), tokens, lambda, keyword, specialSymbol, identifier, typeVariable, newline, strictNewline, intLiteral, textLiteral, charLiteral, operator) where

import Data.Char (isSpace)
import Relude hiding (many, some)
import TH (matches)
import Text.Megaparsec hiding (Token, token, tokens)
import Text.Megaparsec.Char hiding (newline, space)
import Text.Megaparsec.Char.Lexer qualified as L

type Lexer = StateT Int (Parsec Void Text)
type Parser = Parsec Void [Token]

data Token
    = Lambda -- special-cased, since \ is an operator symbol and λ is an identifier symbol
    | Keyword Text
    | SpecialSymbol Text
    | Identifier Text
    | TypeVariable Text -- an identifier starting with ', i.e. 't
    | Newline Pos Int -- newline with indent difference
    | IntLiteral Int
    | TextLiteral Text
    | CharLiteral Text -- TODO: support grapheme clusters (hence the use of Text instead of Char)
    | Operator Text
    deriving (Show, Eq, Ord)

space :: Lexer ()
space = L.space nonNewlineSpace lineComment blockComment
  where
    nonNewlineSpace = void $ takeWhile1P (Just "space") \c -> isSpace c && c /= '\n' -- we can ignore \r here
    lineComment = L.skipLineComment "//"
    blockComment = L.skipBlockCommentNested "/*" "*/"

lexeme :: Lexer a -> Lexer a
lexeme = L.lexeme space

symbol :: Text -> Lexer Text
symbol = L.symbol space

token :: Lexer Token
token =
    choice
        [ Lambda <$ lexeme (oneOf ['\\', 'λ'])
        , Keyword <$> oneSymbolOf keywords
        , SpecialSymbol <$> oneSymbolOf specialSymbols
        , Identifier <$> identifier
        , TypeVariable <$> typeVariable
        , newline
        , intLiteral
        , textLiteral
        , charLiteral
        , operator
        ]
  where
    oneSymbolOf txts = choice $ symbol <$> txts

    keywords :: [Text]
    keywords = ["where"]

    specialSymbols :: [Text]
    specialSymbols = ["=", ":", ".", "(", ")"]

    identifier :: Lexer Text
    identifier = lexeme $ fromString <$> liftA2 (:) letterChar (many alphaNumChar)

    typeVariable :: Lexer Text
    typeVariable = single '\'' *> identifier

    newline :: Lexer Token
    newline = do
        void $ lexeme eol
        prevIndent <- get :: Lexer Int
        curIndent <- L.indentLevel
        put $ unPos curIndent
        pure $ Newline curIndent (unPos curIndent - prevIndent)

    intLiteral :: Lexer Token
    intLiteral = lexeme $ IntLiteral <$> L.signed empty L.decimal

    -- todo: handle escape sequences and interpolation
    textLiteral :: Lexer Token
    textLiteral = TextLiteral . fromString <$> between (symbol "\"") (symbol "\"") (many letterChar)

    charLiteral :: Lexer Token
    charLiteral = CharLiteral . one <$> between (symbol "'") (symbol "'") letterChar

    operator :: Lexer Token
    operator = lexeme $ Operator . fromString <$> some (oneOf operatorChars)

    operatorChars :: [Char]
    operatorChars = "+-*/%^=><&.~!?|"

tokens :: Parsec Void Text [Token]
tokens = evaluatingStateT 1 $ many token -- TODO: better tokeniser errors; consider outputting an `Unexpected` token instead?

lambda :: Parser ()
lambda = void $ satisfy (== Lambda)

keyword, specialSymbol, identifier, typeVariable, textLiteral, charLiteral, operator :: Parser Text
keyword = $(matches 'Keyword)
specialSymbol = $(matches 'SpecialSymbol)
identifier = $(matches 'Identifier)
typeVariable = $(matches 'TypeVariable)
textLiteral = $(matches 'TextLiteral)
charLiteral = $(matches 'CharLiteral)
operator = $(matches 'Operator)

intLiteral :: Parser Int
intLiteral = $(matches 'IntLiteral)

newline :: Parser (Pos, Int)
newline =
    anySingle >>= \case
        Newline pos offset -> pure (pos, offset)
        tok -> unexpected $ Tokens $ tok :| []

strictNewline :: Parser ()
strictNewline = do
    (_, offset) <- newline
    guard $ offset >= 0
