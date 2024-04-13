{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Lexer (Parser, Token (..), tokenise, lambda, keyword, specialSymbol, identifier, typeVariable, newline, intLiteral, textLiteral, charLiteral, operator) where

import Data.Char (isSpace)
import Data.List.NonEmpty qualified as NE
import Relude hiding (many, some)
import TH (matches)
import Text.Megaparsec hiding (Token, token)
import Text.Megaparsec.Char hiding (newline, space)
import Text.Megaparsec.Char qualified as C (newline)
import Text.Megaparsec.Char.Lexer qualified as L

newtype LexerState = LexerState {blocks :: NonEmpty Pos}

type Lexer = StateT LexerState (Parsec Void Text)
type Parser = Parsec Void [Token]

data Token
    = Lambda -- special-cased, since \ is an operator symbol and λ is an identifier symbol
    | BlockKeyword Text -- a keyword that starts a new indented block
    | BlockEnd
    | Keyword Text -- a keyword that doesn't
    | SpecialSymbol Text
    | Identifier Text
    | TypeVariable Text -- an identifier starting with ', i.e. 't
    | Newline
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

-- | any non-zero amount of newlines and any amount of whitespace
newlines :: Lexer ()
newlines = skipSome $ C.newline *> space

-- | space or a newline with increased indentation
spaceOrLineWrap :: Lexer ()
spaceOrLineWrap = void $ space `sepBy` newlineWithIndent
  where
    newlineWithIndent = try do
        baseIndent :| _ <- gets (.blocks)
        void $ L.indentGuard newlines GT baseIndent

lexeme :: Lexer a -> Lexer a
lexeme = L.lexeme spaceOrLineWrap

symbol :: Text -> Lexer Text
symbol = L.symbol spaceOrLineWrap

-- returns a single token or multiple BlockEnd-s. The other option would be to store multiple block ends as one `BlockEnd Int`, but that would make consuming them harder
token :: Lexer [Token]
token =
    newlineOrBlockEnd -- fourmolu is being dumb
        <|> one
        <$> choice
            [ Lambda <$ lexeme (oneOf ['\\', 'λ'])
            , blockKeyword
            , Keyword <$> oneSymbolOf keywords
            , SpecialSymbol <$> oneSymbolOf specialSymbols
            , Identifier <$> identifier
            , intLiteral
            , textLiteral
            , charLiteral
            , TypeVariable <$> typeVariable
            , operator
            ]
  where
    oneSymbolOf txts = choice $ symbol <$> txts

    blockKeywords :: [Text]
    blockKeywords = ["where"]

    blockKeyword :: Lexer Token
    blockKeyword = do
        kw <- oneSymbolOf blockKeywords
        -- `symbol` consumes the indent, so we get the right one here
        indent <- L.indentLevel
        LexerState{blocks} <- get
        put LexerState{blocks = indent `NE.cons` blocks}
        pure $ BlockKeyword kw

    keywords :: [Text]
    keywords = []

    specialSymbols :: [Text]
    specialSymbols = ["=", ":", ".", "(", ")"]

    identifier :: Lexer Text
    identifier = lexeme $ fromString <$> liftA2 (:) letterChar (many alphaNumChar)

    typeVariable :: Lexer Text
    typeVariable = single '\'' *> identifier

    -- if a newline hasn't been consumed by `spaceOrLineWrap`, then its indent level is the same or lower
    newlineOrBlockEnd :: Lexer [Token]
    newlineOrBlockEnd = one Newline <$ symbol ";" <|> blockEnd
      where
        blockEnd = do
            newlines
            indent <- L.indentLevel
            LexerState{blocks} <- get
            let higherThanCurrentIndent blockIndent = unPos blockIndent > unPos indent
            case NE.span higherThanCurrentIndent blocks of
                (toDrop, toKeep) -> do
                    put $ LexerState $ listToNE toKeep
                    pure $ replicate (length toDrop) BlockEnd ++ [Newline]
                  where
                    listToNE (x : xs) = x :| xs
                    listToNE [] = error "some pos is lower than pos1 (shouldn't be possible)"

    intLiteral :: Lexer Token
    intLiteral = try $ lexeme $ IntLiteral <$> L.signed empty L.decimal

    -- todo: handle escape sequences and interpolation
    textLiteral :: Lexer Token
    textLiteral = TextLiteral . fromString <$> between (symbol "\"") (symbol "\"") (many $ anySingleBut '\"')

    charLiteral :: Lexer Token
    charLiteral = CharLiteral . one <$> between (single '\'') (symbol "'") anySingle

    operator :: Lexer Token
    operator = lexeme $ Operator . fromString <$> some (oneOf operatorChars)

    operatorChars :: [Char]
    operatorChars = "+-*/%^=><&.~!?|"

tokenise :: Parsec Void Text [Token]
tokenise = evaluatingStateT (LexerState $ one pos1) $ concat <$> many token -- TODO: better tokeniser errors; consider outputting an `Unexpected` token instead?

lambda :: Parser ()
lambda = void $ single Lambda

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

newline :: Parser ()
newline = void $ single Newline
