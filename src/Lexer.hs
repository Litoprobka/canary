{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Lexer (
    Parser,
    Token (..),
    tokenise,
    lambda,
    keyword,
    specialSymbol,
    newline,
    intLiteral,
    textLiteral,
    charLiteral,
    operator,
    blockEnd,
    someKeyword,
    someSpecial,
    termName,
    typeName,
    typeVariable,
    variantConstructor,
    blockKeyword,
    parens,
    brackets,
    braces,
    block,
    block1,
    recordLens,
) where

import Control.Monad.Combinators.NonEmpty qualified as NE
import Data.Char (isSpace, isUpperCase)
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
    | RecordLens [Text] -- a dot-separated list of identifiers that starts with a dot: `.field.anotherOne.x`
    | SpecialSymbol Text
    | LowerIdentifier Text -- an identifier that starts with a lowercase letter
    | UpperIdentifier Text -- an identifier that starts with an uppercase letter
    | LowerQuoted Text -- an identifier that starts with ' and an uppercase letter, i.e. 't
    | UpperQuoted Text -- an identifier that starts with ' and a lowercase letter, i.e. 'T
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
            , RecordLens <$> recordLens
            , SpecialSymbol <$> oneSymbolOf specialSymbols
            , identifier
            , intLiteral
            , textLiteral
            , charLiteral
            , quoted
            , operator
            ]
  where
    oneSymbolOf txts = choice $ symbol <$> txts

    blockKeywords :: [Text]
    blockKeywords = ["where", "let", "match", "of"]

    blockKeyword :: Lexer Token
    blockKeyword = do
        kw <- oneSymbolOf blockKeywords
        -- `symbol` consumes the indent, so we get the right one here
        indent <- L.indentLevel
        LexerState{blocks} <- get
        put LexerState{blocks = indent `NE.cons` blocks}
        pure $ BlockKeyword kw

    keywords :: [Text]
    keywords = ["if", "then", "else", "type", "alias", "case"]

    specialSymbols :: [Text]
    specialSymbols = ["=", "|", ":", ".", ",", "->", "=>", "<-", "(", ")", "{", "}"]

    identifier' :: Lexer (NonEmpty Char)
    identifier' = liftA2 (:|) (letterChar <|> char '_') (many $ alphaNumChar <|> char '_' <|> char '\'')

    nonEmptyToText :: NonEmpty Char -> Text
    nonEmptyToText = fromString . toList

    identifier :: Lexer Token
    identifier = lexeme do
        name@(c :| _) <- identifier'
        if isUpperCase c
            then pure $ UpperIdentifier $ nonEmptyToText name
            else pure $ LowerIdentifier $ nonEmptyToText name
    -- I didn't feel like factoring out the repeating part
    quoted :: Lexer Token
    quoted = lexeme do
        void $ single '\''
        name@(c :| _) <- identifier'
        if isUpperCase c
            then pure $ UpperQuoted $ nonEmptyToText name
            else pure $ LowerQuoted $ nonEmptyToText name

    recordLens :: Lexer [Text]
    recordLens = lexeme $ single '.' *> (nonEmptyToText <$> identifier') `sepBy` single '.'

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
tokenise = evaluatingStateT (LexerState $ one pos1) $ spaceOrLineWrap *> (concat <$> many token) -- TODO: better tokeniser errors; consider outputting an `Unexpected` token instead?

lambda :: Parser ()
lambda = void $ single Lambda

someKeyword
    , someSpecial
    , termName
    , typeVariable
    , typeName
    , variantConstructor
    , textLiteral
    , charLiteral
    , operator
        :: Parser Text
someKeyword = $(matches 'Keyword)
someSpecial = $(matches 'SpecialSymbol)
termName = $(matches 'LowerIdentifier)
typeName = $(matches 'UpperIdentifier)
typeVariable = $(matches 'LowerQuoted)
variantConstructor = $(matches 'UpperQuoted)
textLiteral = $(matches 'TextLiteral)
charLiteral = $(matches 'CharLiteral)
operator = $(matches 'Operator)

intLiteral :: Parser Int
intLiteral = $(matches 'IntLiteral)

recordLens :: Parser [Text]
recordLens = $(matches 'RecordLens)

newline :: Parser ()
newline = void $ single Newline

blockEnd :: Parser ()
blockEnd = void $ single BlockEnd

keyword :: Text -> Parser ()
keyword = void . single . Keyword

blockKeyword :: Text -> Parser ()
blockKeyword = void . single . BlockKeyword

specialSymbol :: Text -> Parser ()
specialSymbol = void . single . SpecialSymbol

parens, brackets, braces :: Parser a -> Parser a
parens = between (specialSymbol "(") (specialSymbol ")")
brackets = between (specialSymbol "[") (specialSymbol "]")
braces = between (specialSymbol "{") (specialSymbol "}")

block :: Text -> Parser a -> Parser [a]
block kw p = blockKeyword kw *> p `sepEndBy` newline <* blockEnd

block1 :: Text -> Parser a -> Parser (NonEmpty a)
block1 kw p = blockKeyword kw *> p `NE.sepEndBy1` newline <* blockEnd