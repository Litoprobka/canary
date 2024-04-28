module Lexer (
    Parser,
    keywords,
    specialSymbols,
    block,
    block1,
    topLevelBlock,
    letBlock,
    lambda,
    keyword,
    specialSymbol,
    intLiteral,
    textLiteral,
    charLiteral,
    operator,
    termName,
    typeName,
    typeVariable,
    variantConstructor,
    recordLens,
    parens,
    brackets,
    braces,
    commaSep,
    someOperator,
) where

import Control.Monad.Combinators.NonEmpty qualified as NE
import Data.Char (isAlphaNum, isSpace, isUpperCase)
import Data.HashSet qualified as Set
import Data.Text qualified as Text
import Relude hiding (many, some)
import Text.Megaparsec hiding (Token, token)
import Text.Megaparsec.Char hiding (newline, space)
import Text.Megaparsec.Char qualified as C (newline, space1)
import Text.Megaparsec.Char.Lexer qualified as L

type Parser = ReaderT Pos (Parsec Void Text)

-- |  the usual space parser. Doesn't consume newlines
space :: Parser ()

{- | any non-zero amount of newlines and any amount of whitespace
  i.e. it skips lines of whitespace entirely
  should never be used outside of the block-parsing functions
-}
newlines :: Parser ()
(space, newlines) = (L.space nonNewlineSpace lineComment blockComment, C.newline *> L.space C.space1 lineComment blockComment)
  where
    nonNewlineSpace = void $ takeWhile1P (Just "space") \c -> isSpace c && c /= '\n' -- we can ignore \r here
    lineComment = L.skipLineComment "//"
    blockComment = L.skipBlockCommentNested "/*" "*/"

-- | space or a newline with increased indentation
spaceOrLineWrap :: Parser ()
spaceOrLineWrap = void $ space `sepBy` newlineWithIndent
  where
    newlineWithIndent = try do
        baseIndent <- ask
        void $ L.indentGuard newlines GT baseIndent

{- | parses a statement separator
a \n should have the same indent as previous blocks. A semicolon always works
-}
newline :: Parser ()
newline = label "separator" $ void (symbol ";") <|> eqIndent
  where
    eqIndent :: Parser ()
    eqIndent = try do
        indent <- ask
        void $ L.indentGuard newlines EQ indent

lexeme :: Parser a -> Parser a
lexeme = L.lexeme spaceOrLineWrap

symbol :: Text -> Parser Text
symbol = L.symbol spaceOrLineWrap

keywords :: HashSet Text
keywords = Set.fromList ["if", "then", "else", "type", "alias", "case", "where", "let", "match", "of"]

specialSymbols :: [Text]
specialSymbols = ["=", "|", ":", ".", ",", "->", "=>", "<-", "(", ")", "{", "}"]

lambda :: Parser ()
lambda = void $ lexeme $ satisfy \c -> c == '\\' || c == 'λ'

-- | a helper for `block` and `block1`.
block'
    :: (forall b. Parser a -> Parser b -> Parser out)
    -> Text
    -- ^ keyword
    -- ^ `sep` parser. Intended uses are `sepEndBy` and `sepEndBy1`
    -> Parser a
    -- ^ statement parser
    -> Parser out
block' sep kw p = do
    keyword kw

    -- make sure that the block is indented at all
    -- prevents stuff like:
    -- > f x = expr where
    -- > expr = x + x
    -- note that the preceding whitespace is already consumed by `keyword`
    void $ ask >>= L.indentGuard pass GT

    blockIndent <- L.indentLevel
    local (const blockIndent) (p `sep` newline)

block :: Text -> Parser a -> Parser [a]
block = block' sepEndBy

block1 :: Text -> Parser a -> Parser (NonEmpty a)
block1 = block' NE.sepEndBy1

{- | a newline-delimited expression
> let x = y
> z
-}
letBlock :: Text -> (a -> b -> c) -> Parser a -> Parser b -> Parser c
letBlock kw f declaration expression = do
    blockIndent <- L.indentLevel
    keyword kw
    dec <- declaration
    local (const blockIndent) do
        newline
        f dec <$> expression

topLevelBlock :: Parser a -> Parser [a]
topLevelBlock p = L.nonIndented spaceOrLineWrap $ p `sepEndBy` newline <* eof

-- | intended to be called with one of `specialSymbols`
specialSymbol :: Text -> Parser ()
specialSymbol sym = try $ lexeme $ string sym *> notFollowedBy (satisfy isOperatorChar) -- note that `symbol` isn't used here, since the whitespace matters in this case

-- | parses a keyword, i.e. a symbol not followed by an alphanum character
keyword :: Text -> Parser ()
keyword kw = try $ lexeme $ string kw *> notFollowedBy (satisfy isIdentifierChar)

-- | an identifier that doesn't start with an uppercase letter
termName :: Parser Text
termName = try do
    ident <- identifier
    guard (not $ isUpperCase $ Text.head ident)
    pure ident

-- | an identifier that starts with an uppercase letter
typeName :: Parser Text
typeName = try do
    ident <- identifier
    guard (isUpperCase $ Text.head ident)
    pure ident

-- | an identifier that starts with a ' and a lowercase letter, i.e. 'acc
typeVariable :: Parser Text
typeVariable = try $ liftA2 Text.cons (single '\'') termName

-- an identifier that starts with a ' and an uppercase letter, i.e. 'Some
variantConstructor :: Parser Text
variantConstructor = try $ liftA2 Text.cons (single '\'') typeName

-- a helper for other identifier parsers
identifier :: Parser Text
identifier = try do
    ident <- lexeme $ Text.cons <$> (letterChar <|> char '_') <*> takeWhileP (Just "identifier") isIdentifierChar
    when (ident `Set.member` keywords) (fail "expected an identifier, got a keyword")
    pure ident

{- | a record lens, i.e. .field.otherField.thirdField
Chances are, this parser will only ever be used with T.RecordLens (I should rename Term to Expression)
-}
recordLens :: Parser (NonEmpty Text)
recordLens = lexeme $ single '.' *> identifier `NE.sepBy1` single '.'

intLiteral :: Parser Int
intLiteral = try $ lexeme $ L.signed empty L.decimal

-- todo: handle escape sequences and interpolation
textLiteral :: Parser Text
textLiteral = between (symbol "\"") (symbol "\"") $ takeWhileP (Just "text literal body") (/= '"')

charLiteral :: Parser Text
charLiteral = try $ one <$> between (single '\'') (symbol "'") anySingle

operator :: Text -> Parser ()
operator sym = lexeme $ string sym *> notFollowedBy (satisfy isOperatorChar)

someOperator :: Parser Text
someOperator = lexeme $ takeWhile1P (Just "operator") isOperatorChar

isOperatorChar :: Char -> Bool
isOperatorChar = (`elem` ("+-*/%^=><&.~!?|" :: String))

isIdentifierChar :: Char -> Bool
isIdentifierChar c = isAlphaNum c || c == '_' || c == '\''

parens, brackets, braces :: Parser a -> Parser a
parens = between (specialSymbol "(") (specialSymbol ")")
brackets = between (specialSymbol "[") (specialSymbol "]")
braces = between (specialSymbol "{") (specialSymbol "}")

commaSep :: Parser a -> Parser [a]
commaSep = (`sepEndBy` specialSymbol ",")