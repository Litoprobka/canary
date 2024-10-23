{-# LANGUAGE OverloadedRecordDot #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use <$>" #-}
module Lexer (
    Parser,
    ParserM,
    keywords,
    specialSymbols,
    block,
    block1,
    topLevelBlock,
    letBlock,
    lexeme,
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
    nonWildcardTerm,
    wildcard,
    forallKeyword,
    existsKeyword,
    withLoc,
    withLoc',
    mkName,
    constructorName,
) where

import Common (Loc (..), SimpleName (..), locFromSourcePos)
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
type ParserM m = (MonadParsec Void Text m, MonadReader Pos m, MonadFail m)

-- |  the usual space parser. Doesn't consume newlines
space :: ParserM m => m ()
space = L.space nonNewlineSpace lineComment blockComment

{- | any non-zero amount of newlines and any amount of whitespace
  i.e. it skips lines of whitespace entirely
  should never be used outside of the block-parsing functions
-}
newlines :: ParserM m => m ()
newlines = C.newline *> L.space C.space1 lineComment blockComment

-- helper functions for @space@ and @newlines@
-- they're not in a where block, because monomorphism restriction
nonNewlineSpace, lineComment, blockComment :: ParserM m => m ()
nonNewlineSpace = void $ takeWhile1P (Just "space") \c -> isSpace c && c /= '\n' -- we can ignore \r here
lineComment = L.skipLineComment "--"
blockComment = L.skipBlockCommentNested "---" "---"

-- | space or a newline with increased indentation
spaceOrLineWrap :: ParserM m => m ()
spaceOrLineWrap = void $ space `sepBy` newlineWithIndent
  where
    newlineWithIndent = try do
        baseIndent <- ask
        void $ L.indentGuard newlines GT baseIndent

{- | parses a statement separator
a \\n should have the same indent as previous blocks. A semicolon always works
-}
newline :: ParserM m => m ()
newline = label "separator" $ void (symbol ";") <|> eqIndent
  where
    eqIndent = try do
        indent <- ask
        void $ L.indentGuard newlines EQ indent

lexeme :: ParserM m => m a -> m a
lexeme = L.lexeme spaceOrLineWrap

symbol :: ParserM m => Text -> m Text
symbol = L.symbol spaceOrLineWrap

keywords :: HashSet Text
keywords = Set.fromList ["if", "then", "else", "type", "alias", "case", "where", "let", "match", "of", "forall", "∀", "exists", "∃"]

-- | punctuation that has a special meaningng, like keywords
specialSymbols :: [Text]
specialSymbols = ["=", "|", ":", ".", ",", "λ", "\\", "∀", "∃", "->", "=>", "<-", "(", ")", "{", "}"]

-- lambda, forall and exists all have an ASCII and a unicode version

lambda :: ParserM m => m ()
lambda = void $ symbol "\\" <|> symbol "λ" -- should we allow `λx -> expr` without a space after λ?

forallKeyword :: ParserM m => m ()
forallKeyword = keyword "forall" <|> void (symbol "∀")

existsKeyword :: ParserM m => m ()
existsKeyword = keyword "exists" <|> void (symbol "∃")

-- | a helper for `block` and `block1`.
block'
    :: ParserM m
    => (forall b. m a -> m b -> m out)
    -- ^ `sep` parser. Intended uses are `sepEndBy` and `sepEndBy1`
    -> Text
    -- ^ keyword
    -> m a
    -- ^ statement parser
    -> m out
block' sep kw p = do
    keyword kw

    -- make sure that the block is indented at all
    -- prevents stuff like:
    -- > f x = expr where
    -- > expr = x + x
    -- that being said, the check wouldn't make sense if also use `block` for
    -- top-level blocks
    --
    -- note that the preceding whitespace is already consumed by `keyword`
    void $ ask >>= L.indentGuard pass GT

    blockIndent <- L.indentLevel
    local (const blockIndent) (p `sep` newline)

block :: ParserM m => Text -> m a -> m [a]
block = block' sepEndBy

block1 :: ParserM m => Text -> m a -> m (NonEmpty a)
block1 = block' NE.sepEndBy1

{- | a newline-delimited expression
> let x = y
> z
-}
letBlock :: ParserM m => Text -> (a -> b -> c) -> m a -> m b -> m c
letBlock kw f declaration expression = do
    blockIndent <- L.indentLevel
    keyword kw
    dec <- declaration
    local (const blockIndent) do
        newline
        f dec <$> expression

topLevelBlock :: Parser a -> Parser [a]
topLevelBlock p = newlines *> L.nonIndented spaceOrLineWrap (p `sepEndBy` newline <* eof)

-- | intended to be called with one of `specialSymbols`
specialSymbol :: ParserM m => Text -> m ()
specialSymbol sym = label (toString sym) $ try $ lexeme $ string sym *> notFollowedBy (satisfy isOperatorChar) -- note that `symbol` isn't used here, since the whitespace matters in this case

-- | parses a keyword, i.e. a symbol not followed by an alphanum character
-- it is assumed that `kw` appears in the `keywords` list
keyword :: ParserM m => Text -> m ()
keyword kw = label (toString kw) $ try $ lexeme $ string kw *> notFollowedBy (satisfy isIdentifierChar)

-- | an identifier that doesn't start with an uppercase letter
termName' :: ParserM m => m Text
termName' = do
    void $ lookAhead (satisfy $ not . isUpperCase)
    lexeme identifier

termName :: ParserM m => m SimpleName
termName = mkName termName'

-- | a term name that doesn't start with an underscore
nonWildcardTerm :: ParserM m => m SimpleName
nonWildcardTerm =
    choice
        [ lookAhead (anySingleBut '_') *> termName
        , wildcard *> fail "unexpected wildcard"
        ]

-- | a termName that starts with an underscore
-- note: the current implementation forbids `_1`, `_1abc`, etc. That may be undesired
wildcard :: ParserM m => m SimpleName
wildcard = lexeme $ mkName $ Text.cons <$> single '_' <*> option "" identifier

-- | an identifier that starts with an uppercase letter
-- this is not a lexeme
typeName' :: ParserM m => m Text
typeName' = do
    void $ lookAhead (satisfy isUpperCase)
    identifier

-- | an identifier that starts with an uppercase letter  
-- unlike `typeName'`, this /is/ a lexeme
typeName :: ParserM m => m SimpleName
typeName = lexeme $ mkName typeName'

-- | a value constructor name  
-- this is not a lexeme
constructorName :: ParserM m => m SimpleName
constructorName = mkName typeName'

-- | an identifier that starts with a ' and a lowercase letter, i.e. 'acc
typeVariable :: ParserM m => m SimpleName
typeVariable = try $ mkName $ liftA2 Text.cons (single '\'') termName'

-- | an identifier that starts with a ' and an uppercase letter, i.e. 'Some
-- this is not a lexeme
variantConstructor :: ParserM m => m SimpleName
variantConstructor = try $ mkName $ liftA2 Text.cons (single '\'') typeName'

-- | a helper for other identifier parsers  
-- note that it's not a lexeme, i.e. it doesn't consume trailing whitespace
identifier :: ParserM m => m Text
identifier = try do
    ident <- Text.cons <$> (letterChar <|> char '_') <*> takeWhileP (Just "identifier") isIdentifierChar
    when (ident `Set.member` keywords) (fail $ "unexpected keyword '" <> toString ident <> "'")
    pure ident

{- | a record lens, i.e. .field.otherField.thirdField
Chances are, this parser will only ever be used with E.RecordLens
-}
recordLens :: ParserM m => m (NonEmpty SimpleName)
recordLens = label "record lens" $ lexeme $ single '.' *> mkName identifier `NE.sepBy1` single '.'

-- for anybody wondering, `empty` is *not* a noop parser
intLiteral :: ParserM m => m Int
intLiteral = label "int literal" $ try $ lexeme $ L.signed pass L.decimal

-- todo: handle escape sequences and interpolation
textLiteral :: ParserM m => m Text
textLiteral = label "text literal" $ between (symbol "\"") (symbol "\"") $ takeWhileP (Just "text literal body") (/= '"')

charLiteral :: ParserM m => m Text
charLiteral = label "char literal" $ try $ one <$> between (single '\'') (symbol "'") anySingle

operator :: ParserM m => Text -> m Loc
operator sym = label "operator" $ lexeme $ withLoc' const $ string sym *> notFollowedBy (satisfy isOperatorChar)

someOperator :: ParserM m => m SimpleName
someOperator = lexeme $ mkName do
    op <- takeWhile1P (Just "operator") isOperatorChar
    guard (op `notElem` specialSymbols)
    pure op

isOperatorChar :: Char -> Bool
isOperatorChar = (`elem` ("+-*/%^=><&.~!?|" :: String))

isIdentifierChar :: Char -> Bool
isIdentifierChar c = isAlphaNum c || c == '_' || c == '\''

{- todo: it might be a good idea to ignore strict newlines when inside the brackets
i.e. that would allow
> stuff = [
>   x,
>   y,
>   z,
> ]
the indentation inside the list is optional as well  
using anythinging indentation-sensitve, i.e. do notation, reintroduces strict newlines
> otherStuff = [
>   x,
>   do
>     action1
>     action2,
>   y,   
> ]
-}
parens, brackets, braces :: ParserM m => m a -> m a
parens = between (specialSymbol "(") (specialSymbol ")")
brackets = between (specialSymbol "[") (specialSymbol "]")
braces = between (specialSymbol "{") (specialSymbol "}")

-- leading commas, trailing commas, anything goes
commaSep :: ParserM m => m a -> m [a]
commaSep p = optional (specialSymbol ",") *> p `sepEndBy` specialSymbol ","

-- | parses an AST node with location info
-- todo: don't include trailing whitespace where possible
withLoc :: ParserM m => m (Loc -> a) -> m a
withLoc p = do
    start <- getSourcePos
    f <- p
    end <- getSourcePos
    let loc = if start == end then Blank else locFromSourcePos start end
    pure $ f loc

withLoc' :: ParserM m => (Loc -> a -> b) -> m a -> m b
withLoc' f p = withLoc $ flip f <$> p

mkName :: ParserM m => m Text -> m SimpleName
mkName = withLoc' SimpleName