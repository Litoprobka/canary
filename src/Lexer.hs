{-# LANGUAGE TemplateHaskell #-}
{-# HLINT ignore "Use <$>" #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module Lexer where

import Common (Literal_ (..), Loc (..), Located (..), SimpleName, SimpleName_ (..), locFromSourcePos, unLoc, pattern L)
import Control.Monad.Combinators.NonEmpty qualified as NE
import Data.Char (isLetter, isSpace, isUpperCase)
import Data.Text qualified as Text
import Data.Vector (Vector)
import Data.Vector qualified as V
import LangPrelude hiding (optional)
import Relude.Monad (ask, local)

-- import Text.Megaparsec hiding (Token, token)
import Text.Megaparsec qualified as MP

-- import Text.Megaparsec.Char hiding (newline, space)

import Control.Monad.Combinators (between, choice, skipManyTill)
import FlatParse.Basic hiding (Parser, Pos, try, (<|>))
import FlatParse.Basic qualified as FP
import Syntax.Token
import Text.Megaparsec.Char.Lexer qualified as L

type Parser = ReaderT MP.Pos (MP.Parsec Void TokenStream)
type Lexer = FP.Parser ()

data TokenStream = TokenStream Text (Vector (Located Token))

instance MP.Stream TokenStream where
    type Token TokenStream = Token
    type Tokens TokenStream = Vector Token

    tokensToChunk _ = V.fromList
    chunkToTokens _ = V.toList
    chunkLength _ = length
    chunkEmpty _ = null
    take1_ (TokenStream inp v) =
        V.uncons v <&> \(L tok, v') ->
            (tok, TokenStream inp v')
    takeN_ n (TokenStream inp v)
        | V.null v = Nothing
        | otherwise =
            let (toks, v') = V.splitAt n v
             in Just (fmap unLoc toks, TokenStream inp v')
    takeWhile_ p (TokenStream inp v) =
        let (toks, v') = V.span (p . unLoc) v
         in (fmap unLoc toks, TokenStream inp v')

token' :: Lexer Token
token' =
    choice
        [ Newline <$ $(char '\n')
        , Whitespace <$ space'
        , Keyword <$> keyword'
        , $( switch
                [|
                    case _ of
                        "∀" -> pure $ Keyword Forall
                        "Π" -> pure $ Keyword Foreach -- todo: probably needs a notFollowedBy check
                        "∃" -> pure $ Keyword Exists
                        "Σ" -> pure $ Keyword Some
                        "\\" -> pure $ SpecialSymbol Lambda
                        "(" -> pure LParen
                        ")" -> pure RParen
                        "{" -> pure LBrace
                        "}" -> pure RBrace
                        "[" -> pure LBracket
                        "]" -> pure RBracket
                        "," -> pure Comma
                        ";" -> pure Semicolon
                    |]
           )
        , identifier'
        , quotedIdent
        , SpecialSymbol <$> specialSymbol'
        , operator'
        , Literal <$> literal
        ]
  where
    -- it might be cleaner to parse an identifier and then check whether it's a keyword
    keyword' =
        $(rawSwitchWithPost (Just [|fails (satisfy isIdentifierChar)|]) (parseTable @Keyword) Nothing)
    specialSymbol' =
        $(rawSwitchWithPost (Just [|fails (satisfy isOperatorChar)|]) (parseTable @SpecialSymbol) Nothing)
    -- todo: should operators in parens be identifiers?
    identifier' = do
        firstChar <- satisfy isLetter <|> ('_' <$ $(char '_'))
        ident <- Text.pack . (firstChar :) <$> many (satisfy isIdentifierChar)
        pure case firstChar of
            '_' -> Wildcard ident
            c | isUpperCase c -> UpperName ident
            _ -> LowerName ident
    quotedIdent = do
        $(char '\'')
        ident <- Text.pack . ('\'' :) <$> some (satisfy isIdentifierChar)
        pure case Text.head ident of
            c | isUpperCase c -> VariantName ident
            _ -> ImplicitName ident
    operator' = Op . Text.pack <$> some (satisfy isOperatorChar)
    space' =
        choice
            [ skipSome (satisfy isSpace)
            , $(string "---") <* skipAnyChar `skipManyTill` $(string "---")
            , $(string "--") <* takeLine
            ]

token :: Token -> Parser ()
token = void . lexeme . MP.single

{- | any non-zero amount of newlines and any amount of whitespace
  i.e. it skips lines of whitespace entirely
  should never be used outside of the block-parsing functions
-}
newlines :: Parser ()
newlines = MP.skipMany $ token Newline

-- | space or a newline with increased indentation
spaceOrLineWrap :: Parser ()
spaceOrLineWrap = void $ MP.single Whitespace `MP.sepBy` newlineWithIndent
  where
    newlineWithIndent = MP.try do
        baseIndent <- ask
        void $ L.indentGuard newlines GT baseIndent

{- | parses a statement separator
a \\n should have the same indent as previous blocks. A semicolon always works
-}
newline :: Parser ()
newline = MP.label "separator" $ token Semicolon <|> eqIndent
  where
    eqIndent = MP.try do
        indent <- ask
        void $ L.indentGuard newlines EQ indent

lexeme :: Parser a -> Parser a
lexeme = L.lexeme spaceOrLineWrap

-- | a helper for `block` and `block1`.
block'
    :: (forall b. Parser a -> Parser b -> Parser out)
    -- ^ `sep` parser. Intended uses are `sepEndBy` and `sepEndBy1`
    -> Keyword
    -- ^ keyword
    -> Parser a
    -- ^ statement parser
    -> Parser out
block' sep kw p = do
    keyword kw

    -- make sure that the block is indented at all
    -- prevents stuff like:
    -- > f x = expr where
    -- > expr = x + x
    -- that being said, the check wouldn't make sense if we also use `block` for
    -- top-level blocks
    --
    -- note that the preceding whitespace is already consumed by `keyword`
    void $ ask >>= L.indentGuard pass GT

    blockIndent <- L.indentLevel
    local (const blockIndent) (p `sep` newline)

block :: Keyword -> Parser a -> Parser [a]
block = block' MP.sepEndBy

block1 :: Keyword -> Parser a -> Parser (NonEmpty a)
block1 = block' NE.sepEndBy1

{- | a newline-delimited expression
> let x = y
> z
-}
letBlock :: Keyword -> (a -> b -> c) -> Parser a -> Parser b -> Parser c
letBlock kw f declaration expression = do
    blockIndent <- L.indentLevel
    keyword kw
    dec <- declaration
    local (const blockIndent) do
        newline
        f dec <$> expression

letRecBlock :: Parser () -> (NonEmpty a -> b -> c) -> Parser a -> Parser b -> Parser c
letRecBlock kw f declaration expression = do
    outerIndent <- L.indentLevel
    kw
    innerIndent <- L.indentLevel
    decls <- local (const innerIndent) do
        declaration `NE.sepBy1` newline
    local (const outerIndent) do
        newline
        f decls <$> expression

topLevelBlock :: Parser a -> Parser [a]
topLevelBlock p = MP.optional newlines *> L.nonIndented spaceOrLineWrap (p `MP.sepEndBy` newline <* MP.eof)

-- | intended to be called with one of `specialSymbols`
specialSymbol :: SpecialSymbol -> Parser ()
specialSymbol = token . SpecialSymbol

-- | an alias for `token`. Intended to be used with commmas, parens, brackets and braces (i.e. punctuation that can't be used in operators)
punctuation :: Token -> Parser ()
punctuation = token

{- | parses a keyword, i.e. a symbol not followed by an alphanum character
it is assumed that `kw` appears in the `keywords` list
-}
keyword :: Keyword -> Parser ()
keyword = token . Keyword

-- | an identifier that doesn't start with an uppercase letter
termName' :: Parser Text
termName' = lexeme do
    LowerName name <- MP.anySingle
    pure name

-- | an identifier that doesn't start with an uppercase letter or a parenthesised operator
termName :: Parser SimpleName
termName = parens operator <|> mkName termName'

-- | a termName that starts with an underscore
wildcard :: Parser ()
wildcard = lexeme do
    Wildcard _ <- MP.anySingle
    pass

{- | an identifier that starts with an uppercase letter
this is not a lexeme
-}
typeName' :: Parser Text
typeName' = do
    UpperName name <- MP.anySingle
    pure name

{- | an identifier that starts with an uppercase letter
unlike `typeName'`, this /is/ a lexeme
-}
typeName :: Parser SimpleName
typeName = lexeme $ mkName typeName'

{- | a value constructor name
this is not a lexeme
-}
constructorName :: Parser SimpleName
constructorName = mkName typeName'

-- | an identifier that starts with a ' and a lowercase letter, i.e. 'acc
implicitVariable :: Parser SimpleName
implicitVariable = lexeme $ mkName do
    ImplicitName name <- MP.anySingle
    pure name

{- | an identifier that starts with a ' and an uppercase letter, i.e. 'Some
this is not a lexeme
-}
variantConstructor :: Parser SimpleName
variantConstructor = mkName do
    VariantName name <- MP.anySingle
    pure name

{- | a helper for other identifier parsers
note that it's not a lexeme, i.e. it doesn't consume trailing whitespace
-}
identifier :: Parser Text
identifier = do
    ident <- MP.anySingle
    case ident of
        UpperName name -> pure name
        LowerName name -> pure name
        _ -> fail "expected an identifier"

{- | a record lens, i.e. .field.otherField.thirdField
Chances are, this parser will only ever be used with E.RecordLens
-}

-- recordLens :: Parser (NonEmpty SimpleName)
-- recordLens = label "record lens" $ lexeme $ single '.' *> mkName identifier `NE.sepBy1` single '.'

-- for anybody wondering, `empty` is *not* a noop parser
intLiteral :: Lexer Literal_
intLiteral = IntLiteral <$> anyAsciiDecimalInt

-- todo: handle escape sequences and interpolation
textLiteral :: Lexer Literal_
textLiteral = fmap (TextLiteral . Text.pack) $ between $(char '\'') $(char '\'') $ many (satisfy (/= '"'))

{-
textLiteral' :: Lexer Literal
textLiteral' = located do
    void $ single '"'
    void $ many (Left <$> interp <|> Right <$> normalText)
    void $ single '"'
    pure $ TextLiteral ""
  where
    normalText = takeWhileP (Just "text literal body") (\c -> c `notElem` ['"', '$'])
    interp = do
        void $ single "$"
        between (single "{") (single "}") $ many token
-}

charLiteral :: Lexer Literal_
charLiteral = CharLiteral . one <$> between $(char '\'') $(char '\'') anyChar

-- | any literal
literal' :: Lexer Literal_
literal' = choice [intLiteral, textLiteral, charLiteral]

literal :: Parser Literal_
literal = lexeme do
    Literal lit <- MP.anySingle
    pure lit

operator :: Parser SimpleName
operator = do
    Op op <- MP.anySingle
    mkName $ pure op

{-
someOperator :: Parser SimpleName
someOperator = lexeme $ mkName $ try do
    op <- takeWhile1P (Just "operator") isOperatorChar
    guard (not $ op `Set.member` specialSymbols)
    pure op
-}

-- (+), (<$>), etc.
-- operatorInParens :: Parser SimpleName
-- operatorInParens = try $ parens someOperator

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
parens, brackets, braces :: Parser a -> Parser a
parens = between (punctuation LParen) (punctuation RParen)
brackets = between (punctuation RBracket) (punctuation RBracket)
braces = between (punctuation LBrace) (punctuation RBrace)

-- leading commas, trailing commas, anything goes
commaSep :: Parser a -> Parser [a]
commaSep p = MP.optional (token Comma) *> p `MP.sepEndBy` punctuation ","

{- | parses an AST node with location info
todo: don't include trailing whitespace where possible
-}
withLoc :: Parser (Loc -> a) -> Parser a
withLoc p = do
    start <- getSourcePos
    f <- p
    end <- getSourcePos
    let loc = if start == end then Blank else locFromSourcePos start end
    pure $ f loc

withLoc' :: (Loc -> a -> b) -> Parser a -> Parser b
withLoc' f p = withLoc $ flip f <$> p

located :: Parser a -> Parser (Located a)
located p = withLoc $ flip Located <$> p

mkName :: Parser Text -> Parser SimpleName
mkName = located . fmap Name'
