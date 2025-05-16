{-# HLINT ignore "Use <$>" #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module Lexer where

import Common (Literal, Literal_ (..), Loc (..), Located (..), SimpleName, SimpleName_ (..), locFromSourcePos)
import Control.Monad.Combinators.NonEmpty qualified as NE
import Data.Char (isAlphaNum, isSpace, isUpperCase)
import Data.HashSet qualified as Set
import Data.Text qualified as Text
import Data.Vector (Vector)
import Data.Vector qualified as V
import LangPrelude
import Relude.Monad (ask, local)
import Text.Megaparsec hiding (Token, token)
import Text.Megaparsec qualified as MP (Stream (..))
import Text.Megaparsec.Char hiding (newline, space)
import Text.Megaparsec.Char qualified as C (newline, space1)
import Text.Megaparsec.Char.Lexer qualified as L
import Prelude qualified (show)

type Parser = Parsec Void Text
type Lexer = ReaderT Pos (Parsec Void Text)

data TokenStream = TokenStream Text (Vector (Loc, Token))

instance Stream TokenStream where
    type Token TokenStream = Token
    type Tokens TokenStream = Vector Token

    tokensToChunk _ = V.fromList
    chunkToTokens _ = V.toList
    chunkLength _ = length
    chunkEmpty _ = null
    take1_ (TokenStream inp v) =
        V.uncons v <&> \((_, tok), v') ->
            (tok, TokenStream inp v')
    takeN_ n (TokenStream inp v)
        | V.null v = Nothing
        | otherwise =
            let (toks, v') = V.splitAt n v
             in Just (fmap snd toks, TokenStream inp v')
    takeWhile_ p (TokenStream inp v) =
        let (toks, v') = V.span (p . snd) v
         in (fmap snd toks, TokenStream inp v')

data Token
    = LowerName Text
    | UpperName Text
    | Wildcard Text
    | Keyword Keyword
    | SpecialSymbol SpecialSymbol
    | Op Text
    | Literal Literal
    | LParen
    | RParen
    | LBrace
    | RBrace
    | LBracket
    | RBracket
    | Comma
    | Whitespace -- some constructs are whitespace-sensitive, so we have to track of the existence of whitespace
    | Newline
    | Indent -- there are multiple options: we can make the token parser return multiple tokens and continue parsing until a dedent
    | Outdent -- or we can just use State instead of Reader and store an indent stack
    -- option three is to insert meaningful indent/dedent/newline tokens after parsing
    deriving (Eq, Ord)

-- 'above', 'below', 'equals' and 'application' are conditional keywords - that is, they are allowed to be used as identifiers
data Keyword = If | Then | Else | Type | Case | Where | Let | Rec | Match | Of | Forall | Foreach | Exists | Some | Do | With | Infix
    deriving (Eq, Ord, Enum, Bounded)

instance Show Keyword where
    show = \case
        If -> "if"
        Then -> "then"
        Else -> "else"
        Type -> "type"
        Case -> "case"
        Where -> "where"
        Let -> "let"
        Rec -> "rec"
        Match -> "match"
        Of -> "of"
        Forall -> "forall"
        Foreach -> "foreach"
        Exists -> "exists"
        Some -> "some"
        Do -> "do"
        With -> "with"
        Infix -> "infix"

data SpecialSymbol = Eq | Bar | Colon | Dot | Lambda | Arrow | FatArrow | BackArrow | At | Tilde | DepPair
    deriving (Eq, Ord)

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

token :: Lexer Token
token =
    choice
        [ Whitespace <$ space
        , keyword'
        , altKeyword
        , identifier'
        , specialSymbol'
        , operator'
        , Literal <$> literal
        , LParen <$ symbol "("
        , RParen <$ symbol ")"
        , LBrace <$ symbol "{"
        , RBrace <$ symbol "}"
        , LBracket <$ symbol "["
        , RBracket <$ symbol "]"
        , Comma <$ symbol ","
        , Newline <$ newline
        , Indent <$ error "todo"
        , Outdent <$ error "todo"
        ]
  where
    -- it might be cleaner to parse an identifier and then check whether it's a keyword
    keyword' =
        choice $
            [minBound .. maxBound] <&> \kw ->
                Keyword kw <$ do
                    void $ string (show kw)
                    notFollowedBy (satisfy isIdentifierChar)
    altKeyword =
        choice
            [ Keyword Forall <$ symbol "∀"
            , Keyword Foreach <$ symbol "Π"
            , Keyword Exists <$ symbol "∃"
            , Keyword Some <$ symbol "Σ"
            , SpecialSymbol Lambda <$ symbol "\\"
            ]
    specialSymbol' =
        choice $
            [minBound .. maxBound] <&> \sym ->
                SpecialSymbol sym <$ do
                    void $ string (show sym)
                    notFollowedBy (satisfy isOperatorChar)
    -- todo: should operators in parens be identifiers?
    identifier' = do
        ident <- takeWhile1P (Just "identifier") isIdentifierChar
        pure case Text.head ident of
            '_' -> Wildcard ident
            c | isUpperCase c -> UpperName ident
            _ -> LowerName ident
    operator' = Op <$> takeWhile1P (Just "operator") isOperatorChar

-- |  the usual space parser. Doesn't consume newlines
space :: Lexer ()
space = L.space nonNewlineSpace lineComment blockComment

{- | any non-zero amount of newlines and any amount of whitespace
  i.e. it skips lines of whitespace entirely
  should never be used outside of the block-parsing functions
-}
newlines :: Lexer ()
newlines = C.newline *> L.space C.space1 lineComment blockComment

-- helper functions for @space@ and @newlines@
-- they're not in a where block, because monomorphism restriction
nonNewlineSpace, lineComment, blockComment :: Lexer ()
nonNewlineSpace = void $ takeWhile1P (Just "space") \c -> isSpace c && c /= '\n' -- we can ignore \r here
lineComment =
    try $
        string "--"
            *> notFollowedBy (satisfy isOperatorChar)
            *> void (takeWhileP (Just "character") (/= '\n'))
            *> void (optional newline)
blockComment = L.skipBlockComment "---" "---" -- this syntax doesn't work well with nested comments; it does look neat though

-- | space or a newline with increased indentation
spaceOrLineWrap :: Lexer ()
spaceOrLineWrap = void $ space `sepBy` newlineWithIndent
  where
    newlineWithIndent = try do
        baseIndent <- ask
        void $ L.indentGuard newlines GT baseIndent

{- | parses a statement separator
a \\n should have the same indent as previous blocks. A semicolon always works
-}
newline :: Lexer ()
newline = label "separator" $ void (symbol ";") <|> eqIndent
  where
    eqIndent = try do
        indent <- ask
        void $ L.indentGuard newlines EQ indent

lexeme :: Lexer a -> Lexer a
lexeme = L.lexeme spaceOrLineWrap

symbol :: Text -> Lexer Text
symbol = L.symbol spaceOrLineWrap

keywords :: HashSet Text
keywords =
    Set.fromList
        []

-- | punctuation that has a special meaning, like keywords
specialSymbols :: HashSet Text
specialSymbols = Set.fromList ["=", "|", ":", ".", "λ", "\\", "∀", "∃", "->", "=>", "<-", "@", "~", "**"]

-- lambda, forall and exists all have an ASCII and a unicode version

lambda :: Parser ()
lambda = void $ specialSymbol "\\" <|> specialSymbol "λ" -- should we allow `λx -> expr` without a space after λ?

forallKeyword :: Parser ()
forallKeyword = keyword "forall" <|> specialSymbol "∀"

piKeyword :: Parser ()
piKeyword = keyword "foreach" <|> specialSymbol "Π"

existsKeyword :: Parser ()
existsKeyword = keyword "exists" <|> specialSymbol "∃"

sigmaKeyword :: Parser ()
sigmaKeyword = keyword "some" <|> specialSymbol "Σ"

-- | a helper for `block` and `block1`.
block'
    :: (forall b. Parser a -> Parser b -> Parser out)
    -- ^ `sep` parser. Intended uses are `sepEndBy` and `sepEndBy1`
    -> Text
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
topLevelBlock p = optional newlines *> L.nonIndented spaceOrLineWrap (p `sepEndBy` newline <* eof)

-- | intended to be called with one of `specialSymbols`
specialSymbol :: Text -> Parser ()
specialSymbol sym = label (toString sym) $ try $ lexeme $ string sym *> notFollowedBy (satisfy isOperatorChar) -- note that `symbol` isn't used here, since the whitespace matters in this case

-- | an alias for `symbol`. Intended to be used with commmas, parens, brackets and braces (i.e. punctuation that can't be used in operators)
punctuation :: Text -> Parser ()
punctuation = void . symbol

{- | parses a keyword, i.e. a symbol not followed by an alphanum character
it is assumed that `kw` appears in the `keywords` list
-}
keyword :: Text -> Parser ()
keyword kw = label (toString kw) $ try $ lexeme $ string kw *> notFollowedBy (satisfy isIdentifierChar)

-- | an identifier that doesn't start with an uppercase letter
termName' :: Parser Text
termName' = do
    void $ lookAhead (satisfy $ not . isUpperCase)
    void $ lookAhead (anySingleBut '_') <|> fail "unexpected wildcard"
    lexeme identifier

-- | an identifier that doesn't start with an uppercase letter or a parenthesised operator
termName :: Parser SimpleName
termName = try (parens someOperator) <|> mkName termName'

{- | a termName that starts with an underscore
note: the current implementation forbids `_1`, `_1abc`, etc. That may be undesired
-}
wildcard :: Parser ()
wildcard = single '_' *> void identifier

{- | an identifier that starts with an uppercase letter
this is not a lexeme
-}
typeName' :: Parser Text
typeName' = do
    void $ lookAhead (satisfy isUpperCase)
    identifier

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
implicitVariable = try $ mkName $ liftA2 Text.cons (single '\'') termName'

{- | an identifier that starts with a ' and an uppercase letter, i.e. 'Some
this is not a lexeme
-}
variantConstructor :: Parser SimpleName
variantConstructor = try $ mkName $ liftA2 Text.cons (single '\'') typeName'

{- | a helper for other identifier parsers
note that it's not a lexeme, i.e. it doesn't consume trailing whitespace
-}
identifier :: Lexer Text
identifier = try do
    ident <- Text.cons <$> (letterChar <|> char '_') <*> takeWhileP (Just "identifier") isIdentifierChar
    when (ident `Set.member` keywords) (fail $ "unexpected keyword '" <> toString ident <> "'")
    pure ident

{- | a record lens, i.e. .field.otherField.thirdField
Chances are, this parser will only ever be used with E.RecordLens
-}
recordLens :: Lexer (NonEmpty SimpleName)
recordLens = label "record lens" $ lexeme $ single '.' *> mkName identifier `NE.sepBy1` single '.'

-- for anybody wondering, `empty` is *not* a noop parser
intLiteral :: Lexer Literal
intLiteral = label "int literal" $ try $ lexeme $ located $ fmap IntLiteral $ L.signed pass L.decimal

-- todo: handle escape sequences and interpolation
textLiteral :: Lexer Literal
textLiteral =
    label "text literal" $
        located $
            fmap TextLiteral $
                between (symbol "\"") (symbol "\"") $
                    takeWhileP (Just "text literal body") (/= '"')

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

charLiteral :: Lexer Literal
charLiteral = label "char literal" $ try $ located $ fmap CharLiteral $ one <$> between (single '\'') (symbol "'") anySingle

-- | any literal
literal :: Lexer Literal
literal = choice [intLiteral, textLiteral, charLiteral]

operator :: Text -> Lexer Loc
operator sym = label "operator" $ lexeme $ withLoc' const $ string sym *> notFollowedBy (satisfy isOperatorChar)

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

isOperatorChar :: Char -> Bool
isOperatorChar = (`elem` ("+-*/%^=><&.~!?|@#$:" :: String))

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
parens, brackets, braces :: Parser a -> Parser a
parens = between (punctuation "(") (punctuation ")")
brackets = between (punctuation "[") (punctuation "]")
braces = between (punctuation "{") (punctuation "}")

-- leading commas, trailing commas, anything goes
commaSep :: Parser a -> Parser [a]
commaSep p = optional (punctuation ",") *> p `sepEndBy` punctuation ","

{- | parses an AST node with location info
todo: don't include trailing whitespace where possible
-}
withLoc :: Lexer (Loc -> a) -> Lexer a
withLoc p = do
    start <- getSourcePos
    f <- p
    end <- getSourcePos
    let loc = if start == end then Blank else locFromSourcePos start end
    pure $ f loc

withLoc' :: (Loc -> a -> b) -> Lexer a -> Lexer b
withLoc' f p = withLoc $ flip f <$> p

located :: Lexer a -> Lexer (Located a)
located p = withLoc $ flip Located <$> p

mkName :: Lexer Text -> Lexer SimpleName
mkName = located . fmap Name'
