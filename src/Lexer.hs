{-# LANGUAGE TemplateHaskell #-}
{-# HLINT ignore "Use <$>" #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module Lexer where

import Common (Literal_ (..), Loc (..), Located (..), SimpleName, SimpleName_ (..), unLoc, zipLoc, pattern L)
import Data.Char (isLetter, isSpace, isUpperCase)
import Data.Text qualified as Text
import Data.Vector (Vector)
import Data.Vector qualified as V
import LangPrelude hiding (optional)

-- import Text.Megaparsec hiding (Token, token)
import Text.Megaparsec qualified as MP

-- import Text.Megaparsec.Char hiding (newline, space)

import Common qualified as C
import Control.Monad.Combinators (between, choice, skipManyTill)
import Data.List.NonEmpty qualified as NE
import Diagnostic
import Error.Diagnose (Position (..))
import FlatParse.Stateful hiding (Parser, Pos, ask, local, try, (<|>))
import FlatParse.Stateful qualified as FP
import Syntax.Token

type Parser = MP.Parsec Void TokenStream

{- | state stores the last newline
| reader env stores the current block offset
-}
type Lexer = FP.Parser Int ()

newtype TokenStream = TokenStream (Vector (Located Token)) deriving (Show)

instance MP.Stream TokenStream where
    type Token TokenStream = Located Token
    type Tokens TokenStream = Vector (Located Token)

    tokensToChunk _ = V.fromList
    chunkToTokens _ = V.toList
    chunkLength _ = length
    chunkEmpty _ = null
    take1_ (TokenStream v) =
        V.uncons v <&> second TokenStream
    takeN_ n (TokenStream v)
        | V.null v = Nothing
        | otherwise =
            let (toks, v') = V.splitAt n v
             in Just (toks, TokenStream v')
    takeWhile_ p (TokenStream v) =
        let (toks, v') = V.span p v
         in (toks, TokenStream v')

instance MP.VisualStream TokenStream where
    showTokens _ tokens = show $ foldMap pretty tokens

-- * Interface used by the parser

token :: Token -> Parser ()
token inputToken = MP.label (show inputToken) $ void $ MP.satisfy ((== inputToken) . unLoc)

-- | parses a keyword token
keyword :: Keyword -> Parser ()
keyword = token . Keyword

-- | parser a SpecialSymbol token
specialSymbol :: SpecialSymbol -> Parser ()
specialSymbol = token . SpecialSymbol

{- | parses a statement separator
a \\n should have the same indent as previous blocks. A semicolon always works
-}
newline :: Parser ()
newline = MP.label "separator" $ token Semicolon <|> token Newline

-- | parses a contextual keyword - that is, an identifier that behaves as a keyword in some cases
ctxKeyword :: Text -> Parser ()
ctxKeyword kw = MP.try do
    L (Name' text) <- lowerName <|> upperName
    guard $ text == kw

block :: BlockKeyword -> Parser p -> Parser [p]
block kw p = do
    token $ BlockStart kw
    items <- p `MP.sepBy` newline
    token BlockEnd
    pure items

letBlock :: Parser p -> Parser p
letBlock p = do
    keyword Let
    p <* newline

topLevelBlock :: Parser p -> Parser [p]
topLevelBlock p = p `MP.sepBy` newline

-- | an identifier that doesn't start with an uppercase letter
lowerName :: Parser SimpleName
lowerName = mkName $(tok "lowercase identifier" 'LowerName)

-- | an identifier that doesn't start with an uppercase letter or a parenthesised operator
termName :: Parser SimpleName
termName = MP.try (parens operator) <|> lowerName

-- | an identifier that starts with an uppercase letter
upperName :: Parser SimpleName
upperName = mkName $(tok "uppercase identifier" 'UpperName)

-- | an identifier that starts with a ' and an uppercase letter, i.e. 'Some
variantConstructor :: Parser SimpleName
variantConstructor = mkName $(tok "variant constructor" 'VariantName)

literal :: Parser C.Literal
literal = located $(tok "literal" 'Literal)

operator :: Parser SimpleName
operator = mkName $(tok "operator" 'Op)

{- todo: it might be a good idea to ignore strict newlines when inside the brackets
i.e. that would allow
> stuff = [
>   x,
>   y,
>   z,
> ]
the indentation inside the list is optional as well
using anything indentation-sensitve, i.e. do notation, reintroduces strict newlines
> otherStuff = [
>   x,
>   do
>     action1
>     action2,
>   y,
> ]
-}
parens, brackets, braces :: Parser a -> Parser a
parens = between (token LParen) (token RParen)
brackets = between (token LBracket) (token RBracket)
braces = between (token LBrace) (token RBrace)

-- leading commas, trailing commas, anything goes
commaSep :: Parser a -> Parser [a]
commaSep p = MP.optional (token Comma) *> p `MP.sepEndBy` token Comma

-- like 'commaSep', but parses one or more items
commaSep1 :: Parser a -> Parser [a]
commaSep1 p = MP.optional (token Comma) *> p `MP.sepEndBy1` token Comma

{- | parses an AST node with location info
todo: don't include trailing whitespace where possible
-}
withLoc :: Parser (Loc -> a) -> Parser a
withLoc p = do
    Located startLoc _ <- MP.lookAhead MP.anySingle
    (tokens, f) <- MP.match p
    let loc = case V.unsnoc tokens of
            Nothing -> Blank -- do we ever use location info for zero-sized AST nodes? does this matter?
            Just (_, Located endLoc _) -> zipLoc startLoc endLoc
    pure $ f loc

located :: Parser a -> Parser (Located a)
located p = withLoc $ flip Located <$> p

mkName :: Parser Text -> Parser SimpleName
mkName = located . fmap Name'

-- * Lexer implementation details

-- | lex an input file in UTF-8 encoding. Lexer errors are todo
lex :: Diagnose :> es => (FilePath, ByteString) -> Eff es TokenStream
lex (fileName, fileContents) = do
    let startPos = FP.unPos (FP.mkPos fileContents (0, 0))
    tokens <- case FP.runParser (concatMap NE.toList <$> many token') 0 startPos fileContents of
        OK result _ _ -> pure result
        _ -> internalError Blank "todo: lexer errors lol"
    pure $ mkTokenStream (fileName, fileContents) tokens

mkTokenStream :: (FilePath, ByteString) -> [(Span, Token)] -> TokenStream
mkTokenStream (fileName, fileContents) tokens = TokenStream $ V.fromList locatedTokens
  where
    locatedTokens = zipWith (flip Located) justTokens $ map mkPos $ pairs $ posLineCols fileContents tokenSpans
    justTokens = map snd tokens
    tokenSpans = concatMap (\(Span from to, _) -> [from, to]) tokens
    pairs (x : y : xs) = (x, y) : pairs xs
    pairs _ = []
    mkPos ((lineFrom, columnFrom), (lineTo, columnTo)) =
        Loc
            Position
                { begin = (lineFrom + 1, columnFrom + 1)
                , end = (lineTo + 1, columnTo + 1)
                , file = fileName
                }

{-# INLINE token' #-}
token' :: Lexer (NonEmpty (Span, Token))
token' = tokenNoWS <* spaceOrLineWrap
  where
    tokenNoWS :: Lexer (NonEmpty (Span, Token))
    tokenNoWS =
        ((:|) <$> withSpan' (BlockStart <$> blockKeyword) <*> block')
            <|> letBlock'
            <|> choice
                [ Keyword <$> keyword'
                , $( switch
                        [|
                            case _ of
                                "∀" -> pure $ Keyword Forall
                                "Π" -> Keyword Foreach <$ fails (satisfy isIdentifierChar)
                                "∃" -> pure $ Keyword Exists
                                "Σ" -> Keyword Some <$ fails (satisfy isIdentifierChar)
                                "\\" -> pure $ SpecialSymbol Lambda
                                "(" -> pure LParen
                                ")" -> pure RParen
                                "{" -> pure LBrace -- todo: tight braces
                                "}" -> pure RBrace
                                "[" -> pure LBracket
                                "]" -> pure RBracket
                                "," -> pure Comma
                                ";" -> pure Semicolon
                            |]
                   )
                , identifier' -- make sure that identifier is applied after all keyword parsers
                , Literal <$> choice [intLiteral, textLiteral, charLiteral]
                , quotedIdent
                , SpecialSymbol <$> specialSymbol'
                , operator' -- same as above, operator' should be after specialSymbol
                ]
            `withSpan` (\tok span -> pure $ one (span, tok))
            <|> fmap one (withSpan' exactNewline)

withSpan' :: Lexer a -> Lexer (Span, a)
withSpan' p = withSpan p \tok span -> pure (span, tok)

-- it might be cleaner to parse an identifier and then check whether it's a keyword
keyword' :: Lexer Keyword
keyword' =
    $(rawSwitchWithPost (Just [|fails (satisfy isIdentifierChar)|]) (parseTable @Keyword) Nothing)

specialSymbol' :: Lexer SpecialSymbol
specialSymbol' =
    $(rawSwitchWithPost (Just [|fails (satisfy isOperatorChar)|]) (parseTable @SpecialSymbol) Nothing)

blockKeyword :: Lexer BlockKeyword
blockKeyword =
    $( switchWithPost
        (Just [|fails (satisfy isIdentifierChar)|])
        [|
            case _ of
                "match" -> pure Match
                "of" -> pure Of
                "where" -> pure Where
                "do" -> pure Do
            |]
     )

-- todo: should operators in parens be identifiers?
identifier' :: Lexer Token
identifier' = do
    firstChar <- satisfy isLetter <|> ('_' <$ $(char '_'))
    ident <- Text.pack . (firstChar :) <$> many (satisfy isIdentifierChar)
    pure case firstChar of
        '_' -> Wildcard ident
        c | isUpperCase c -> UpperName ident
        _ -> LowerName ident

quotedIdent :: Lexer Token
quotedIdent = do
    $(char '\'')
    identTail <- some (satisfy isIdentifierChar)
    let ident = Text.pack $ '\'' : identTail
    pure case listToMaybe identTail of
        Just c | isUpperCase c -> VariantName ident
        _ -> ImplicitName ident

operator' :: Lexer Token
operator' = Op . Text.pack <$> some (satisfy isOperatorChar)

-- | a newline with the same column offset as the current block
exactNewline :: Lexer Token
exactNewline =
    Newline <$ do
        newlines
        offset <- columnBytes
        blockOffset <- FP.ask
        guard $ offset == blockOffset

block' :: Lexer [(Span, Token)]
block' = do
    spaceOrLineWrap
    newOffset <- columnBytes
    prevOffset <- FP.ask
    blockContents <-
        if newOffset <= prevOffset
            then pure []
            else FP.local (const newOffset) do
                concatMap NE.toList <$> FP.many token'
    blockEnd <- withSpan' (pure BlockEnd)
    pure $ blockContents <> one blockEnd

-- the scoping rules of let blocks are slightly different
letBlock' :: Lexer (NonEmpty (Span, Token))
letBlock' = do
    offset <- columnBytes
    letTok <- withSpan' $ Keyword Let <$ $(string "let") `notFollowedBy` satisfy isOperatorChar
    spaceOrLineWrap -- we have to remove the whitespace after the token manually here
    tokens <- FP.local (const offset) do
        -- todo: this is ugly
        -- I think it might be not quite right to parse a semicolon as an exact newline here, since it might appear in a nested scope
        -- e.g. `let test = do this; that\nbody`
        -- perhaps a better approach is to drop the `someTill` part and just parse a terminator afterwards?
        let terminatorP = withSpan' $ exactNewline <|> Semicolon <$ $(char ';')
        (tokens, terminator) <- first (concatMap NE.toList) <$> token' `MP.someTill_` terminatorP
        pure $ tokens <> [terminator]
    pure $ letTok :| tokens

-- | returns the byte offset since the last occured newline
columnBytes :: Lexer Int
columnBytes = do
    lastNewline <- FP.get
    pos <- FP.getPos
    pure $ lastNewline - pos.unPos

{- | any non-zero amount of newlines and any amount of whitespace

i.e. it skips lines of whitespace entirely
-}
newlines :: Lexer ()
newlines = skipSome $ newlineWithMeta *> space'
  where
    newlineWithMeta :: Lexer ()
    newlineWithMeta = do
        $(char '\n')
        pos <- FP.getPos
        FP.put pos.unPos

-- | non-newline space
space' :: Lexer ()
space' =
    choice
        [ skipMany (skipSatisfy \c -> isSpace c && c /= '\n')
        , $(string "---") <* skipAnyChar `skipManyTill` $(string "---")
        , $(string "--") <* takeLine
        ]

-- | space or a newline with increased indentation
spaceOrLineWrap :: Lexer ()
spaceOrLineWrap = void $ space' `MP.sepBy` lineWrap
  where
    lineWrap = do
        blockIndent <- FP.ask
        newlines
        currentIndent <- columnBytes
        guard $ currentIndent > blockIndent

intLiteral :: Lexer Literal_
intLiteral = IntLiteral <$> anyAsciiDecimalInt

-- todo: handle escape sequences and interpolation
textLiteral :: Lexer Literal_
textLiteral = fmap (TextLiteral . Text.pack) $ between $(char '\"') $(char '\"') $ many (satisfy (/= '"'))

charLiteral :: Lexer Literal_
charLiteral = CharLiteral . one <$> between $(char '\'') $(char '\'') anyChar
