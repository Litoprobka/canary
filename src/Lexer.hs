{-# LANGUAGE TemplateHaskell #-}
{-# HLINT ignore "Use <$>" #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module Lexer where

import Common (Literal_ (..), Loc (..), Located (..), SimpleName, SimpleName_ (..), unLoc, zipLoc, pattern L, pattern Located)
import Common qualified as C
import Control.Monad.Combinators (between, choice, sepBy, sepEndBy, sepEndBy1, skipManyTill, someTill_)
import Control.Monad.Combinators qualified as P
import Data.Char (isLetter, isSpace, isUpperCase)
import Data.List.NonEmpty qualified as NE
import Data.Text qualified as Text
import Data.Vector (Vector)
import Data.Vector qualified as V
import Diagnostic
import Error.Diagnose (Position (..))
import FlatParse.Stateful hiding (Parser, Pos, ask, local, try, (<|>))
import FlatParse.Stateful qualified as FP
import LangPrelude hiding (optional)
import Proto qualified as P
import Syntax.Token

type Parser e = P.Proto e TokenStream

{- | state stores the last newline
| reader env stores the current block offset
-}
type Lexer = FP.Parser Int Void

newtype TokenStream = TokenStream (Vector (Located Token)) deriving (Show)

instance P.Stream TokenStream where
    type Token TokenStream = Located Token
    take1 (TokenStream s) = second TokenStream <$> V.uncons s

-- * Interface used by the parser

token :: Token -> Parser e ()
token inputToken = void $ P.satisfy ((== inputToken) . unLoc)

-- | parses a keyword token
keyword :: Keyword -> Parser e ()
keyword = token . Keyword

-- | parser a SpecialSymbol token
specialSymbol :: SpecialSymbol -> Parser e ()
specialSymbol = token . SpecialSymbol

{- | parses a statement separator
a \\n should have the same indent as previous blocks. A semicolon always works
-}
newline :: Parser e ()
newline = token Semicolon <|> token Newline

-- | parses a contextual keyword - that is, an identifier that behaves as a keyword in some cases
ctxKeyword :: Text -> Parser e ()
ctxKeyword kw = do
    L (Name' text) <- identifier
    guard $ text == kw

{- | parse an indented block, starting with the given block keyword

if a parsing failure occurs after the keyword, produce an throw an error
with the given error parser
-}
block :: BlockKeyword -> Parser e e -> Parser e p -> Parser e [p]
block kw mkError p = do
    token $ BlockStart kw
    parseItems <|> (mkError >>= P.error)
  where
    parseItems = (p `sepBy` newline) <* token BlockEnd

letBlock :: Parser e p -> Parser e p
letBlock p = do
    keyword Let
    p <* newline

topLevelBlock :: Parser e p -> Parser e [p]
topLevelBlock p = p `sepEndBy` newline

-- | an identifier that doesn't start with an uppercase letter or a parenthesised operator that doesn't start with a colon
termName :: Parser e SimpleName
termName = parens termOperator <|> mkName $(tok 'LowerName)

-- | an identifier that starts with an uppercase letter or a parenthesized operator that starts with a colon
upperName :: Parser e SimpleName
upperName = parens colonOperator <|> mkName $(tok 'UpperName)

-- do we even need the upper/lower distinction at lexer level?
identifier :: Parser e SimpleName
identifier =
    parens anyOperator <|> mkName do
        P.anyToken >>= \case
            L (UpperName name) -> pure name
            L (LowerName name) -> pure name
            _ -> P.failed

-- | an identifier that starts with a ' and an uppercase letter, i.e. 'Some
variantConstructor :: Parser e SimpleName
variantConstructor = mkName $(tok 'VariantName)

literal :: Parser e C.Literal
literal = located $(tok 'Literal)

anyOperator :: Parser e SimpleName
anyOperator = termOperator <|> colonOperator

termOperator :: Parser e SimpleName
termOperator = mkName $(tok 'Op)

colonOperator :: Parser e SimpleName
colonOperator = mkName $(tok 'ColonOp)

{- parens / brackets / braces locally disable the scoping rules,
which allows stuff like this without the parser complaining about a newline before the terminating bracket
> stuff = [
>   x,
>   y,
>   z,
> ]
the indentation inside the list is optional as well
using anything that uses block rules, i.e. do notation, reintroduces strict newlines
> otherStuff = [
>   x,
>   do
>     action1
>     action2,
>   y,
> ]
-}
parens, brackets, braces :: Parser e a -> Parser e a
parens = between (token LParen) (token RParen)
brackets = between (token LBracket) (token RBracket)
braces = between (token LBrace) (token RBrace)

-- leading commas, trailing commas, anything goes
commaSep :: Parser e a -> Parser e [a]
commaSep p = P.optional (token Comma) *> p `sepEndBy` token Comma

-- like 'commaSep', but parses one or more items
commaSep1 :: Parser e a -> Parser e [a]
commaSep1 p = P.optional (token Comma) *> p `sepEndBy1` token Comma

{- | parses an AST node with location info
todo: don't include trailing whitespace where possible
-}
withLoc :: Parser e (Loc -> a) -> Parser e a
withLoc p = do
    Located startLoc@(Loc Position{begin, file}) _ <- P.lookAhead P.anyToken
    TokenStream stream <- P.Proto \s -> P.Parsed s s
    f <- p
    TokenStream newStream <- P.Proto \s -> P.Parsed s s
    let tokensTaken = V.length stream - V.length newStream
        loc
            | tokensTaken <= 0 = Loc Position{begin, end = begin, file}
            | Just endToken <- stream V.!? (tokensTaken - 1) = zipLoc startLoc (C.getLoc endToken)
            | otherwise = startLoc
    pure $ f loc

located :: Parser e a -> Parser e (Located a)
located p = withLoc $ flip Located <$> p

mkName :: Parser e Text -> Parser e SimpleName
mkName = located . fmap Name'

-- * Lexer implementation details

-- | lex an input file in UTF-8 encoding. Lexer errors are todo
lex :: Diagnose :> es => Int -> (FilePath, ByteString) -> Eff es TokenStream
lex initOffset (fileName, fileContents) = do
    tokens <- case lex' initOffset fileContents of
        OK result _ _ -> pure result
        _ -> internalError' "todo: lexer errors lol"
    pure $ mkTokenStream (fileName, fileContents) tokens

-- | pure version of 'lex' that doesn't postprocess tokens
lex' :: Int -> ByteString -> Result Void [(Span, Token)]
lex' offset input = FP.runParser (FP.skip offset *> anySpace *> tokens) 0 startPos input
  where
    anySpace = FP.skipMany space1 `sepBy` newlines
    startPos = FP.unPos (FP.mkPos input (0, 0))

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

{-# INLINE tokens #-}
tokens :: Lexer [(Span, Token)]
tokens = concatMap NE.toList <$> FP.many token'

{-# INLINE token' #-}
token' :: Lexer (NonEmpty (Span, Token))
token' = tokenNoWS <* spaceOrLineWrap
  where
    tokenNoWS :: Lexer (NonEmpty (Span, Token))
    tokenNoWS =
        ((:|) <$> withSpan' (BlockStart <$> blockKeyword) <*> block')
            <|> parenBlock (LParen <$ $(char '(')) (RParen <$ $(char ')'))
            <|> parenBlock (LBracket <$ $(char '[')) (RBracket <$ $(char ']'))
            -- todo: tight braces
            <|> parenBlock (LBrace <$ $(char '{')) (RBrace <$ $(char '}'))
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
blockKeyword = $(rawSwitchWithPost (Just [|fails (satisfy isIdentifierChar)|]) (parseTable @BlockKeyword) Nothing)

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
operator' = do
    opStr <- some (satisfy isOperatorChar)
    let op = Text.pack opStr
    pure case listToMaybe opStr of
        Just ':' -> ColonOp op
        _ -> Op op

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
            else FP.local (const newOffset) tokens
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
        (tokens, terminator) <- first (concatMap NE.toList) <$> token' `someTill_` terminatorP
        pure $ tokens <> [terminator]
    pure $ letTok :| tokens

-- | inside parenthesis, outer scope block rules are disabled
parenBlock :: Lexer Token -> Lexer Token -> Lexer (NonEmpty (Span, Token))
parenBlock openP closeP = do
    open <- withSpan' openP <* spaceOrLineWrap
    -- an offset of -1 means that even an unindented newline would be considered a line continuation
    tokens <- FP.local (const (-1)) tokens
    close <- withSpan' closeP
    pure $ open :| tokens <> [close]

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
newlines = skipSome $ newlineWithMeta *> FP.skipMany space1
  where
    newlineWithMeta :: Lexer ()
    newlineWithMeta = do
        $(char '\n')
        pos <- FP.getPos
        FP.put pos.unPos

-- | non-zero amount of non-newline space
space1 :: Lexer ()
space1 =
    $( switch
        [|
            case _ of
                "---" -> skipAnyChar `skipManyTill` $(string "---")
                "--" -> skipMany $ skipSatisfy (/= '\n')
                _ -> skipSome (skipSatisfy \c -> isSpace c && c /= '\n')
            |]
     )

-- | space or a newline with increased indentation
spaceOrLineWrap :: Lexer ()
spaceOrLineWrap = void $ FP.skipMany space1 `sepBy` lineWrap
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
