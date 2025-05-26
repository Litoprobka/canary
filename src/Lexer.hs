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
import Language.Haskell.TH qualified as TH
import Syntax.Token

type Parser = MP.Parsec Void TokenStream

{- | state stores the last newline
| reader env stores the current block offset
-}
type Lexer = FP.Parser Int ()

newtype TokenStream = TokenStream (Vector (Located Token))

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

{- | matches a token pattern and returns its payload

tok :: Pattern (a -> Token) -> Lexer a
-}
tok :: TH.Name -> TH.ExpQ
tok patName = do
    x <- TH.newName "x"
    [|
        MP.try do
            L $(TH.conP patName [TH.varP x]) <- MP.anySingle
            pure $(TH.varE x)
        |]

{- | parses a keyword token
it is assumed that `kw` appears in the `keywords` list
-}
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
lowerName = MP.try $ mkName do
    L (LowerName name) <- MP.anySingle
    pure name

-- | an identifier that doesn't start with an uppercase letter or a parenthesised operator
termName :: Parser SimpleName
termName = parens operator <|> lowerName

-- | an identifier that starts with an uppercase letter
upperName :: Parser SimpleName
upperName = MP.try $ mkName do
    L (UpperName name) <- MP.anySingle
    pure name

-- | an identifier that starts with a ' and an uppercase letter, i.e. 'Some
variantConstructor :: Parser SimpleName
variantConstructor = MP.try $ mkName do
    L (VariantName name) <- MP.anySingle
    pure name

literal :: Parser C.Literal
literal = MP.try $ located do
    L (Literal lit) <- MP.anySingle
    pure lit

operator :: Parser SimpleName
operator = MP.try $ mkName do
    L (Op op) <- MP.anySingle
    pure op

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
brackets = between (token RBracket) (token RBracket)
braces = between (token LBrace) (token RBrace)

-- leading commas, trailing commas, anything goes
commaSep :: Parser a -> Parser [a]
commaSep p = MP.optional (token Comma) *> p `MP.sepEndBy` token Comma

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
    tokensWithSpans <- case FP.runParser (concatMap NE.toList <$> many token') 0 startPos fileContents of
        OK result _ _ -> pure result
        _ -> internalError Blank "todo: lexer errors lol"
    let tokenSpans = concatMap (\(Span from to, _) -> [from, to]) tokensWithSpans
        tokens = map snd tokensWithSpans
        locatedTokens = zipWith (flip Located) tokens $ map mkPos $ pairs $ posLineCols fileContents tokenSpans
    pure $ TokenStream $ V.fromList locatedTokens
  where
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
    ident <- Text.pack . ('\'' :) <$> some (satisfy isIdentifierChar)
    pure case Text.head ident of
        c | isUpperCase c -> VariantName ident
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
