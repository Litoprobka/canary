{-# LANGUAGE TemplateHaskell #-}
{-# HLINT ignore "Use <$>" #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module Lexer where

import Common (Literal_ (..), Loc (..), Located (..), SimpleName, SimpleName_ (..), unLoc, zipLocOf, pattern L)
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
import FlatParse.Stateful hiding (Parser, Pos, ask, local, try, (<|>))
import FlatParse.Stateful qualified as FP
import Language.Haskell.TH qualified as TH
import Syntax.Token

type Parser = ReaderT MP.Pos (MP.Parsec Void TokenStream)

{- | state stores the last newline
| reader env stores the current block offset
-}
type Lexer = FP.Parser Int ()

newtype TokenStream = TokenStream (Vector (Located Token))

instance MP.Stream TokenStream where
    type Token TokenStream = Token
    type Tokens TokenStream = Vector Token

    tokensToChunk _ = V.fromList
    chunkToTokens _ = V.toList
    chunkLength _ = length
    chunkEmpty _ = null
    take1_ (TokenStream v) =
        V.uncons v <&> \(L tok, v') ->
            (tok, TokenStream v')
    takeN_ n (TokenStream v)
        | V.null v = Nothing
        | otherwise =
            let (toks, v') = V.splitAt n v
             in Just (fmap unLoc toks, TokenStream v')
    takeWhile_ p (TokenStream v) =
        let (toks, v') = V.span (p . unLoc) v
         in (fmap unLoc toks, TokenStream v')

-- * Interface used by the parser

token :: Token -> Parser ()
token = void . MP.single

{- | matches a token pattern and returns its payload

tok :: Pattern (a -> Token) -> Lexer a
-}
tok :: TH.Name -> TH.ExpQ
tok patName = do
    x <- TH.newName "x"
    [|
        do
            $(TH.conP patName [TH.varP x]) <- MP.anySingle
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
lowerName = mkName do
    LowerName name <- MP.anySingle
    pure name

-- | an identifier that doesn't start with an uppercase letter or a parenthesised operator
termName :: Parser SimpleName
termName = parens operator <|> lowerName

-- | an identifier that starts with an uppercase letter
upperName :: Parser SimpleName
upperName = mkName do
    UpperName name <- MP.anySingle
    pure name

-- | an identifier that starts with a ' and an uppercase letter, i.e. 'Some
variantConstructor :: Parser SimpleName
variantConstructor = mkName do
    VariantName name <- MP.anySingle
    pure name

literal :: Parser C.Literal
literal = located do
    Literal lit <- MP.anySingle
    pure lit

operator :: Parser SimpleName
operator = mkName do
    Op op <- MP.anySingle
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
    startOffset <- MP.getOffset
    f <- p
    endOffset <- MP.getOffset
    MP.State{MP.stateInput = TokenStream toks} <- MP.getParserState
    let loc
            | startOffset == endOffset = Blank -- do we ever use location info for zero-sized AST nodes? does this matter?
            | otherwise = zipLocOf (toks V.! startOffset) (toks V.! (endOffset - 1))
    pure $ f loc

located :: Parser a -> Parser (Located a)
located p = withLoc $ flip Located <$> p

mkName :: Parser Text -> Parser SimpleName
mkName = located . fmap Name'

-- * Lexer implementation details

{-# INLINE token' #-}
token' :: Lexer (NonEmpty Token)
token' =
    one
        <$> choice
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
            , identifier'
            , quotedIdent
            , SpecialSymbol <$> specialSymbol'
            , operator'
            , Literal <$> choice [intLiteral, textLiteral, charLiteral]
            ]
        <|> ((:|) <$> (BlockStart <$> blockKeyword) <*> block')
        <|> letBlock'
  where
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

    -- \| a newline with the same column offset as the current block
    exactNewline :: Lexer Token
    exactNewline =
        Newline <$ do
            newlineWithMeta
            offset <- columnBytes
            blockOffset <- FP.ask
            guard $ offset == blockOffset

    block' :: Lexer [Token]
    block' = do
        spaceOrLineWrap
        newOffset <- columnBytes
        prevOffset <- FP.ask
        blockContents <-
            if newOffset <= prevOffset
                then pure []
                else FP.local (const newOffset) do
                    -- todo: this is ugly
                    fmap concat . FP.many $ (NE.toList <$> token' <|> fmap one exactNewline) <* spaceOrLineWrap
        pure $ blockContents <> one BlockEnd

    -- the scoping rules of let blocks are slightly different
    letBlock' :: Lexer (NonEmpty Token)
    letBlock' = do
        offset <- columnBytes
        $(string "let") `notFollowedBy` satisfy isOperatorChar
        tokens <- FP.local (const offset) do
            -- todo: this is ugly
            tokens <- fmap concat . FP.many $ (NE.toList <$> token') <* spaceOrLineWrap
            terminator <- exactNewline <|> Semicolon <$ $(char ';')
            pure $ tokens <> [terminator]
        pure $ Keyword Let :| tokens

    -- \| returns the byte offset since the last occured newline
    columnBytes :: Lexer Int
    columnBytes = do
        lastNewline <- FP.get
        pos <- FP.getPos
        pure $ lastNewline - pos.unPos

    newlineWithMeta :: Lexer ()
    newlineWithMeta = do
        $(char '\n')
        pos <- FP.getPos
        FP.put pos.unPos

    -- \| any non-zero amount of newlines and any amount of whitespace
    --      i.e. it skips lines of whitespace entirely
    --      should never be used outside of the block-parsing functions
    --
    newlines :: Lexer ()
    newlines = skipMany $ newlineWithMeta <|> space'

    -- \| non-newline space
    space' :: Lexer ()
    space' =
        choice
            [ skipSome (skipSatisfy isSpace)
            , $(string "---") <* skipAnyChar `skipManyTill` $(string "---")
            , $(string "--") <* takeLine
            ]

    -- \| space or a newline with increased indentation
    spaceOrLineWrap :: Lexer ()
    spaceOrLineWrap = void $ space' `MP.sepBy` newlineWithIndent
      where
        newlineWithIndent = do
            blockIndent <- FP.ask
            newlines
            currentIndent <- columnBytes
            guard $ currentIndent > blockIndent

    intLiteral :: Lexer Literal_
    intLiteral = IntLiteral <$> anyAsciiDecimalInt

    -- todo: handle escape sequences and interpolation
    textLiteral :: Lexer Literal_
    textLiteral = fmap (TextLiteral . Text.pack) $ between $(char '\'') $(char '\'') $ many (satisfy (/= '"'))

    charLiteral :: Lexer Literal_
    charLiteral = CharLiteral . one <$> between $(char '\'') $(char '\'') anyChar
