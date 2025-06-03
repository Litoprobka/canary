{-# HLINT ignore "Use <$>" #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module Parser (code, declaration, pattern', patternParens, term, termParens, Parser', parseModule, run) where

import LangPrelude hiding (error)

import Common (
    Fixity (..),
    Located (..),
    Pass (..),
    PriorityRelation' (..),
    SimpleName,
    getLoc,
    mkNotes,
    unLoc,
    zipLocOf,
    pattern L,
    pattern (:@),
 )
import Control.Monad.Combinators
import Control.Monad.Combinators.NonEmpty qualified as NE
import Data.List.NonEmpty qualified as NE
import Diagnostic (Diagnose, fatal)
import Error.Diagnose (Marker (This, Where), Report (..))
import Lexer
import Prettyprinter.Render.Terminal (AnsiStyle)
import Proto hiding (token)
import Syntax
import Syntax.Declaration qualified as D
import Syntax.Row
import Syntax.Row qualified as Row
import Syntax.Term
import Syntax.Token (SpecialSymbol, tok)
import Syntax.Token qualified as Token

data ParseError = ParseError {unexpected :: Located Token.Token, expecting :: Doc AnsiStyle} deriving (Show)
type Parser' = Parser ParseError

parseError :: Doc AnsiStyle -> Parser' x
parseError expecting = do
    unexpected <- lookAhead anyToken
    error ParseError{unexpected, expecting}

orError :: Parser' a -> Doc AnsiStyle -> Parser' a
orError p expecting = p <|> parseError expecting

reportParseError :: Maybe ParseError -> Report (Doc AnsiStyle)
reportParseError Nothing = Err Nothing "Internal error: the parser backtracked all the way to the start" [] []
reportParseError (Just ParseError{unexpected, expecting}) =
    Err
        Nothing
        "Parse error"
        ( mkNotes [(getLoc unexpected, This ("unexpected" <+> pretty unexpected)), (getLoc unexpected, Where ("expecting" <+> expecting))]
        )
        []

run :: Diagnose :> es => (FilePath, ByteString) -> Parser' a -> Eff es a
run (fileName, fileContents) parser = do
    tokenStream <- lex (fileName, fileContents)
    either (fatal . one . reportParseError) pure $
        parse (parser <* eof `orError` "end of input") tokenStream

parseModule :: Diagnose :> es => (FilePath, ByteString) -> Eff es [Declaration 'Parse]
parseModule input = run input code

code :: Parser' [Declaration 'Parse]
code = topLevelBlock declaration

declaration :: Parser' (Declaration 'Parse)
declaration = located $ choice [typeDec, fixityDec, signature, valueDec]
  where
    valueDec = D.Value <$> binding <*> option [] whereBlock
    whereBlock = block Token.Where (parseError "declarations") (located valueDec)

    typeDec = do
        keyword Token.Type
        name <- identifier `orError` "a type name"
        gadtDec name <|> simpleTypeDec name

    simpleTypeDec name = do
        vars <- many varBinder
        pats <- option [] $ specialSymbol Token.Eq *> typePattern `sepBy1` specialSymbol Token.Bar
        pure $ D.Type name vars pats

    gadtDec :: SimpleName -> Parser' (Declaration_ 'Parse)
    gadtDec name = do
        mbKind <- optional $ specialSymbol Token.Colon *> term
        constrs <- block Token.Where (parseError "constructor signatures") $ withLoc do
            con <- upperName
            specialSymbol Token.Colon
            sig <- term
            pure \loc -> D.GadtConstructor loc con sig
        pure $ D.GADT name mbKind constrs

    typePattern :: Parser' (Constructor 'Parse)
    typePattern = withLoc do
        name <- upperName
        args <- many termParens
        pure \loc -> D.Constructor loc name args

    signature = do
        name <- identifier <* specialSymbol Token.Colon
        D.Signature name <$> term

    fixityDec = do
        keyword Token.Infix
        fixity <-
            choice
                [ InfixL <$ ctxKeyword "left"
                , InfixR <$ ctxKeyword "right"
                , InfixChain <$ ctxKeyword "chain"
                , pure Infix
                ]
        op <- operator `orError` "name of the operator"
        above <- option [] do
            ctxKeyword "above"
            commaSep (Just <$> operator <|> Nothing <$ ctxKeyword "application")
        below <- option [] do
            ctxKeyword "below"
            commaSep operator
        equal <- option [] do
            ctxKeyword "equals"
            commaSep operator
        pure $ D.Fixity fixity op PriorityRelation{above, below, equal}

varBinder :: Parser' (VarBinder 'Parse)
varBinder =
    parens (VarBinder <$> var <* specialSymbol Token.Colon <*> fmap Just term)
        <|> flip VarBinder Nothing
            <$> var
  where
    var = identifier <|> mkName $(tok 'Token.ImplicitName)

someRecord :: SpecialSymbol -> Parser' value -> Maybe (SimpleName -> value) -> Parser' (ExtRow value)
someRecord delim valueP missingValue = braces do
    row <- fromList <$> commaSep recordItem
    optional (specialSymbol Token.Bar *> valueP) <&> \case
        Just ext -> ExtRow row ext
        Nothing -> NoExtRow row
  where
    onMissing name = case missingValue of
        Nothing -> id
        Just nameToValue -> option (nameToValue name)
    recordItem = do
        recordLabel <- identifier
        valuePattern <- onMissing recordLabel $ specialSymbol delim *> valueP
        pure (recordLabel, valuePattern)

noExtRecord :: SpecialSymbol -> Parser' value -> Maybe (SimpleName -> value) -> Parser' (Row value)
noExtRecord delim valueP missingValue =
    someRecord delim valueP missingValue
        >>= \case
            NoExtRow row -> pure row
            ExtRow{} -> parseError "unexpected row extension"

lambda' :: Parser' (Expr 'Parse)
lambda' = withLoc do
    specialSymbol Token.Lambda
    args <- NE.some patternParens `orError` "argument patterns"
    specialSymbol Token.Arrow
    body <- term
    pure \loc -> foldr (\var -> Located loc . Lambda var) body args

quantifier :: Parser' (Type 'Parse)
quantifier = withLoc do
    (q, erased) <-
        choice
            [ (Forall, Erased) <$ keyword Token.Forall
            , (Exists, Erased) <$ keyword Token.Exists
            , (Forall, Retained) <$ keyword Token.Foreach
            , (Exists, Retained) <$ keyword Token.Some
            ]
    binders <- NE.some varBinder `orError` "a variable with an optional type"
    let arrOrStar = case q of
            Forall -> Token.Arrow
            Exists -> Token.DepPair
    visibility <-
        (Implicit <$ specialSymbol Token.Dot <|> Visible <$ specialSymbol arrOrStar) `orError` ("a . or an" <+> pretty arrOrStar)
    body <- term
    pure \loc -> foldr (\binder acc -> Located loc $ Q q visibility erased binder acc) body binders

pattern' :: Parser' (Pattern 'Parse)
pattern' = located do
    pat <-
        choice
            [ located $ ConstructorP <$> upperName <*> many patternParens
            , located $ VariantP <$> variantConstructor <*> patternParens
            , patternParens
            ]
    option (unLoc pat) do
        specialSymbol Token.Colon
        AnnotationP pat <$> term

{- | parses a pattern with constructors enclosed in parens
should be used in cases where multiple patterns in a row are accepted, i.e.
function definitions and match expressions
-}
patternParens :: Parser' (Pattern 'Parse)
patternParens =
    located . choice $
        [ VarP <$> termName
        , WildcardP <$> $(tok 'Token.Wildcard)
        , record
        , ListP <$> brackets (commaSep pattern')
        , LiteralP <$> literal
        , -- todo: tightly-bound record
          ConstructorP <$> upperName <*> pure []
        , (\(con :@ loc) -> VariantP con (unit :@ loc)) <$> located variantConstructor -- some sugar for variants with a unit payload
        , unLoc <$> parens pattern'
        ]
  where
    record = RecordP <$> noExtRecord Token.Eq pattern' (Just $ \n -> Located (getLoc n) $ VarP n)
    unit = RecordP Row.empty

binding :: Parser' (Binding 'Parse)
binding = do
    f <-
        -- it should probably be `try (E.FunctionBinding <$> funcName) <*> NE.some patternParens
        -- for cleaner parse errors
        try (FunctionB <$> funcName <*> NE.some patternParens)
            <|> (ValueB <$> pattern')
    specialSymbol Token.Eq
    f <$> term
  where
    -- we might want to support infix operator declarations in the future
    -- > f $ x = f x
    funcName = identifier

-- an expression with infix operators and unresolved priorities
-- the `E.Infix` constructor is only used when there is more than one operator
-- function arrows are a special case that is handled directly in the parser
term :: Parser' (Expr 'Parse)
term = rightAssoc Token.Colon Annotation nonAnn
  where
    rightAssoc :: Token.SpecialSymbol -> (Located expr -> Located expr -> expr) -> Parser' (Located expr) -> Parser' (Located expr)
    rightAssoc opToken con argParser = parser
      where
        parser = located do
            lhs <- argParser
            option (unLoc lhs) do
                specialSymbol opToken
                rhs <- parser
                pure $ con lhs rhs

    -- second lowest level of precedence, 'anything but annotations'
    -- so far, this level has only right-associative dependent pairs
    -- 'depPairArg' ** 'nonAnn'
    nonAnn :: Parser' (Expr 'Parse)
    nonAnn = rightAssoc Token.DepPair Sigma depPairArg

    -- third lowest level of precedence, something that can appear in a dependent pair
    depPairArg :: Parser' (Expr 'Parse)
    depPairArg = rightAssoc Token.Arrow Function infixExpr
      where
        -- an expression that contains infix operators with unresolved precedences
        infixExpr = located do
            (firstExpr, pairs) <- do
                firstExpr <- noPrec
                pairs <- many $ (,) <$> optional operator <*> noPrec
                pure (firstExpr, pairs)
            pure case pairs of
                [] -> unLoc firstExpr
                [(Nothing, secondExpr)] -> firstExpr `App` secondExpr
                [(Just op, secondExpr)] -> Located (zipLocOf firstExpr op) (Located (getLoc op) (Name op) `App` firstExpr) `App` secondExpr -- todo: a separate AST node for an infix application?
                (_ : _ : _) -> uncurry InfixE $ shift firstExpr pairs
        -- x [(+, y), (*, z), (+, w)] --> [(x, +), (y, *), (z, +)] w
        shift expr [] = ([], expr)
        shift lhs ((op, rhs) : rest) = first ((lhs, op) :) $ shift rhs rest
    -- type application precedence level
    typeApp = do
        expr <- termParens
        -- type applications bind tighther than anything else
        -- this might not work well with higher-than-application precedence operators, though
        apps <- many do
            specialSymbol Token.At
            termParens
        pure $ foldl' (\e app -> Located (zipLocOf e app) $ TypeApp e app) expr apps

    noPrec = keywordBased <|> typeApp

    -- expression forms that have a leading keyword/symbol
    -- most of them also consume all trailing terms
    keywordBased :: Parser' (Term 'Parse)
    keywordBased =
        located $
            choice
                [ unLoc <$> lambda'
                , unLoc <$> quantifier
                , Let <$> letBlock binding <*> term
                , letRec
                , case'
                , match'
                , if'
                , doBlock
                ]

letRec :: Parser' (Expr_ Parse)
letRec = do
    bindings <- letBlock (block Token.Rec (parseError "bindings") binding)
    case NE.nonEmpty bindings of
        Nothing -> parseError "empty let rec"
        Just bindingsNE -> LetRec bindingsNE <$> term `orError` "an expression at the end of a let rec block"

case' :: Parser' (Expr_ Parse)
case' = do
    keyword Token.Case
    arg <- term
    matches <- block Token.Of (parseError "pattern matches") $ (,) <$> pattern' <* specialSymbol Token.Arrow <*> term
    pure $ Case arg matches

match' :: Parser' (Expr_ Parse)
match' = Match <$> block Token.Match (parseError "pattern matches") ((,) <$> some patternParens <* specialSymbol Token.Arrow <*> term)

if' :: Parser' (Expr_ Parse)
if' = do
    keyword Token.If
    cond <- term
    keyword Token.Then
    true <- term
    keyword Token.Else
    false <- term
    pure $ If cond true false

doBlock :: Parser' (Expr_ Parse)
doBlock = do
    stmts <-
        block Token.Do (parseError "do-actions") . located . choice $
            [ Bind <$> pattern' <* specialSymbol Token.BackArrow <*> term
            , With <$ keyword Token.With <*> pattern' <* specialSymbol Token.BackArrow <*> term
            , keyword Token.Let *> fmap DoLet binding
            , Action <$> term
            ]
    case unsnoc stmts of
        Nothing -> parseError "empty do block"
        Just (stmts', L (Action lastAction)) -> pure $ Do stmts' lastAction
        _ -> parseError "last statement in a do block must be an expression"
  where
    unsnoc [] = Nothing
    unsnoc [x] = Just ([], x)
    unsnoc (x : xs) = first (x :) <$> unsnoc xs

-- a term that may be used as a type parameter or type application
-- that is, it does not contain any unparenthesized spaces
termParens :: Parser' (Expr 'Parse)
termParens =
    located $
        choice
            [ try record
            , recordType -- todo: ambiguity with empty record value
            , try $ List <$> brackets (commaSep term)
            , -- todo: since annotation expressions are a thing, variantType is pretty much always ambiguous
              -- perhaps it should require a trailing |?
              variantType
            , try $ Name <$> parens operator
            , parens $ unLoc <$> term
            , -- , RecordLens <$> _recordLens
              -- , tightConstructor
              Variant <$> variantConstructor
            , Literal <$> literal
            , Name <$> identifier
            , ImplicitVar <$> mkName $(tok 'Token.ImplicitName)
            , parens $ unLoc <$> term
            ]
  where
    variantItem = do
        con :@ loc <- variantConstructor
        ty <- option (Located loc $ RecordT $ NoExtRow Row.empty) termParens
        pure (con :@ loc, ty)
    record = Record <$> noExtRecord Token.Eq term (Just $ \n -> Located (getLoc n) $ Name n)
    recordType = RecordT <$> someRecord Token.Colon term Nothing
    variantType = brackets do
        items <- fromList <$> commaSep variantItem
        VariantT <$> option (NoExtRow items) do
            specialSymbol Token.Bar
            ExtRow items <$> term

-- todo: tight record binding
{-
tightConstructor = do
    name <- upperName
    -- somehow check for no whitespace between the name and the record
    optional (located record) <&> \case
        Nothing -> Name name
        Just arg -> Located (getLoc name) (Name name) `App` arg
-}
