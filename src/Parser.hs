{-# HLINT ignore "Use <$>" #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module Parser (code, declaration, pattern', term, parseModule, run) where

import LangPrelude

import Common (
    Fixity (..),
    Loc (..),
    Located (..),
    Pass (..),
    PriorityRelation' (..),
    SimpleName,
    SimpleName_ (..),
    locFromSourcePos,
    zipLocOf,
 )
import Control.Monad.Combinators.NonEmpty qualified as NE
import Data.List.NonEmpty qualified as NE
import Diagnostic (Diagnose, fatal, reportsFromBundle)
import Lexer
import Syntax
import Syntax.Declaration qualified as D
import Syntax.Row
import Syntax.Row qualified as Row
import Syntax.Term
import Text.Megaparsec
import Text.Megaparsec.Char (string)

run :: Diagnose :> es => (FilePath, Text) -> Parser a -> Eff es a
run (fileName, fileContents) parser =
    either (fatal . NE.toList . reportsFromBundle) pure $
        parse (usingReaderT pos1 parser) fileName fileContents

parseModule :: Diagnose :> es => (FilePath, Text) -> Eff es [Declaration 'Parse]
parseModule input = run input code

code :: Parser [Declaration 'Parse]
code = topLevelBlock declaration

declaration :: Parser (Declaration 'Parse)
declaration = withLoc $ choice [typeDec, fixityDec, signature, valueDec]
  where
    valueDec = flip3 D.Value <$> binding <*> whereBlock
    whereBlock = option [] $ block "where" (withLoc valueDec)

    typeDec = do
        keyword "type"
        name <- typeName
        simpleTypeDec name <|> gadtDec name

    simpleTypeDec name = do
        vars <- many varBinder
        specialSymbol "="
        flip4 D.Type name vars <$> typePattern `sepBy` specialSymbol "|"

    gadtDec :: SimpleName -> Parser (Loc -> Declaration 'Parse)
    gadtDec name = do
        mbKind <- optional $ specialSymbol ":" *> term
        constrs <- block "where" $ withLoc do
            con <- typeName
            specialSymbol ":"
            sig <- term
            pure $ flip3 D.GadtConstructor con sig
        pure $ flip4 D.GADT name mbKind constrs

    typePattern :: Parser (Constructor 'Parse)
    typePattern = withLoc do
        name <- typeName
        args <- many termParens
        pure $ flip3 D.Constructor name args

    signature = do
        name <- try $ (operatorInParens <|> termName) <* specialSymbol ":"
        flip3 D.Signature name <$> term

    fixityDec = do
        keyword "infix"
        fixity <-
            choice
                [ InfixL <$ keyword "left"
                , InfixR <$ keyword "right"
                , InfixChain <$ keyword "chain"
                , pure Infix
                ]
        op <- someOperator
        above <- option [] do
            keyword "above"
            commaSep (Just <$> someOperator <|> Nothing <$ keyword "application")
        below <- option [] do
            keyword "below"
            commaSep someOperator
        equal <- option [] do
            keyword "equals"
            commaSep someOperator
        pure $ \loc -> D.Fixity loc fixity op PriorityRelation{above, below, equal}

varBinder :: Parser (VarBinder 'Parse)
varBinder =
    parens (VarBinder <$> termName <* specialSymbol ":" <*> fmap Just term)
        <|> flip VarBinder Nothing
        <$> termName

typeVariable :: Parser (Type 'Parse)
typeVariable = Name <$> termName <|> ImplicitVar <$> implicitVariable

someRecord :: Text -> Parser value -> Maybe (SimpleName -> value) -> Parser (Row value)
someRecord delim valueP missingValue = braces (fromList <$> commaSep recordItem)
  where
    onMissing name = case missingValue of
        Nothing -> id
        Just nameToValue -> option (nameToValue name)
    recordItem = do
        recordLabel <- termName
        valuePattern <- onMissing recordLabel $ specialSymbol delim *> valueP
        pure (recordLabel, valuePattern)

lambdaLike :: (Loc -> a -> b -> b) -> Parser () -> Parser a -> Text -> Parser (b -> b)
lambdaLike con kw argP endSym = do
    kw
    args <- NE.some $ (,) <$> getSourcePos <*> argP
    specialSymbol endSym
    end <- getSourcePos
    pure \body -> foldr (\(start, arg) -> con (locFromSourcePos start end) arg) body args

pattern' :: Parser (Pattern 'Parse)
pattern' =
    choice
        [ ConstructorP <$> typeName <*> many patternParens
        , VariantP <$> variantConstructor <*> patternParens
        , patternParens
        ]

{- | parses a pattern with constructors enclosed in parens
should be used in cases where multiple patterns in a row are accepted, i.e.
function definitions and match expressions
-}
patternParens :: Parser (Pattern 'Parse)
patternParens = do
    pat <-
        choice
            [ VarP <$> termName
            , lexeme $ withLoc' WildcardP $ string "_" <* option "" termName'
            , record
            , withLoc' ListP $ brackets (commaSep pattern')
            , LiteralP <$> literal
            , -- a constructor without arguments or with a tightly-bound record pattern
              lexeme $ ConstructorP <$> constructorName <*> option [] (one <$> record)
            , flip VariantP unit <$> variantConstructor -- some sugar for variants with a unit payload
            , parens pattern'
            ]
    option pat do
        specialSymbol ":"
        AnnotationP pat <$> term
  where
    record = withLoc' RecordP $ someRecord "=" pattern' (Just VarP)
    unit = RecordP Blank Row.empty

binding :: Parser (Binding 'Parse)
binding = do
    f <-
        -- it should probably be `try (E.FunctionBinding <$> funcName) <*> NE.some patternParens
        -- for cleaner parse errors
        try (FunctionB <$> funcName <*> NE.some patternParens)
            <|> (ValueB <$> pattern')
    specialSymbol "="
    f <$> term
  where
    -- we might want to support infix operator declarations in the future
    -- > f $ x = f x
    funcName = operatorInParens <|> termName

-- an expression with infix operators and unresolved priorities
-- the `E.Infix` constructor is only used when there is more than one operator
-- function arrows are a special case that is handled directly in the parser
term :: Parser (Expr 'Parse)
term = do
    expr <- nonAnn
    option expr do
        specialSymbol ":"
        Annotation expr <$> term
  where
    -- second lowest level of precedence, 'anything but annotations'
    nonAnn = do
        firstExpr <- noPrec
        pairs <- many $ (,) <$> optional someOperator <*> noPrec
        let expr = case pairs of
                [] -> firstExpr
                [(Nothing, secondExpr)] -> firstExpr `App` secondExpr
                [(Just op, secondExpr)] -> Name op `App` firstExpr `App` secondExpr -- todo: a separate AST node for an infix application?
                (_ : _ : _) -> uncurry InfixE $ shift firstExpr pairs
        option expr do
            specialSymbol "->"
            rhs <- nonAnn
            pure $ Function (zipLocOf expr rhs) expr rhs
    -- type application precedence level
    typeApp = do
        expr <- termParens
        -- type applications bind tighther than anything else
        -- this might not work well with higher-than-application precedence operators, though
        apps <- many do
            void $ single '@'
            termParens
        pure $ foldl' TypeApp expr apps
    -- x [(+, y), (*, z), (+, w)] --> [(x, +), (y, *), (z, +)] w
    shift expr [] = ([], expr)
    shift lhs ((op, rhs) : rest) = first ((lhs, op) :) $ shift rhs rest
    noPrec = typeApp <|> keywordBased <|> termParens

    -- expression forms that have a leading keyword/symbol
    -- most of them also consume all trailing terms
    keywordBased =
        choice
            [ lambdaLike Lambda lambda pattern' "->" <*> term
            , lambdaLike Forall forallKeyword varBinder "." <*> term
            , lambdaLike Exists forallKeyword varBinder "." <*> term
            , withLoc $ letRecBlock (try $ keyword "let" *> keyword "rec") (flip3 LetRec) binding term
            , withLoc $ letBlock "let" (flip3 Let) binding term
            , case'
            , match'
            , if'
            , doBlock
            ]

case' :: Parser (Expr Parse)
case' = withLoc do
    keyword "case"
    arg <- term
    matches <- block "of" $ (,) <$> pattern' <* specialSymbol "->" <*> term
    pure $ flip3 Case arg matches

match' :: Parser (Expr Parse)
match' = withLoc $ flip Match <$> block "match" ((,) <$> some patternParens <* specialSymbol "->" <*> term)

if' :: Parser (Expr Parse)
if' = withLoc do
    keyword "if"
    cond <- term
    keyword "then"
    true <- term
    keyword "else"
    false <- term
    pure $ flip4 If cond true false

doBlock :: Parser (Expr Parse)
doBlock = withLoc do
    stmts <-
        block "do" $
            choice
                [ try $ Bind <$> pattern' <* specialSymbol "<-" <*> term
                , withLoc $ flip3 With <$ keyword "with" <*> pattern' <* specialSymbol "<-" <*> term
                , withLoc' DoLet $ keyword "let" *> binding
                , Action <$> term
                ]
    case unsnoc stmts of
        Nothing -> fail "empty do block"
        Just (stmts', Action lastAction) -> pure $ flip3 Do stmts' lastAction
        _ -> fail "last statement in a do block must be an expression"
  where
    unsnoc [] = Nothing
    unsnoc [x] = Just ([], x)
    unsnoc (x : xs) = first (x :) <$> unsnoc xs

-- a term that may be used as a type parameter or type application
-- that is, it does not contain any unparenthesized spaces
termParens :: Parser (Expr 'Parse)
termParens =
    choice
        [ record
        , recordType -- todo: ambiguity with empty record value
        , withLoc $ flip List <$> brackets (commaSep term)
        , variantType -- todo: ambiguity with empty list; unit sugar ambiguity
        , Name <$> operatorInParens
        , parens term
        , withLoc' RecordLens recordLens
        , constructor
        , Variant <$> variantConstructor
        , Literal <$> literal
        , Name <$> termName
        , typeVariable
        , parens term
        ]
  where
    variantItem = (,) <$> variantConstructor <*> option (Name $ Located Blank $ Name' "Unit") termParens
    record = withLoc $ flip Record <$> someRecord "=" term (Just Name)
    recordType = withLoc' RecordT $ NoExtRow <$> someRecord ":" term Nothing
    variantType = withLoc' VariantT $ NoExtRow <$> brackets (fromList <$> commaSep variantItem)
    constructor = lexeme do
        name <- constructorName
        optional record <&> \case
            Nothing -> Name name
            Just arg -> Name name `App` arg

flip3 :: (a -> b -> c -> d) -> b -> c -> a -> d
flip3 f y z x = f x y z

flip4 :: (a -> b -> c -> d -> e) -> b -> c -> d -> a -> e
flip4 f y z w x = f x y z w
