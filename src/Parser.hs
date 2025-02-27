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
    getLoc,
    unLoc,
    zipLocOf,
    pattern L,
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
declaration = located $ choice [typeDec, fixityDec, signature, valueDec]
  where
    valueDec = D.Value <$> binding <*> whereBlock
    whereBlock = option [] $ block "where" (located valueDec)

    typeDec = do
        keyword "type"
        name <- typeName
        simpleTypeDec name <|> gadtDec name

    simpleTypeDec name = do
        vars <- many varBinder
        specialSymbol "="
        D.Type name vars <$> typePattern `sepBy` specialSymbol "|"

    gadtDec :: SimpleName -> Parser (Declaration_ 'Parse)
    gadtDec name = do
        mbKind <- optional $ specialSymbol ":" *> term
        constrs <- block "where" $ withLoc do
            con <- typeName
            specialSymbol ":"
            sig <- term
            pure \loc -> D.GadtConstructor loc con sig
        pure $ D.GADT name mbKind constrs

    typePattern :: Parser (Constructor 'Parse)
    typePattern = withLoc do
        name <- typeName
        args <- many termParens
        pure \loc -> D.Constructor loc name args

    signature = do
        name <- try $ (operatorInParens <|> termName) <* specialSymbol ":"
        D.Signature name <$> term

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
        pure $ D.Fixity fixity op PriorityRelation{above, below, equal}

varBinder :: Parser (VarBinder 'Parse)
varBinder =
    parens (VarBinder <$> termName <* specialSymbol ":" <*> fmap Just term)
        <|> flip VarBinder Nothing
        <$> termName

typeVariable :: Parser (Type_ 'Parse)
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

lambda' :: Parser (Expr 'Parse)
lambda' = withLoc do
    lambda
    args <- NE.some patternParens
    specialSymbol "->"
    body <- term
    pure \loc -> foldr (\var -> Located loc . Lambda var) body args

quantifier :: Parser (Type 'Parse)
quantifier = withLoc do
    (q, erased) <- choice
        [ (Forall, Erased) <$ forallKeyword 
        , (Exists, Erased) <$ existsKeyword
        , (Forall, Retained) <$ piKeyword
        , (Exists, Retained) <$ sigmaKeyword
        ]
    binders <- NE.some varBinder
    let arrOrStar = specialSymbol case q of
         Forall -> "->"
         Exists -> "**"
    visibility <- Implicit <$ specialSymbol "." <|> Visible <$ arrOrStar
    body <- term
    pure \loc -> foldr (\binder acc -> Located loc $ Q q visibility erased binder acc) body binders
  

pattern' :: Parser (Pattern 'Parse)
pattern' =
    choice
        [ located $ ConstructorP <$> typeName <*> many patternParens
        , located $ VariantP <$> variantConstructor <*> patternParens
        , patternParens
        ]

{- | parses a pattern with constructors enclosed in parens
should be used in cases where multiple patterns in a row are accepted, i.e.
function definitions and match expressions
-}
patternParens :: Parser (Pattern 'Parse)
patternParens = located do
    pat <- located . choice $
            [ VarP <$> termName
            , lexeme $ WildcardP <$> string "_" <* option "" termName'
            , record
            , ListP <$> brackets (commaSep pattern')
            , LiteralP <$> literal
            , -- a constructor without arguments or with a tightly-bound record pattern
              lexeme $ ConstructorP <$> constructorName <*> option [] (one <$> located record)
            , flip VariantP unit <$> variantConstructor -- some sugar for variants with a unit payload
            , unLoc <$> parens pattern'
            ]
    option (unLoc pat) do
        specialSymbol ":"
        AnnotationP pat <$> term
  where
    record = RecordP <$> someRecord "=" pattern' (Just $ \n -> Located (getLoc n) $ VarP n)
    unit = Located Blank $ RecordP Row.empty

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
term = located do
    expr <- nonAnn
    option (unLoc expr) do
        specialSymbol ":"
        Annotation expr <$> term
  where
    -- second lowest level of precedence, 'anything but annotations'
    nonAnn :: Parser (Expr 'Parse)
    nonAnn = located do
        (Located loc (firstExpr, pairs)) <- located do
            firstExpr <- noPrec
            pairs <- many $ (,) <$> optional someOperator <*> noPrec
            pure (firstExpr, pairs)
        let expr = case pairs of
                [] -> unLoc firstExpr
                [(Nothing, secondExpr)] -> firstExpr `App` secondExpr
                [(Just op, secondExpr)] -> Located (zipLocOf firstExpr op) (Located (getLoc op) (Name op) `App` firstExpr) `App` secondExpr -- todo: a separate AST node for an infix application?
                (_ : _ : _) -> uncurry InfixE $ shift firstExpr pairs
        option expr do
            specialSymbol "->"
            rhs <- nonAnn
            pure $ Function (Located loc expr) rhs
    -- type application precedence level
    typeApp = do
        expr <- termParens
        -- type applications bind tighther than anything else
        -- this might not work well with higher-than-application precedence operators, though
        apps <- many do
            void $ single '@'
            termParens
        pure $ foldl' (\e app -> Located (zipLocOf e app) $ TypeApp e app) expr apps
    -- x [(+, y), (*, z), (+, w)] --> [(x, +), (y, *), (z, +)] w
    shift expr [] = ([], expr)
    shift lhs ((op, rhs) : rest) = first ((lhs, op) :) $ shift rhs rest
    noPrec = typeApp <|> keywordBased <|> termParens

    -- expression forms that have a leading keyword/symbol
    -- most of them also consume all trailing terms
    keywordBased :: Parser (Term 'Parse)
    keywordBased =
        located $
            choice
                [ unLoc <$> lambda'
                , unLoc <$> quantifier
                , letRecBlock (try $ keyword "let" *> keyword "rec") LetRec binding term
                , letBlock "let" Let binding term
                , case'
                , match'
                , if'
                , doBlock
                ]

case' :: Parser (Expr_ Parse)
case' = do
    keyword "case"
    arg <- term
    matches <- block "of" $ (,) <$> pattern' <* specialSymbol "->" <*> term
    pure $ Case arg matches

match' :: Parser (Expr_ Parse)
match' = Match <$> block "match" ((,) <$> some patternParens <* specialSymbol "->" <*> term)

if' :: Parser (Expr_ Parse)
if' = do
    keyword "if"
    cond <- term
    keyword "then"
    true <- term
    keyword "else"
    false <- term
    pure $ If cond true false

doBlock :: Parser (Expr_ Parse)
doBlock = do
    stmts <-
        block "do" . located . choice $
            [ try $ Bind <$> pattern' <* specialSymbol "<-" <*> term
            , With <$ keyword "with" <*> pattern' <* specialSymbol "<-" <*> term
            , keyword "let" *> fmap DoLet binding
            , Action <$> term
            ]
    case unsnoc stmts of
        Nothing -> fail "empty do block"
        Just (stmts', L (Action lastAction)) -> pure $ Do stmts' lastAction
        _ -> fail "last statement in a do block must be an expression"
  where
    unsnoc [] = Nothing
    unsnoc [x] = Just ([], x)
    unsnoc (x : xs) = first (x :) <$> unsnoc xs

-- a term that may be used as a type parameter or type application
-- that is, it does not contain any unparenthesized spaces
termParens :: Parser (Expr 'Parse)
termParens =
    located $
        choice
            [ record
            , recordType -- todo: ambiguity with empty record value
            , List <$> brackets (commaSep term)
            , variantType -- todo: ambiguity with empty list; unit sugar ambiguity
            , Name <$> operatorInParens
            , parens $ unLoc <$> term
            , RecordLens <$> recordLens
            , constructor
            , Variant <$> variantConstructor
            , Literal <$> literal
            , Name <$> termName
            , typeVariable
            ]
  where
    variantItem = (,) <$> variantConstructor <*> option (Located Blank $ RecordT $ NoExtRow Row.empty) termParens
    record = Record <$> someRecord "=" term (Just $ \n -> Located (getLoc n) $ Name n)
    recordType = RecordT . NoExtRow <$> someRecord ":" term Nothing
    variantType = VariantT . NoExtRow <$> brackets (fromList <$> commaSep variantItem)
    constructor = lexeme do
        name <- constructorName
        optional (located record) <&> \case
            Nothing -> Name name
            Just arg -> Located (getLoc name) (Name name) `App` arg
