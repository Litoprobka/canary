{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use <$>" #-}
module Parser (code, declaration, type', pattern', expression) where

import Relude hiding (many, some)

import Lexer
import Syntax
import Syntax.Declaration qualified as D
import Syntax.Expression qualified as E
import Syntax.Pattern qualified as P
import Syntax.Type qualified as T

import Control.Monad.Combinators.Expr
import Control.Monad.Combinators.NonEmpty qualified as NE

import CheckerTypes (Loc (..), SimpleName (..), getLoc, zipLoc)
import Data.IntMap.Strict qualified as IntMap
import Syntax.Row
import Syntax.Row qualified as Row
import Text.Megaparsec
import qualified Data.List.NonEmpty as NE

code :: Parser [Declaration SimpleName]
code = topLevelBlock declaration

declaration :: Parser (Declaration SimpleName)
declaration = withLoc $ choice [typeDec, valueDec, signature]
  where
    valueDec = flip3 D.Value <$> binding <*> whereBlock
    whereBlock = option [] $ block "where" (withLoc valueDec)

    typeDec = keyword "type" *> (typeAliasDec <|> typeDec')
    typeAliasDec = do
        keyword "alias"
        name <- typeName
        specialSymbol "="
        flip3 D.Alias name <$> type'

    typeDec' = do
        name <- typeName
        vars <- many typeVariable -- placeholder
        specialSymbol "="
        flip4 D.Type name vars <$> typePattern `sepBy` specialSymbol "|"

    typePattern :: Parser (Constructor SimpleName)
    typePattern = withLoc do
        name <- typeName
        args <- many typeParens
        pure $ flip3 D.Constructor name args

    signature :: Parser (Loc -> Declaration SimpleName)
    signature = do
        name <- termName
        specialSymbol ":"
        flip3 D.Signature name <$> type'

type' :: ParserM m => m (Type' SimpleName)
type' = makeExprParser typeParens [[typeApp], [function], [forall', exists]]
  where
    forall' = Prefix $ lambdaLike T.Forall forallKeyword typeVariable "."
    exists = Prefix $ lambdaLike T.Exists existsKeyword typeVariable "."

    typeApp = InfixL $ pure $ appLoc T.Application
    function = InfixR $ appLoc T.Function <$ specialSymbol "->"
    appLoc con lhs rhs = con (zipLoc (getLoc lhs) (getLoc rhs)) lhs rhs

-- a type expression with higher precedence than application
-- used when parsing constructor arguement types and the like
typeParens :: ParserM m => m (Type' SimpleName)
typeParens =
    choice
        [ T.Name <$> typeName
        , T.Var <$> typeVariable
        , parens type'
        , withLoc' T.Record $ NoExtRow <$> someRecord ":" type' Nothing
        , withLoc' T.Variant $ NoExtRow <$> brackets (fromList <$> commaSep variantItem)
        ]
  where
    variantItem = (,) <$> variantConstructor <*> option (T.Name $ SimpleName Blank "Unit") typeParens

someRecord :: ParserM m => Text -> m value -> Maybe (SimpleName -> value) -> m (Row value)
someRecord delim valueP missingValue = braces (fromList <$> commaSep recordItem)
  where
    onMissing name = case missingValue of
        Nothing -> id
        Just nameToValue -> option (nameToValue name)
    recordItem = do
        recordLabel <- termName
        valuePattern <- onMissing recordLabel $ specialSymbol delim *> valueP
        pure (recordLabel, valuePattern)

lambdaLike :: ParserM m => (Loc -> a -> b -> b) -> m () -> m a -> Text -> m (b -> b)
lambdaLike con kw argP endSym = do
    kw
    args <- NE.some $ (,) <$> getSourcePos <*> argP
    specialSymbol endSym
    end <- getSourcePos
    pure \body -> foldr (\(start, arg) -> con (Loc start end) arg) body args

pattern' :: ParserM m => m (Pattern SimpleName)
pattern' = do
    pat <-
        choice
            [ withLoc $ flip3 P.Constructor <$> typeName <*> many patternParens
            , withLoc $ flip3 P.Variant <$> variantConstructor <*> patternParens
            , patternParens
            ]
    option pat $ withLoc do
        specialSymbol ":"
        flip3 P.Annotation pat <$> type'

{- | parses a pattern with constructors enclosed in parens
should be used in cases where multiple patterns in a row are accepted, i.e.
function definitions and match expressions
-}
patternParens :: ParserM m => m (Pattern SimpleName)
patternParens =
    choice
        [ P.Var <$> termName
        , withLoc' P.Record $ someRecord "=" pattern' (Just P.Var)
        , withLoc' P.List $ brackets (commaSep pattern')
        , withLoc' P.IntLiteral intLiteral
        , withLoc' P.TextLiteral textLiteral
        , withLoc' P.CharLiteral charLiteral
        , withLoc $ flip3 P.Constructor <$> typeName <*> pure [] -- a constructor without arguments
        , withLoc $ flip3 P.Variant <$> variantConstructor <*> pure unit -- some sugar for variants with a unit payload
        , parens pattern'
        ]
  where
    unit = P.Record Blank Row.empty

binding :: ParserM m => m (Binding SimpleName)
binding = withLoc do
    f <-
        -- it should probably be `try (E.FunctionBinding <$> termName) <*> NE.some patternParens
        -- for cleaner parse errors
        try (flip4 E.FunctionBinding <$> termName <*> NE.some patternParens)
            <|> (flip3 E.ValueBinding <$> pattern')
    specialSymbol "="
    f <$> expression

expression :: ParserM m => m (Expression SimpleName)
expression = expression' $ E.Name <$> nonWildcardTerm

expression' :: ParserM m => m (Expression SimpleName) -> m (Expression SimpleName)
expression' termParser = label "expression" $ makeExprParser (noPrec termParser) [[annotation]]
  where
    sameScopeExpr = expression' termParser

    newScopeExpr :: ParserM m => StateT Int m (Expression SimpleName)
    newScopeExpr =
        expression' $
            withLoc (nextVar <* wildcard)
                <|> fmap E.Name termName

    annotation = Postfix $ withLoc do
        specialSymbol ":"
        ty <- type'
        pure \loc expr -> E.Annotation loc expr ty

    noPrec varParser = choice $ keywordBased <> terminals varParser

    keywordBased =
        [ lambdaLike E.Lambda lambda pattern' "->" <*> sameScopeExpr
        , let'
        , case'
        , match'
        , if'
        , withWildcards $ withLoc $ flip E.Record <$> someRecord "=" newScopeExpr (Just E.Name)
        , withWildcards $ withLoc $ flip E.List <$> brackets (commaSep newScopeExpr)
        ]
      where
        let' =
            withLoc $
                letBlock "let" (flip3 E.Let) binding sameScopeExpr
        case' = withLoc do
            keyword "case"
            arg <- sameScopeExpr
            matches <- block "of" $ (,) <$> pattern' <* specialSymbol "->" <*> sameScopeExpr
            pure $ flip3 E.Case arg matches
        match' = withLoc $ flip E.Match <$> block "match" ((,) <$> some patternParens <* specialSymbol "->" <*> sameScopeExpr)
        if' = withLoc do
            keyword "if"
            cond <- sameScopeExpr
            keyword "then"
            true <- sameScopeExpr
            keyword "else"
            false <- sameScopeExpr
            pure $ flip4 E.If cond true false

    terminals :: ParserM m => m (Expression SimpleName) -> [m (Expression SimpleName)]
    terminals varParser =
        [ parens $ withWildcards newScopeExpr
        , withLoc' E.RecordLens recordLens
        , E.Constructor <$> typeName
        , E.Variant <$> variantConstructor
        , withLoc' E.IntLiteral intLiteral
        , withLoc' E.CharLiteral charLiteral
        , withLoc' E.TextLiteral textLiteral
        , varParser
        ]

    infixExpr varParser = do
        firstExpr <- noPrec varParser
        pairs <- many $ (,) <$> option (SimpleName Blank "app") someOperator <*> noPrec varParser
        pure $ uncurry E.Infix $ shift firstExpr pairs
      where
        -- x [(+, y), (*, z), (+, w)] --> [(x, +), (y, *), (z, +)] w
        shift expr [] = ([], expr)
        shift lhs ((op, rhs) : rest) = first ((lhs, op) :) $ shift rhs rest

        
            

-- turns out that respecting operator precedence makes for confusing code
-- i.e. consider, say, `3 + _ * 4`
-- with precendence, it should be parsed as `3 + (\x -> x * 4)`
-- but what you probably mean is `\x -> 3 + x * 4`
--
-- in the end, I decided to go with the simples rules possible - that is, parens determine
-- the scope of the implicit lambda
--
-- it's not clear whether I want to require parens around list and record literals
-- on one hand, `({x = 3, y = 3})` looks a bit janky
-- on the other hand, without that you wouldn't be able to write `f {x = 3, y = _}`
-- if you want it to mean `\y -> f {x = 3, y}`
withWildcards :: ParserM m => StateT Int m (Expression SimpleName) -> m (Expression SimpleName)
withWildcards p = do
    -- todo: collect a list of var names along with the counter
    ((expr, varCount), loc) <- withLoc $ (,) <$> runStateT p 0
    pure $ foldr (\i -> E.Lambda loc (P.Var $ SimpleName Blank $ "$" <> show i)) expr [1 .. varCount]

nextVar :: MonadParsec Void Text m => StateT Int m (Loc -> Expression SimpleName)
nextVar = do
    modify succ
    i <- get
    pure \loc -> E.Name $ SimpleName loc $ "$" <> show i

flip3 :: (a -> b -> c -> d) -> b -> c -> a -> d
flip3 f y z x = f x y z

flip4 :: (a -> b -> c -> d -> e) -> b -> c -> d -> a -> e
flip4 f y z w x = f x y z w