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

import Data.IntMap.Strict qualified as IntMap
import Syntax.Row
import Syntax.Row qualified as Row
import Text.Megaparsec

code :: Parser [Declaration Text]
code = topLevelBlock declaration

declaration :: Parser (Declaration Text)
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

    typePattern :: Parser (Constructor Text)
    typePattern = withLoc do
        name <- typeName
        args <- many typeParens
        pure $ flip3 D.Constructor name args

    signature :: Parser (T.Loc -> Declaration Text)
    signature = do
        name <- termName
        specialSymbol ":"
        flip3 D.Signature name <$> type'

type' :: ParserM m => m (Type' Text)
type' = makeExprParser typeParens [[typeApp], [function], [forall', exists]]
  where
    forall' = Prefix $ lambdaLike T.Forall forallKeyword typeVariable "."
    exists = Prefix $ lambdaLike T.Exists existsKeyword typeVariable "."

    typeApp = InfixL $ pure $ appLoc T.Application
    function = InfixR $ appLoc T.Function <$ specialSymbol "->"
    appLoc con lhs rhs = con (zipLoc (T.getLoc lhs) (T.getLoc rhs)) lhs rhs

-- a type expression with higher precedence than application
-- used when parsing constructor arguement types and the like
typeParens :: ParserM m => m (Type' Text)
typeParens =
    choice
        [ withLoc $ flip T.Name <$> typeName
        , withLoc $ flip T.Var <$> typeVariable
        , parens type'
        , withLoc $ flip T.Record . NoExtRow <$> someRecord ":" type' Nothing
        , withLoc $ flip T.Variant . NoExtRow <$> brackets (fromList <$> commaSep variantItem)
        ]
  where
    variantItem = (,) <$> variantConstructor <*> option (T.Name T.Blank "Unit") typeParens

someRecord :: ParserM m => Text -> m value -> Maybe (T.Loc -> Text -> value) -> m (Row value)
someRecord delim valueP missingValue = braces (fromList <$> commaSep recordItem)
  where
    onMissing loc txt = case missingValue of
        Nothing -> id
        Just textToValue -> option (textToValue loc txt)
    recordItem = do
        (recordLabel, loc) <- withLoc $ (,) <$> termName
        valuePattern <- onMissing loc recordLabel $ specialSymbol delim *> valueP
        pure (recordLabel, valuePattern)

lambdaLike :: ParserM m => (T.Loc -> a -> b -> b) -> m () -> m a -> Text -> m (b -> b)
lambdaLike con kw argP endSym = do
    kw
    args <- NE.some $ (,) <$> getSourcePos <*> argP
    specialSymbol endSym
    end <- getSourcePos
    pure \body -> foldr (\(start, arg) -> con (T.Loc start end) arg) body args

pattern' :: ParserM m => m (Pattern Text)
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
patternParens :: ParserM m => m (Pattern Text)
patternParens =
    choice
        [ withLoc $ flip P.Var <$> termName
        , withLoc $ flip P.Record <$> someRecord "=" pattern' (Just P.Var)
        , withLoc $ flip P.List <$> brackets (commaSep pattern')
        , withLoc $ flip P.IntLiteral <$> intLiteral
        , withLoc $ flip P.TextLiteral <$> textLiteral
        , withLoc $ flip P.CharLiteral <$> charLiteral
        , withLoc $ flip3 P.Constructor <$> typeName <*> pure [] -- a constructor without arguments
        , withLoc $ flip3 P.Variant <$> variantConstructor <*> pure unit -- some sugar for variants with a unit payload
        , parens pattern'
        ]
  where
    unit = P.Record T.Blank Row.empty

binding :: ParserM m => m (Binding Text)
binding = withLoc do
    f <-
        -- it should probably be `try (E.FunctionBinding <$> termName) <*> NE.some patternParens
        -- for cleaner parse errors
        try (flip4 E.FunctionBinding <$> termName <*> NE.some patternParens)
            <|> (flip3 E.ValueBinding <$> pattern')
    specialSymbol "="
    f <$> expression

expression :: ParserM m => m (Expression Text)
expression = expression' $ withLoc (flip E.Name <$> nonWildcardTerm)

expression' :: ParserM m => m (Expression Text) -> m (Expression Text)
expression' termParser = label "expression" $ makeExprParser (noPrec termParser) (snd <$> IntMap.toDescList precMap)
  where
    sameScopeExpr = expression' termParser

    newScopeExpr :: ParserM m => StateT Int m (Expression Text)
    newScopeExpr =
        expression' $ withLoc $
            nextVar <* wildcard <|> (flip E.Name <$> termName)

    precMap =
        IntMap.fromList
            [ (120, [infixR "."]) -- lens composition
            , (110, infixL <$> ["^.", "^..", "^?"]) -- lens getters (subject to change)
            , (100, [InfixL $ pure appLoc])
            , (90, [infixL ">>", infixR "<<"]) -- function composition
            , (80, [infixR "^"])
            , (70, infixL <$> ["*", "/"])
            , (60, map infixL ["+", "-"] <> [infixR "<>"])
            , (50, infixR <$> [".~", "%~", "?~"]) -- lens setters (subject to change)
            , (40, infixN <$> ["==", "!=", ">", ">=", "<", "<="])
            , (30, [infixR "&&"])
            , (20, [infixR "||"])
            , (0, [infixL "|>", infixR "<|"]) -- pipes
            , (-100, [annotation]) -- I can't think of anything that should have lower precedence than annotation
            ]
      where
        annotation = Postfix $ withLoc do
            specialSymbol ":"
            ty <- type'
            pure \loc expr -> E.Annotation loc expr ty

        appLoc lhs rhs = E.Application (zipLoc (E.getLoc lhs) (E.getLoc rhs)) lhs rhs
        infixL = infix' InfixL
        infixR = infix' InfixR
        infixN = infix' InfixN
        infix' fixity sym = fixity do
            opLoc <- withLoc $ (\ _ x -> x) <$> operator sym
            pure \lhs rhs -> E.Name opLoc sym `appLoc` lhs `appLoc` rhs

    noPrec varParser = choice $ keywordBased <> terminals varParser

    -- anyOperator = choice $ operator <$> [".", "^.", "^..", "^?", ">>", "<<", "^", "*", "/", "+", "-", "<>", ".~", "%~", "?~", "==", "!=", ">", ">=", "<", "<=", "&&", "||", "|>", "<|"]
    -- this is a bit of an ad-hoc solution for the case where `let x = y; x == z == w` gets parsed as `(let x = y; x == z) == w`
    keywordBased =
        (<* notFollowedBy someOperator)
            <$> [ lambdaLike E.Lambda lambda pattern' "->" <*> sameScopeExpr
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

    terminals :: ParserM m => m (Expression Text) -> [m (Expression Text)]
    terminals varParser =
        [ parens $ withWildcards newScopeExpr
        , withLoc $ flip E.RecordLens <$> recordLens
        , withLoc $ flip E.Constructor <$> typeName
        , withLoc $ flip E.Variant <$> variantConstructor
        , withLoc $ flip E.IntLiteral <$> intLiteral
        , withLoc $ flip E.CharLiteral <$> charLiteral
        , withLoc $ flip E.TextLiteral <$> textLiteral
        , varParser
        ]

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
withWildcards :: ParserM m => StateT Int m (Expression Text) -> m (Expression Text)
withWildcards p = do
    ((expr, varCount), loc) <- withLoc $ (,) <$> runStateT p 0
    pure $ foldr (\i -> E.Lambda loc (P.Var T.Blank $ "$" <> show i)) expr [1 .. varCount]

zipLoc :: T.Loc -> T.Loc -> T.Loc
zipLoc loc T.Blank = loc
zipLoc T.Blank loc = loc
zipLoc (T.Loc start _) (T.Loc _ end) = T.Loc start end

nextVar :: MonadParsec Void Text m => StateT Int m (T.Loc -> Expression Text)
nextVar = do
    modify succ
    i <- get
    pure \loc -> E.Name loc $ "$" <> show i

flip3 :: (a -> b -> c -> d) -> b -> c -> a -> d
flip3 f y z x = f x y z

flip4 :: (a -> b -> c -> d -> e) -> b -> c -> d -> a -> e
flip4 f y z w x = f x y z w