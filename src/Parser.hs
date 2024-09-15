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
import Text.Megaparsec
import Syntax.Row

code :: Parser [Declaration Text]
code = topLevelBlock declaration

declaration :: Parser (Declaration Text)
declaration = choice [typeDec, valueDec, signature]
  where
    valueDec = try $ D.Value <$> binding <*> whereBlock
    whereBlock = option [] $ block "where" valueDec

    typeDec = keyword "type" *> (typeAliasDec <|> typeDec')
    typeAliasDec = do
        keyword "alias"
        name <- typeName
        specialSymbol "="
        D.Alias name <$> type'

    typeDec' = do
        name <- typeName
        vars <- many typeVariable -- placeholder
        D.Type name vars <$> (typePattern `sepBy` specialSymbol "|")

    typePattern :: Parser (Text, [Type' Text])
    typePattern = do
        name <- typeName
        args <- many type'
        pure (name, args)

    signature :: Parser (Declaration Text)
    signature = do
        name <- termName
        specialSymbol ":"
        D.Signature name <$> type'

type' :: ParserM m => m (Type' Text)
type' = makeExprParser noPrec [[typeApp], [function], [forall', exists]]
  where
    noPrec =
        choice
            [ T.Name <$> typeName
            , T.Var <$> typeVariable
            , parens type'
            , T.Record . NoExtRow <$> someRecord ":" type' Nothing
            , T.Variant . NoExtRow <$> brackets (fromList <$> commaSep variantItem)
            ]
      where
        variantItem = (,) <$> variantConstructor <*> option (T.Name "Unit") noPrec

    forall' = Prefix $ lambdaLike T.Forall (keyword "forall") typeVariable "."
    exists = Prefix $ lambdaLike T.Exists (keyword "exists") typeVariable "."

    typeApp = InfixL $ pure T.Application
    function = InfixR $ T.Function <$ specialSymbol "->"

someRecord :: ParserM m => Text -> m value -> Maybe (Text -> value) -> m (Row value)
someRecord delim valueP missingValue = braces (fromList <$> commaSep recordItem)
  where
    onMissing txt = case missingValue of
        Nothing -> id
        Just textToValue -> option (textToValue txt)
    recordItem = do
        recordLabel <- termName
        valuePattern <- onMissing recordLabel $ specialSymbol delim *> valueP
        pure (recordLabel, valuePattern)

lambdaLike :: ParserM m => (a -> b -> b) -> m () -> m a -> Text -> m (b -> b)
lambdaLike con kw arg endSym = do
    kw
    args <- NE.some arg
    specialSymbol endSym
    pure \body -> foldr con body args

pattern' :: ParserM m => m (Pattern Text)
pattern' =
    choice
        [ P.Constructor <$> typeName <*> many patternParens
        , P.Variant <$> variantConstructor <*> patternParens
        , patternParens
        ]

{- | parses a pattern with constructors enclosed in parens
should be used in cases where multiple patterns in a row are accepted, i.e.
function definitions and match expressions
-}
patternParens :: ParserM m => m (Pattern Text)
patternParens =
    choice
        [ P.Var <$> termName
        , P.Record <$> someRecord "=" pattern' (Just P.Var)
        , P.List <$> brackets (commaSep pattern')
        , P.IntLiteral <$> intLiteral
        , P.TextLiteral <$> textLiteral
        , P.CharLiteral <$> charLiteral
        , P.Constructor <$> typeName <*> pure [] -- a constructor without arguments
        , P.Variant <$> variantConstructor <*> pure unit -- some sugar for variants with a unit payload
        , parens pattern'
        ]
    where unit = P.Constructor "Unit" []

binding :: ParserM m => m (Binding Text)
binding = do
    f <-
        -- it should probably be `try (E.FunctionBinding <$> termName) <*> NE.some patternParens
        -- for cleaner parse errors
        try (E.FunctionBinding <$> termName <*> NE.some patternParens)
            <|> (E.ValueBinding <$> pattern')
    specialSymbol "="
    f <$> expression

expression :: ParserM m => m (Expression Text)
expression = expression' OuterScope

data LambdaScope = OuterScope | NewScope

expression' :: ParserM m => LambdaScope -> m (Expression Text)
expression' scope = case scope of
    NewScope -> withWildcards scopedExpr
    OuterScope -> makeExprParser (noPrec $ E.Name <$> termName) (snd <$> IntMap.toDescList precMap)
  where
    scopedExpr :: ParserM m => StateT Int m (Expression Text)
    scopedExpr = makeExprParser (noPrec wildcardOrVar) (snd <$> IntMap.toDescList precMap)

    precMap :: ParserM m => IntMap [Operator m (Expression Text)]
    precMap =
        IntMap.fromList
            [ (120, [infixR "."]) -- lens composition
            , (110, infixL <$> ["^.", "^..", "^?"]) -- lens getters (subject to change)
            , (100, [InfixL $ pure E.Application])
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
        annotation = Postfix do
            specialSymbol ":"
            ty <- type'
            pure (`E.Annotation` ty)

        infixL = infix' InfixL
        infixR = infix' InfixR
        infixN = infix' InfixN
        infix' fixity sym = fixity $ operator sym $> \lhs rhs -> E.Name sym `E.Application` lhs `E.Application` rhs

    noPrec varParser = choice $ keywordBased <> terminals varParser

    keywordBased :: ParserM m => [m (Expression Text)]
    keywordBased =
        [ lambdaLike E.Lambda lambda pattern' "->" <*> expression
        , let'
        , case'
        , match'
        , E.If <$ keyword "if" <*> expression <* keyword "then" <*> expression <* keyword "else" <*> expression
        , withWildcards $ E.Record <$> someRecord "=" scopedExpr (Just E.Name)
        , withWildcards $ E.List <$> brackets (commaSep scopedExpr)
        ]
      where
        let' = do
            letBlock "let" E.Let binding expression
        case' = do
            keyword "case"
            arg <- expression
            matches <- block "of" $ (,) <$> pattern' <* specialSymbol "->" <*> expression
            pure $ E.Case arg matches
        match' = E.Match <$> block "match" ((,) <$> some patternParens <* specialSymbol "->" <*> expression)

    -- todo: better error messages for out-of-scope wildcards
    wildcardOrVar :: ParserM m => StateT Int m (Expression Text)
    wildcardOrVar = do
        name <- termName
        if name == "_"
            then nextVar
            else pure $ E.Name name

    terminals varParser =
        [ parens $ expression' NewScope
        , varParser
        , E.RecordLens <$> recordLens
        , E.Constructor <$> typeName
        , E.Variant <$> variantConstructor
        , E.IntLiteral <$> intLiteral
        , E.CharLiteral <$> charLiteral
        , E.TextLiteral <$> textLiteral
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
withWildcards :: Monad m => StateT Int m (Expression Text) -> m (Expression Text)
withWildcards p = do
    (expr, varCount) <- runStateT p 0
    pure $ foldr (\i -> E.Lambda (P.Var $ "$" <> show i)) expr [1..varCount]

nextVar :: MonadParsec Void Text m => StateT Int m (Expression Text)
nextVar = do
    modify succ
    i <- get
    pure $ E.Name $ "$" <> show i