module Parser (code, declaration, type', pattern', expression) where

import Relude hiding (many, some)

import Lexer
import Syntax.All
import Syntax.Declaration qualified as D
import Syntax.Expression qualified as E
import Syntax.Pattern qualified as P
import Syntax.Type qualified as T

import Control.Monad.Combinators.Expr
import Control.Monad.Combinators.NonEmpty qualified as NE
import Data.HashMap.Strict qualified as Map
import Data.IntMap.Strict qualified as IntMap
import Text.Megaparsec

code :: Parser [Declaration Name]
code = topLevelBlock declaration

declaration :: Parser (Declaration Name)
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

    typePattern :: Parser (Name, [Type' Name])
    typePattern = do
        name <- typeName
        args <- many type'
        pure (name, args)

    signature :: Parser (Declaration Name)
    signature = do
        name <- termName
        specialSymbol ":"
        D.Signature name <$> type'

type' :: Parser (Type' Name)
type' = makeExprParser noPrec [[typeApp], [function], [forall', exists]]
  where
    noPrec =
        choice
            [ T.Name <$> typeName
            , T.Var <$> typeVariable
            , parens type'
            , T.Record <$> someRecord ":" type' Nothing
            , T.Variant <$> brackets (Map.fromList <$> commaSep variantItem)
            ]
      where
        variantItem = (,) <$> variantConstructor <*> noPrec

    forall' = Prefix $ lambdaLike T.Forall (keyword "forall") typeVariable "."
    exists = Prefix $ lambdaLike T.Exists (keyword "exists") typeVariable "."

    typeApp = InfixL $ pure T.Application
    function = InfixR $ T.Function <$ specialSymbol "->"

someRecord :: Text -> Parser value -> Maybe (Text -> value) -> Parser (HashMap Name value)
someRecord delim valueP missingValue = braces (Map.fromList <$> commaSep recordItem)
  where
    onMissing txt = case missingValue of
        Nothing -> id
        Just textToValue -> option (textToValue txt)
    recordItem = do
        recordLabel <- termName
        valuePattern <- onMissing recordLabel $ specialSymbol delim *> valueP
        pure (recordLabel, valuePattern)

lambdaLike :: (a -> b -> b) -> Parser () -> Parser a -> Text -> Parser (b -> b)
lambdaLike con kw arg endSym = do
    kw
    args <- NE.some arg
    specialSymbol endSym
    pure \body -> foldr con body args

pattern' :: Parser (Pattern Name)
pattern' = choice [nonTerminals, terminals, parens pattern']
  where
    nonTerminals =
        choice
            [ P.Constructor <$> typeName <*> many pattern'
            , P.Variant <$> variantConstructor <*> pattern'
            ]
    terminals =
        choice
            [ P.Var <$> termName
            , P.Record <$> someRecord "=" pattern' (Just P.Var)
            , P.List <$> brackets (commaSep pattern')
            , P.IntLiteral <$> intLiteral
            , P.TextLiteral <$> textLiteral
            , P.CharLiteral <$> charLiteral
            ]

binding :: Parser (Binding Name)
binding = do
    f <-
        try (E.FunctionBinding <$> termName <*> NE.some pattern')
            <|> (E.ValueBinding <$> pattern')
    specialSymbol "="
    f <$> expression

expression :: Parser (Expression Name)
expression = makeExprParser noPrec (snd <$> IntMap.toDescList precMap)
  where
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

    noPrec = choice $ keywordBased <> terminals

    keywordBased =
        [ lambdaLike E.Lambda lambda pattern' "->" <*> expression
        , let'
        , case'
        , match'
        , E.If <$ keyword "if" <*> expression <* keyword "then" <*> expression <* keyword "else" <*> expression
        , E.Record <$> someRecord "=" expression (Just E.Name)
        , E.List <$> brackets (commaSep expression)
        ]
      where
        let' = do
            letBlock "let" E.Let binding expression
        case' = do
            keyword "case"
            arg <- expression
            matches <- block "of" $ (,) <$> pattern' <* specialSymbol "->" <*> expression
            pure $ E.Case arg matches
        match' = E.Match <$> block "match" ((,) <$> some pattern' <* specialSymbol "->" <*> expression)

    terminals =
        [ parens expression
        , E.Name <$> termName
        , E.RecordLens <$> recordLens
        , E.Constructor <$> typeName
        , E.Variant <$> variantConstructor
        , E.IntLiteral <$> intLiteral
        , E.CharLiteral <$> charLiteral
        , E.TextLiteral <$> textLiteral
        ]