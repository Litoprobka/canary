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
    valueDec = D.Value <$> termName <*> many pattern' <* specialSymbol "=" <*> expression <*> whereBlock
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
type' = prec [const [forall', exists], typeApp, recordOrVariant] terminal
  where
    terminal =
        [ T.Name <$> typeName
        , T.Var <$> typeVariable
        ]
    forall' = do
        keyword "forall" -- todo: unicode
        T.Forall <$> some typeVariable <* specialSymbol "." <*> type'

    exists = do
        keyword "exists"
        T.Exists <$> some typeVariable <* specialSymbol "." <*> type'

    typeApp higherPrec = one $ try $ T.Application <$> higherPrec <*> NE.some higherPrec
    recordOrVariant hp =
        [ T.Record <$> someRecord ":" type'
        , T.Variant <$> brackets (Map.fromList <$> commaSep variantItem)
        ]
      where
        variantItem = (,) <$> variantConstructor <*> many (prec [recordOrVariant] [hp])

someRecord :: Text -> Parser value -> Parser (HashMap Name value)
someRecord delim valueP = braces (Map.fromList <$> commaSep recordItem)
  where
    recordItem = do
        recordLabel <- termName
        specialSymbol delim
        valuePattern <- valueP
        pure (recordLabel, valuePattern)

pattern' :: Parser (Pattern Name)
pattern' = prec [nonTerminals] terminals
  where
    nonTerminals hp =
        [ P.Constructor <$> typeName <*> many hp
        , P.Variant <$> variantConstructor <*> many hp
        ]
    terminals =
        [ P.Var <$> termName
        , P.Record <$> someRecord "=" pattern'
        , P.List <$> brackets (commaSep pattern')
        , P.IntLiteral <$> intLiteral
        , P.TextLiteral <$> textLiteral
        , P.CharLiteral <$> charLiteral
        ]

{- | given a list of recursive parsers in precedence groups (lowest to highest) and a list of terminals, produces a
| parser that parses all options with parentheses where needed
-}
prec :: [Parser a -> [Parser a]] -> [Parser a] -> Parser a
prec initPs terminals = go initPs
  where
    go [] = parens (prec initPs terminals) <|> choice terminals
    go (pgroup : groups) = choice (pgroup higherPrec) <|> higherPrec
      where
        higherPrec = go groups

expression :: Parser (Expression Name)
expression = makeExprParser noPrec (snd <$> IntMap.toDescList precMap)
  where
    precMap =
        IntMap.fromList
            [ (120, [infixR "."]) -- lens composition
            , (110, infixL <$> ["^.", "^..", "^?"]) -- lens getters (subject to change)
            , (100, [application])
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
        -- I'm not sure whether multi-arg applications are a good idea at all
        -- there's no clean way to parse it via `makeExprParser`, so I'm relying on
        -- the `binApp` function that normalises instead
        application = InfixL $ pure binApp

        annotation = Postfix do
            specialSymbol ":"
            ty <- type'
            pure (`E.Annotation` ty)

        infixL = infix' InfixL
        infixR = infix' InfixR
        infixN = infix' InfixN
        infix' fixity sym = fixity $ operator sym $> \lhs rhs -> binApp (binApp (E.Name sym) lhs) rhs

        -- E.Application that merges with the lhs if possible
        -- i.e. f `binApp` x `binApp` y is E.Application f [x, y]
        -- rather than E.Application (E.Application f [x]) [y]
        binApp :: Expression n -> Expression n -> Expression n
        binApp lhs rhs = case lhs of
            E.Application f args -> E.Application f $ args <> one rhs
            _ -> E.Application lhs (one rhs)

    noPrec = choice $ keywordBased <> terminals

    keywordBased =
        [ E.Lambda <$ lambda <*> NE.some pattern' <* specialSymbol "->" <*> expression
        , let'
        , case'
        , match'
        , E.If <$ keyword "if" <*> expression <* keyword "then" <*> expression <* keyword "else" <*> expression
        , E.Record <$> someRecord "=" expression
        , E.List <$> brackets (commaSep expression)
        ]
      where
        let' = do
            let binding = (,) <$> pattern' <* specialSymbol "=" <*> expression
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