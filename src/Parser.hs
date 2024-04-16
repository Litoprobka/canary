module Parser (code, declaration, type', pattern', term) where

import Relude hiding (many, some)

import Lexer
import Syntax.All
import Syntax.Declaration qualified as D
import Syntax.Pattern qualified as P
import Syntax.Term qualified as E -- stand for 'Expression'
import Syntax.Type qualified as T

import Control.Monad.Combinators.NonEmpty qualified as NE
import Data.HashMap.Strict qualified as Map
import Text.Megaparsec

code :: Parser [Declaration]
code = topLevelBlock declaration

declaration :: Parser Declaration
declaration = choice [typeDec, valueDec, signature]
  where
    valueDec = D.Value <$> termName <*> many pattern' <* specialSymbol "=" <*> term <*> whereBlock
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

    typePattern :: Parser (Name, [Type'])
    typePattern = do
        name <- typeName
        args <- many type'
        pure (name, args)

    signature :: Parser Declaration
    signature = do
        name <- termName
        specialSymbol ":"
        D.Signature name <$> type'

type' :: Parser Type'
type' = prec [const [forall', exists], typeApp, recordOrVariant] terminal
  where
    terminal = [T.Name <$> typeName]
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

pattern' :: Parser Pattern
pattern' = prec [nonTerminals] terminals
  where
    nonTerminals hp =
        [ P.Constructor <$> typeName <*> many hp
        , P.Variant <$> variantConstructor <*> many hp
        ]
    terminals =
        [ P.Var <$> termName
        , P.Record <$> someRecord "=" pattern'
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

term :: Parser Term
term = prec [annotation, application, const noPrecGroup] terminals
  where
    annotation hp = one $ try $ E.Annotation <$> hp <* specialSymbol ":" <*> type'
    application hp = one $ try $ E.Application <$> hp <*> NE.some hp
    -- I'm not sure whether `let` and `if` belong here, since `if ... then ... else ... : ty` should be parsed as `if ... then ... else (... : ty)`
    noPrecGroup =
        [ E.Lambda <$ lambda <*> NE.some pattern' <* specialSymbol "->" <*> term
        , let'
        , case'
        , match'
        , E.If <$ keyword "if" <*> term <* keyword "then" <*> term <* keyword "else" <*> term
        , E.Record <$> someRecord "=" term
        , E.List <$> brackets (commaSep term)
        ]
    let' = do
        let binding = (,) <$> pattern' <* specialSymbol "=" <*> term
        bindings <- block1 "let" binding
        E.Let bindings <$> term
    case' = do
        keyword "case"
        arg <- term
        matches <- block "of" $ (,) <$> pattern' <* specialSymbol "->" <*> term
        pure $ E.Case arg matches
    match' = E.Match <$> block "match" ((,) <$> some pattern' <* specialSymbol "->" <*> term)

    terminals =
        [ E.Name <$> termName
        , E.RecordLens <$> recordLens
        , E.Constructor <$> typeName
        , E.Variant <$> variantConstructor
        , E.IntLiteral <$> intLiteral
        , E.CharLiteral <$> charLiteral
        , E.TextLiteral <$> textLiteral
        ]