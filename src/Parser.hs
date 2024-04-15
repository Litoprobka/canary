module Parser (code, declaration, type', pattern', term) where

import Relude hiding (many, some)

import Lexer hiding (Lambda, RecordLens)
import Syntax.All
import Syntax.Declaration qualified as D
import Syntax.Pattern qualified as P
import Syntax.Term qualified as T
import Syntax.Type qualified as Ty

import Control.Monad.Combinators.NonEmpty qualified as NE
import Data.HashMap.Strict qualified as Map
import Text.Megaparsec

code :: Parser [Declaration]
code = declaration `sepEndBy` newline

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
    terminal = [Ty.Name <$> typeName]
    forall' = do
        keyword "forall" -- todo: unicode
        Ty.Forall <$> some typeVariable <* specialSymbol "." <*> type'

    exists = do
        keyword "exists"
        Ty.Exists <$> some typeVariable <* specialSymbol "." <*> type'

    typeApp higherPrec = one $ try $ Ty.Application <$> higherPrec <*> NE.some higherPrec
    recordOrVariant hp =
        [ Ty.Record <$> someRecord ":" type'
        , Ty.Variant <$> brackets (Map.fromList <$> variantItem `sepEndBy` specialSymbol ",")
        ]
      where
        variantItem = (,) <$> variantConstructor <*> many (prec [recordOrVariant] [hp])

someRecord :: Text -> Parser value -> Parser (HashMap Name value)
someRecord delim valueP = braces (Map.fromList <$> recordItem `sepEndBy` specialSymbol ",")
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
    annotation hp = one $ T.Annotation <$> hp <* specialSymbol ":" <*> type'
    application hp = one $ T.Application <$> hp <*> NE.some hp
    -- I'm not sure whether `let` and `if` belong here, since `if ... then ... else ... : ty` should be parsed as `if ... then ... else (... : ty)`
    noPrecGroup =
        [ T.Lambda <$ lambda <*> NE.some pattern' <* specialSymbol "->" <*> term
        , let'
        , case'
        , match'
        , T.If <$ keyword "if" <*> term <* keyword "then" <*> term <* keyword "else" <*> term
        , T.Record <$> someRecord "=" term
        , T.List <$> brackets (term `sepEndBy` specialSymbol ",")
        ]
    let' = do
        let binding = (,) <$> pattern' <* specialSymbol "=" <*> term
        bindings <- block1 "let" binding
        blockEnd
        T.Let bindings <$> term
    case' = do
        keyword "case"
        arg <- term
        matches <- block "of" $ (,) <$> pattern' <* specialSymbol "->" <*> term
        pure $ T.Case arg matches
    match' = T.Match <$> block "match" ((,) <$> some pattern' <* specialSymbol "->" <*> term)

    terminals =
        [ T.Name <$> termName
        , T.RecordLens <$> recordLens
        , T.Constructor <$> typeName
        , T.Variant <$> variantConstructor
        ]