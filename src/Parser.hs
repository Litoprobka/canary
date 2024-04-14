module Parser where

import Relude hiding (many, some)

import Ast
import Lexer hiding (Lambda, RecordLens)

import Control.Monad.Combinators.NonEmpty qualified as NE
import Data.HashMap.Strict qualified as Map
import Text.Megaparsec

code :: Parser [Declaration]
code = declaration `sepEndBy` newline

declaration :: Parser Declaration
declaration = choice [typeDec, valueDec, signature]
  where
    valueDec = ValueD <$> termName <*> many pattern' <* specialSymbol "=" <*> term <*> whereBlock
    whereBlock = option [] $ block "where" valueDec

    typeDec = keyword "type" *> (typeAliasDec <|> typeDec')
    typeAliasDec = do
        keyword "alias"
        name <- typeName
        specialSymbol "="
        AliasD name <$> type'

    typeDec' = do
        name <- typeName
        vars <- many typeVariable -- placeholder
        TypeD name vars <$> (typePattern `sepBy` specialSymbol "|")

    typePattern :: Parser (Name, [Type'])
    typePattern = do
        name <- typeName
        args <- many type'
        pure (name, args)

    signature :: Parser Declaration
    signature = do
        name <- termName
        specialSymbol ":"
        SigD name <$> type'

type' :: Parser Type'
type' = prec [const [forall', exists], typeApp, recordOrVariant] terminal
  where
    terminal = [TypeName <$> typeName]
    forall' = do
        keyword "forall" -- todo: unicode
        Forall <$> some typeVariable <* specialSymbol "." <*> type'

    exists = do
        keyword "exists"
        Exists <$> some typeVariable <* specialSymbol "." <*> type'

    typeApp higherPrec = one $ TypeApplication <$> higherPrec <*> many higherPrec
    recordOrVariant hp =
        [ RecordType <$> someRecord ":" type'
        , VariantType <$> brackets (Map.fromList <$> variantItem `sepEndBy` specialSymbol ",")
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
        [ ConP <$> typeName <*> many hp
        , VariantP <$> variantConstructor <*> many hp
        ]
    terminals =
        [ VarP <$> termName
        , RecordP <$> someRecord "=" pattern'
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
    annotation hp = one $ Annotation <$> hp <* specialSymbol ":" <*> type'
    application hp = one do
        f <- hp
        args <- many hp
        pure case args of
            [] -> f
            (x : xs) -> Application f (x :| xs)
    -- I'm not sure whether `let` and `if` belong here, since `if ... then ... else ... : ty` should be parsed as `if ... then ... else (... : ty)`
    noPrecGroup =
        [ Lambda <$ lambda <*> NE.some pattern' <* specialSymbol "->" <*> term
        , let'
        , case'
        , match'
        , If <$ keyword "if" <*> term <* keyword "then" <*> term <* keyword "else" <*> term
        , Record <$> someRecord "=" term
        , List <$> brackets (term `sepEndBy` specialSymbol ",")
        ]
    let' = do
        let binding = (,) <$> pattern' <* specialSymbol "=" <*> term
        bindings <- block1 "let" binding
        blockEnd
        Let bindings <$> term
    case' = do
        keyword "case"
        arg <- term
        matches <- block "of" $ (,) <$> pattern' <* specialSymbol "->" <*> term
        pure $ Case arg matches
    match' = Match <$> block "match" ((,) <$> some pattern' <* specialSymbol "->" <*> term)

    terminals =
        [ Name <$> termName
        , RecordLens <$> recordLens
        , Constructor <$> typeName
        , Variant <$> variantConstructor
        ]