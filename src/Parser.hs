module Parser where

import Relude hiding (many, some)

import Ast
import Lexer

import Data.HashMap.Strict qualified as Map
import Text.Megaparsec

code :: Parser [Declaration]
code = declaration `sepEndBy` newline

declaration :: Parser Declaration
declaration = choice [typeDec, valueDec, signature]
  where
    valueDec = Ast.ValueD <$> termName <*> many pattern' <*> term <*> whereBlock
    whereBlock = option [] do
        void $ single $ BlockKeyword "where"
        valueDec `sepEndBy` newline <* blockEnd

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
term = undefined

{-
data Term
    = Lambda [Name] Term
    | Application Term [Term]
    | Let [(Pattern, Term)] Term
    | Case Term [(Pattern, Term)]
    | Match [([Pattern], Term)] -- | Haskell's \case
    | If Term Term Term
    | -- | value : Type
      Annotation Term Type'
    | Name Name
    | -- | .field.otherField.thirdField
      RecordLens [Name]
    | Constructor Name
    | -- | 'Constructor
      Variant Name
    | Record (HashMap Name Term)
    | List [Term]
-}
