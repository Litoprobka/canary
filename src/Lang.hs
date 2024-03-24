module Lang where

import Relude hiding (some, many)
import Text.Megaparsec
import Text.Megaparsec.Char hiding (space)
import Text.Megaparsec.Char.Lexer qualified as L
import Data.HashMap.Strict qualified as Map
import Data.Char (isSpace)

type Parser a = Parsec Void Text a

space :: Parser ()
space = L.space nonNewlineSpace lineComment blockComment where
    nonNewlineSpace = void $ takeWhile1P (Just "space") \c -> isSpace c && c /= '\n' -- we can ignore \r here
    lineComment = L.skipLineComment "//"
    blockComment = L.skipBlockCommentNested "/*" "*/"

lexeme :: Parser a -> Parser a
lexeme = L.lexeme space

symbol :: Text -> Parser Text
symbol = L.symbol space

type Name = Text
data Expr
    = Lam Name Expr
    | App Expr Expr
    | Var Name
    | Int Int deriving (Show, Eq)
type Code = HashMap Name Expr

lambdaCalc :: Parser Code
lambdaCalc = space *> (Map.fromList <$> declP `sepEndBy1` many (newline *> space))

nameP :: Parser Name
nameP = lexeme $ fromString <$> some letterChar

declP :: Parser (Name, Expr)
declP = lexeme do
    name <- nameP
    symbol "="
    body <- exprP
    pure (name, body)

exprP :: Parser Expr
exprP = choice [lambdaP, app, Var <$> nameP, intP]

lambdaP :: Parser Expr
lambdaP = lexeme do
    lexeme $ oneOf ['\\', 'λ']
    name <- nameP
    symbol "."
    Lam name <$> exprP

app :: Parser Expr
app = between (symbol "(") (symbol ")") $
    foldl' App <$> exprP <*> some exprP

intP :: Parser Expr
intP = Int <$> L.signed space (lexeme L.decimal)

data RuntimeError = UnboundVar Name | TypeError deriving Show

lookup' :: Name -> HashMap Name a -> Either RuntimeError a
lookup' name scope = case Map.lookup name scope of
    Just expr -> Right expr
    Nothing -> Left $ UnboundVar name

reduce :: Code -> Either RuntimeError Expr
reduce decls = do
    main <- lookup' "main" decls
    go decls main
  where
    go :: HashMap Name Expr -> Expr -> Either RuntimeError Expr
    go scope expr = case expr of
        Lam argName body -> Lam argName <$> go (Map.insert argName (Var argName) scope) body
        App fExpr argExpr -> do
            f <- go scope fExpr
            arg <- go scope argExpr
            case f of
                Lam argName body -> go (Map.insert argName arg scope) body
                Var{} -> Right $ App f arg
                _ -> Left TypeError
        Var name -> do
            mbBody <- lookup' name scope
            case mbBody of
                Var name' | name == name' -> Right $ Var name -- unresolved variable
                other -> go scope other
        n@Int{} -> Right n

pretty :: Expr -> Text
pretty (Lam arg body) = "λ" <> arg <> ". " <> pretty body
pretty (App f x) = "(" <> pretty f <> " " <> pretty x <> ")"
pretty (Var var) = var
pretty (Int n) = show n

{-
substitute :: Name -> Expr -> Expr -> Expr
substitute varName varBody expr = go expr where
    go (Lam var' body) = Lam var' $ go body
    go (App fExpr argExpr) = App (go fExpr) (go argExpr)
    go (Var name)
        | varName == name = varBody
        | otherwise = Var name
    go n@Int{} = n
-}