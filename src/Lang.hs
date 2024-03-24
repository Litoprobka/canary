module Lang where

import Relude hiding (some)
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
lambdaCalc = (Map.fromList <$> decl `sepEndBy1` newline)

name :: Parser Name
name = lexeme $ fromString <$> some letterChar

decl :: Parser (Name, Expr)
decl = lexeme do
    name' <- name
    symbol "="
    body <- expr
    pure $ (name', body)

expr :: Parser Expr
expr = choice [lambda, app, Var <$> name, int]

lambda :: Parser Expr
lambda = lexeme do
    lexeme $ oneOf ['\\', 'λ']
    name' <- name
    symbol "."
    body <- expr
    pure $ Lam name' body

app :: Parser Expr
app = between (symbol "(") (symbol ")") $
    App <$> expr <*> expr

int :: Parser Expr
int = Int <$> L.signed space (lexeme L.decimal)

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
    go scope expr = case expr of
        lam@Lam{} -> Right lam
        App fExpr argExpr -> do
            f <- go scope fExpr
            arg <- go scope argExpr
            case f of
                Lam varName body -> go (Map.insert varName arg scope) body
                _ -> Left TypeError
        Var name -> lookup' name scope >>= go scope
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