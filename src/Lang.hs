module Lang where

import Data.Char (isSpace)
import Data.HashMap.Strict qualified as Map
import Relude hiding (many, some)
import Text.Megaparsec
import Text.Megaparsec.Char hiding (space)
import Text.Megaparsec.Char.Lexer qualified as L

type Parser a = Parsec Void Text a

space :: Parser ()
space = L.space nonNewlineSpace lineComment blockComment
  where
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
    | Int Int
    deriving (Show, Eq)
type Code = HashMap Name Expr

lambdaCalc :: Parser Code
lambdaCalc = space *> (Map.fromList <$> declP `sepEndBy1` many (newline *> space))

nameP :: Parser Name
nameP = lexeme $ fromString <$> some letterChar

declP :: Parser (Name, Expr)
declP = lexeme do
    name <- nameP
    args <- many nameP
    symbol "="
    body <- exprP
    let body' = foldr Lam body args
    pure (name, body')

exprP :: Parser Expr
exprP = go 0 <$> nonApplication <*> many wildcardOrNA
  where
    wildcardOrNA = Nothing <$ symbol "_" <|> Just <$> nonApplication
    go _ acc [] = acc
    go i acc (Nothing : xs) =
        let x = "x" <> show i
         in Lam x $ go (i + 1) (App acc $ Var x) xs
    go i acc (Just x : xs) = go i (App acc x) xs

lambdaP :: Parser Expr
lambdaP = lexeme do
    lexeme $ oneOf ['\\', 'λ']
    name <- nameP
    symbol "."
    Lam name <$> exprP

nonApplication :: Parser Expr
nonApplication =
    lexeme $
        choice
            [ between (symbol "(") (symbol ")") exprP
            , lambdaP
            , Var <$> nameP
            , intP
            ]

intP :: Parser Expr
intP = Int <$> L.signed space (lexeme L.decimal)

data RuntimeError = UnboundVar Name | TypeError deriving (Show)

lookup' :: Name -> HashMap Name a -> Either RuntimeError a
lookup' name scope = case Map.lookup name scope of
    Just expr -> Right expr
    Nothing -> Left $ UnboundVar name

reduce :: Code -> Either RuntimeError Expr
reduce decls = do
    main <- lookup' "main" decls
    go main
  where
    go :: Expr -> Either RuntimeError Expr
    go expr = case expr of
        lam@Lam{} -> Right lam
        App fExpr argExpr -> do
            f <- go fExpr
            arg <- go argExpr
            case f of
                Lam argName body -> go $ substitute argName arg body
                _ -> Left TypeError
        Var name -> do lookup' name decls
        n@Int{} -> Right n

pretty :: Expr -> Text
pretty (Lam arg body) = "λ" <> arg <> ". " <> pretty body
pretty (App f x) = parensLam f <> " " <> parensApp x
  where
    parensLam lam@Lam{} = "(" <> pretty lam <> ")"
    parensLam other = pretty other
    parensApp app@App{} = "(" <> pretty app <> ")"
    parensApp other = parensLam other
pretty (Var var) = var
pretty (Int n) = show n

substitute :: Name -> Expr -> Expr -> Expr
substitute varName varBody = go
  where
    go (Lam var' body)
        | var' == varName = Lam var' body
        | otherwise = Lam var' $ go body
    go (App fExpr argExpr) = App (go fExpr) (go argExpr)
    go (Var name)
        | varName == name = varBody
        | otherwise = Var name
    go n@Int{} = n