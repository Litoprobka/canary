module Lang (lambdaCalc, pretty, reduce) where

import Data.Char (isSpace)
import Data.HashMap.Strict qualified as Map
import Relude hiding (many, some)
import Text.Megaparsec
import Text.Megaparsec.Char hiding (space)
import Text.Megaparsec.Char.Lexer qualified as L
import Data.HashSet qualified as Set

type Parser a = ReaderT Pos (Parsec Void Text) a

space :: Parser ()
space = L.space nonNewlineSpace lineComment blockComment where
    nonNewlineSpace = void $ takeWhile1P (Just "space") \c -> isSpace c && c /= '\n' -- we can ignore \r here        
    lineComment = L.skipLineComment "//"
    blockComment = L.skipBlockCommentNested "/*" "*/"

-- | any non-zero amount of newlines and any amount of whitespace
newlines :: Parser ()
newlines = skipSome $ newline *> space

-- | space or a newline with increased indentation
spaceNL :: Parser ()
spaceNL = void $ space `sepBy` try do
    baseIndent <- ask
    void $ L.indentGuard newlines GT baseIndent

lexeme :: Parser a -> Parser a
lexeme = L.lexeme spaceNL

symbol :: Text -> Parser Text
symbol = L.symbol spaceNL

type Name = Text
data Expr
    = Lam Name Expr
    | App Expr Expr
    | Var Name
    | Int Int
    deriving (Show, Eq)
type Code = HashMap Name Expr

lambdaCalc :: Parsec Void Text Code
lambdaCalc = usingReaderT pos1 $
    space *> (Map.fromList <$> declP `sepEndBy1` newlines) <* eof

keywords :: HashSet Text
keywords = fromList ["where"]

nameP :: Parser Name
nameP = label "identifier" $ try $ lexeme $ nonKeyword . fromString =<< some letterChar where
    nonKeyword txt
        | txt `Set.member` keywords = empty -- todo: a more sensible error message
        | otherwise = pure txt


declP :: Parser (Name, Expr)
declP = label "declaration" $ lexeme do
    name <- nameP
    args <- many nameP
    void $ symbol "="
    body <- exprP
    localDefs <- Map.toList <$> whereBlock
    -- desugars local definitions to immediate lambda applications
    let body' = foldr Lam (foldl' addLocal body localDefs) args
    pure (name, body')
  where
    addLocal body (name, defBody) = Lam name body `App` defBody

whereBlock :: Parser Code
whereBlock = option Map.empty do
    void $ symbol "where"
    indent <- L.indentLevel
    -- note that `local` is only applied to the inner `declP` here
    defs <- local (const indent) declP `sepEndBy` spaceNL
    pure $ Map.fromList defs

exprP :: Parser Expr
exprP = label "expression" $ go 0 <$> nonApplication <*> many wildcardOrNA
  where
    wildcardOrNA = Nothing <$ symbol "_" <|> Just <$> nonApplication
    go :: Int -> Expr -> [Maybe Expr] -> Expr
    go _ acc [] = acc
    go i acc (Nothing : xs) =
        let x = "x" <> show i
         in Lam x $ go (i + 1) (App acc $ Var x) xs
    go i acc (Just x : xs) = go i (App acc x) xs

lambdaP :: Parser Expr
lambdaP = lexeme do
    void $ lexeme $ oneOf ['\\', 'λ']
    args <- some nameP
    void $ symbol "."
    expr <- exprP
    pure $ foldr Lam expr args

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
        Var name -> lookup' name decls
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