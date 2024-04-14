module Lang (lambdaCalc, pretty, reduce) where

import Data.HashMap.Strict qualified as Map
import Lexer
import Relude hiding (many, some)
import Text.Megaparsec hiding (Token)

type Name = Text
data Expr
    = Lam Name Expr
    | App Expr Expr
    | Var Name
    | Int Int
    deriving (Show, Eq)
type Code = HashMap Name Expr

lambdaCalc :: Parsec Void [Token] Code
lambdaCalc = Map.fromList <$> declP `sepEndBy1` newline <* eof

declP :: Parser (Name, Expr)
declP = label "declaration" $ do
    name <- termName
    args <- many termName
    specialSymbol "="
    body <- exprP
    localDefs <- Map.toList <$> whereBlock
    -- desugars local definitions to immediate lambda applications
    let body' = foldr Lam (foldl' addLocal body localDefs) args
    pure (name, body')
  where
    addLocal body (name, defBody) = Lam name body `App` defBody

whereBlock :: Parser Code
whereBlock = option Map.empty do
    defs <- block "where" declP
    pure $ Map.fromList defs

exprP :: Parser Expr
exprP = label "expression" $ go 0 <$> nonApplication <*> many wildcardOrNA
  where
    wildcardOrNA = Nothing <$ single (LowerIdentifier "_") <|> Just <$> nonApplication
    go :: Int -> Expr -> [Maybe Expr] -> Expr
    go _ acc [] = acc
    go i acc (Nothing : xs) =
        let x = "x" <> show i
         in Lam x $ go (i + 1) (App acc $ Var x) xs
    go i acc (Just x : xs) = go i (App acc x) xs

lambdaP :: Parser Expr
lambdaP = do
    lambda
    args <- some termName
    specialSymbol "->"
    expr <- exprP
    pure $ foldr Lam expr args

nonApplication :: Parser Expr
nonApplication =
    choice
        [ parens exprP
        , lambdaP
        , Var <$> termName
        , Int <$> intLiteral
        ]

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
pretty (Lam arg body) = "λ" <> arg <> " -> " <> pretty body
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