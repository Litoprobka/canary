{-# HLINT ignore "Use <$>" #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module Parser (code, declaration, type', pattern', expression, parseModule, run) where

import LangPrelude

import Common (
    Fixity (..),
    Loc (..),
    Located (..),
    Pass (..),
    PriorityRelation' (..),
    SimpleName,
    SimpleName_ (..),
    locFromSourcePos,
    zipLocOf,
 )
import Control.Monad.Combinators.Expr qualified as Expr
import Control.Monad.Combinators.NonEmpty qualified as NE
import Data.List.NonEmpty qualified as NE
import Data.Sequence qualified as Seq
import Diagnostic (Diagnose, fatal, reportsFromBundle)
import Lexer
import Relude.Monad (gets, modify)
import Syntax
import Syntax.Declaration qualified as D
import Syntax.Row
import Syntax.Row qualified as Row
import Syntax.Term
import Text.Megaparsec
import Text.Megaparsec.Char (string)

run :: Diagnose :> es => (FilePath, Text) -> Parser a -> Eff es a
run (fileName, fileContents) parser =
    either (fatal . NE.toList . reportsFromBundle) pure $
        parse (usingReaderT pos1 parser) fileName fileContents

parseModule :: Diagnose :> es => (FilePath, Text) -> Eff es [Declaration 'Parse]
parseModule input = run input code

code :: Parser [Declaration 'Parse]
code = topLevelBlock declaration

declaration :: Parser (Declaration 'Parse)
declaration = withLoc $ choice [typeDec, fixityDec, signature, valueDec]
  where
    valueDec = do
        flip3 D.Value <$> binding <*> whereBlock
    whereBlock = option [] $ block "where" (withLoc valueDec)

    typeDec = do
        keyword "type"
        name <- typeName
        simpleTypeDec name <|> gadtDec name

    simpleTypeDec name = do
        vars <- many varBinder
        specialSymbol "="
        flip4 D.Type name vars <$> typePattern `sepBy` specialSymbol "|"

    gadtDec :: SimpleName -> Parser (Loc -> Declaration 'Parse)
    gadtDec name = do
        mbKind <- optional $ specialSymbol ":" *> type'
        constrs <- block "where" $ withLoc do
            con <- constructorName
            specialSymbol ":"
            sig <- type'
            pure $ flip3 D.GadtConstructor con sig
        pure $ flip4 D.GADT name mbKind constrs

    typePattern :: Parser (Constructor 'Parse)
    typePattern = withLoc do
        name <- typeName
        args <- many typeParens
        pure $ flip3 D.Constructor name args

    signature = do
        name <- try $ (operatorInParens <|> termName) <* specialSymbol ":"
        flip3 D.Signature name <$> type'

    fixityDec = do
        keyword "infix"
        fixity <-
            choice
                [ InfixL <$ keyword "left"
                , InfixR <$ keyword "right"
                , InfixChain <$ keyword "chain"
                , pure Infix
                ]
        op <- someOperator
        above <- option [] do
            keyword "above"
            commaSep (Just <$> someOperator <|> Nothing <$ keyword "application")
        below <- option [] do
            keyword "below"
            commaSep someOperator
        equal <- option [] do
            keyword "equals"
            commaSep someOperator
        pure $ \loc -> D.Fixity loc fixity op PriorityRelation{above, below, equal}

varBinder :: ParserM m => m (VarBinder 'Parse)
varBinder =
    parens (VarBinder <$> typeVariable <* specialSymbol ":" <*> fmap Just type')
        <|> flip VarBinder Nothing
        <$> typeVariable

type' :: ParserM m => m (Type 'Parse)
type' = Expr.makeExprParser typeParens [[typeApp], [function], [forall', exists]]
  where
    forall' = Expr.Prefix $ lambdaLike Forall forallKeyword varBinder "."
    exists = Expr.Prefix $ lambdaLike Exists existsKeyword varBinder "."

    typeApp = Expr.InfixL $ pure Application
    function = Expr.InfixR $ appLoc Function <$ specialSymbol "->"
    appLoc con lhs rhs = con (zipLocOf lhs rhs) lhs rhs

-- a type expression with higher precedence than application
-- used when parsing constructor argument types and the like
typeParens :: ParserM m => m (Type 'Parse)
typeParens =
    label "type" $
        choice
            [ Name <$> typeName
            , Var <$> typeVariable
            , parens type'
            , withLoc' RecordT $ NoExtRow <$> someRecord ":" type' Nothing
            , withLoc' VariantT $ NoExtRow <$> brackets (fromList <$> commaSep variantItem)
            ]
  where
    variantItem = (,) <$> variantConstructor <*> option (Name $ Located Blank $ Name' "Unit") typeParens

someRecord :: ParserM m => Text -> m value -> Maybe (SimpleName -> value) -> m (Row value)
someRecord delim valueP missingValue = braces (fromList <$> commaSep recordItem)
  where
    onMissing name = case missingValue of
        Nothing -> id
        Just nameToValue -> option (nameToValue name)
    recordItem = do
        recordLabel <- termName
        valuePattern <- onMissing recordLabel $ specialSymbol delim *> valueP
        pure (recordLabel, valuePattern)

lambdaLike :: ParserM m => (Loc -> a -> b -> b) -> m () -> m a -> Text -> m (b -> b)
lambdaLike con kw argP endSym = do
    kw
    args <- NE.some $ (,) <$> getSourcePos <*> argP
    specialSymbol endSym
    end <- getSourcePos
    pure \body -> foldr (\(start, arg) -> con (locFromSourcePos start end) arg) body args

pattern' :: ParserM m => m (Pattern 'Parse)
pattern' =
    choice
        [ ConstructorP <$> typeName <*> many patternParens
        , VariantP <$> variantConstructor <*> patternParens
        , patternParens
        ]

{- | parses a pattern with constructors enclosed in parens
should be used in cases where multiple patterns in a row are accepted, i.e.
function definitions and match expressions
-}
patternParens :: ParserM m => m (Pattern 'Parse)
patternParens = do
    pat <-
        choice
            [ VarP <$> termName
            , lexeme $ withLoc' WildcardP $ string "_" <* option "" termName'
            , record
            , withLoc' ListP $ brackets (commaSep pattern')
            , LiteralP <$> literal
            , -- a constructor without arguments or with a tightly-bound record pattern
              lexeme $ ConstructorP <$> constructorName <*> option [] (one <$> record)
            , flip VariantP unit <$> variantConstructor -- some sugar for variants with a unit payload
            , parens pattern'
            ]
    option pat do
        specialSymbol ":"
        AnnotationP pat <$> type'
  where
    record = withLoc' RecordP $ someRecord "=" pattern' (Just VarP)
    unit = RecordP Blank Row.empty

binding :: ParserM m => m (Binding 'Parse)
binding = do
    f <-
        -- it should probably be `try (E.FunctionBinding <$> funcName) <*> NE.some patternParens
        -- for cleaner parse errors
        try (FunctionB <$> funcName <*> NE.some patternParens)
            <|> (ValueB <$> pattern')
    specialSymbol "="
    f <$> expression
  where
    -- we might want to support infix operator declarations in the future
    -- > f $ x = f x
    funcName = operatorInParens <|> termName

expression :: ParserM m => m (Expr 'Parse)
expression = expression' do
    expr <- Name <$> termName
    -- type applications bind tighther than anything else
    apps <- many do
        void $ single '@'
        typeParens
    pure $ foldl' TypeApplication expr apps

-- an expression with infix operators and unresolved priorities
-- the `E.Infix` constructor is only used when there is more than one operator
expression' :: ParserM m => m (Expr 'Parse) -> m (Expr 'Parse)
expression' termParser = do
    firstExpr <- noPrec termParser
    pairs <- many $ (,) <$> optional someOperator <*> noPrec termParser
    let expr = case pairs of
            [] -> firstExpr
            [(Nothing, secondExpr)] -> firstExpr `Application` secondExpr
            [(Just op, secondExpr)] -> Name op `Application` firstExpr `Application` secondExpr
            (_ : _ : _) -> uncurry InfixE $ shift firstExpr pairs
    option expr do
        specialSymbol ":"
        Annotation expr <$> type'
  where
    sameScopeExpr = expression' termParser

    -- overrides the term parser of expression to collect wildcards
    -- has to be called in the scope of `withWildcards`
    newScopeExpr :: ParserM m => StateT (Seq Loc) m (Expr 'Parse)
    newScopeExpr =
        expression' $
            nextVar
                <|> fmap Name termName

    -- x [(+, y), (*, z), (+, w)] --> [(x, +), (y, *), (z, +)] w
    shift expr [] = ([], expr)
    shift lhs ((op, rhs) : rest) = first ((lhs, op) :) $ shift rhs rest
    noPrec varParser = choice $ [varParser] <> keywordBased <> terminals

    -- expression forms that have a leading keyword/symbol
    keywordBased =
        [ -- note that we don't use `sameScopeExpression` here, since interleaving explicit and implicit lambdas, i.e. `(\f -> f _)`, is way too confusing
          lambdaLike Lambda lambda pattern' "->" <*> expression
        , letRec
        , let'
        , case'
        , match'
        , if'
        , doBlock
        , record
        , withWildcards $ withLoc $ flip List <$> brackets (commaSep newScopeExpr)
        , Name <$> operatorInParens -- operators are never wildcards, so it's okay to sidestep termParser here
        , parens $ withWildcards newScopeExpr
        ]
      where
        letRec = withLoc $ letRecBlock (try $ keyword "let" *> keyword "rec") (flip3 LetRec) binding expression
        let' =
            withLoc $
                letBlock "let" (flip3 Let) binding expression -- wildcards do not propagate through let bindings. Use an explicit lambda instead!
        case' = withLoc do
            keyword "case"
            arg <- expression -- `case _ of` is redundant, since it has the same meaning as a one arg `match`
            matches <- block "of" $ (,) <$> pattern' <* specialSymbol "->" <*> expression
            pure $ flip3 Case arg matches
        match' = withLoc $ flip Match <$> block "match" ((,) <$> some patternParens <* specialSymbol "->" <*> expression)
        if' = withLoc do
            keyword "if"
            cond <- sameScopeExpr
            keyword "then"
            true <- sameScopeExpr
            keyword "else"
            false <- sameScopeExpr
            pure $ flip4 If cond true false
        doBlock = withLoc do
            stmts <-
                block "do" $
                    choice
                        [ try $ Bind <$> pattern' <* specialSymbol "<-" <*> expression
                        , withLoc $ flip3 With <$ keyword "with" <*> pattern' <* specialSymbol "<-" <*> expression
                        , withLoc' DoLet $ keyword "let" *> binding
                        , Action <$> expression
                        ]
            case unsnoc stmts of
                Nothing -> fail "empty do block"
                Just (stmts', Action lastAction) -> pure $ flip3 Do stmts' lastAction
                _ -> fail "last statement in a do block must be an expression"
        unsnoc [] = Nothing
        unsnoc [x] = Just ([], x)
        unsnoc (x : xs) = first (x :) <$> unsnoc xs

    record =
        withWildcards $ withLoc $ flip Record <$> someRecord "=" newScopeExpr (Just Name)

    terminals =
        [ withLoc' RecordLens recordLens
        , constructor
        , Variant <$> variantConstructor
        , Literal <$> literal
        ]
    constructor = lexeme do
        name <- constructorName
        optional record <&> \case
            Nothing -> Constructor name
            Just arg -> Constructor name `Application` arg

-- turns out that respecting operator precedence makes for confusing code
-- i.e. consider, say, `3 + _ * 4`
-- with precendence, it should be parsed as `3 + (\x -> x * 4)`
-- but what you probably mean is `\x -> 3 + x * 4`
--
-- in the end, I decided to go with the simplest rules possible - that is, parens determine
-- the scope of the implicit lambda
--
-- it's not clear whether I want to require parens around list and record literals
-- on one hand, `({x = 3, y = 3})` looks a bit janky
-- on the other hand, without that you wouldn't be able to write `f {x = 3, y = _}`
-- if you want it to mean `\y -> f {x = 3, y}`
withWildcards :: ParserM m => StateT (Seq Loc) m (Expr 'Parse) -> m (Expr 'Parse)
withWildcards p = do
    -- todo: collect a list of wildcard names along with the counter
    ((expr, mbVarLocs), loc) <- withLoc $ (,) <$> runStateT p Seq.empty
    pure case NE.nonEmpty $ zip [1 ..] $ toList mbVarLocs of
        Just varLocs ->
            WildcardLambda loc ((\(i, varLoc) -> Located varLoc $ Wildcard' i) <$> varLocs) expr
        Nothing -> expr

-- foldr (\i -> E.Lambda loc (P.Var $ SimpleName Blank $ "$" <> show i)) expr [1 .. varCount]

nextVar :: ParserM m => StateT (Seq Loc) m (Expr 'Parse)
nextVar = do
    loc <- withLoc' const wildcard
    modify (Seq.|> loc)
    i <- gets Seq.length
    pure . Name . Located loc $ Wildcard' i

flip3 :: (a -> b -> c -> d) -> b -> c -> a -> d
flip3 f y z x = f x y z

flip4 :: (a -> b -> c -> d -> e) -> b -> c -> d -> a -> e
flip4 f y z w x = f x y z w
