{-# LANGUAGE ApplicativeDo #-}
{-# OPTIONS_GHC -Wno-partial-fields #-}

module Syntax.Elaborated where

import Common hiding (Name)
import Data.Row
import LangPrelude
import Syntax.Core (CoreTerm, CoreType)
import Syntax.Term (Visibility)

{-x
The elaborated AST is halfway between core and pre-typecheck passes
-}

infix 3 :::
data Typed a = a ::: CoreType deriving (Show)

unTyped :: Typed a -> a
unTyped (x ::: _) = x

data EPattern
    = VarP SimpleName_
    | WildcardP Text
    | ConstructorP Name_ [(Visibility, EPattern)]
    | TypeP Name_ [(Visibility, EPattern)]
    | VariantP OpenName EPattern
    | RecordP (Vector (OpenName, EPattern))
    | SigmaP Visibility EPattern EPattern
    | ListP [EPattern]
    | LiteralP Literal
    deriving (Show)

data EDeclaration
    = ValueD Name_ CoreTerm -- no local bindings for now
    -- I'm not sure which representation for typechecked constructors makes more sense, this is the bare minimum
    | TypeD Name_ [(Name_, Vector (Visibility, CoreType))]
    | SignatureD Name_ CoreType

instance HasLoc a => HasLoc (Typed a) where
    getLoc (x ::: _) = getLoc x

-- | How many new variables does a pattern bind?
patternArity :: EPattern -> Int
patternArity = go
  where
    go = \case
        VarP{} -> 1
        WildcardP{} -> 1 -- further types may still depend on the value of a wildcard, so it is treated as a variable here
        ConstructorP _ args -> sum (map (go . snd) args)
        TypeP _ args -> sum (map (go . snd) args)
        VariantP _ arg -> go arg
        RecordP row -> sum (fmap (go . snd) row)
        SigmaP _ lhs rhs -> go lhs + go rhs
        ListP args -> sum (map go args)
        LiteralP{} -> 0

{-

lift :: Int -> ETerm -> ETerm
lift n = liftAt n (Level 0)

liftAt :: Int -> Level -> ETerm -> ETerm
liftAt n = go
  where
    go depth = \case
        Var (Index index)
            | index >= depth.getLevel -> Var (Index $ index + n)
            | otherwise -> Var (Index index)
        other -> elabTraversalPureWithLevel go (C.liftAt n) depth other

elabTraversalWithLevel
    :: Applicative f => (Level -> ETerm -> f ETerm) -> (Level -> CoreTerm -> f CoreTerm) -> Level -> ETerm -> f ETerm
elabTraversalWithLevel recur recurCore lvl = \case
    App vis lhs rhs -> App vis <$> recur lvl lhs <*> recur lvl rhs
    Lambda vis pat body -> Lambda vis pat <$> recur (lvl `incLevel` patternArity pat) body
    Let ValueB{name, body = bindingBody} body -> do
        bindingBody <- recur lvl bindingBody
        body <- recur (succ lvl) body
        pure $ Let ValueB{name, body = bindingBody} body
    Let FunctionB{name, args, body = fnBody} body -> do
        let fnLevel = lvl `incLevel` sum (fmap (patternArity . snd) args)
        fnBody <- recur fnLevel fnBody
        body <- recur (succ lvl) body
        pure $ Let FunctionB{name, args, body = fnBody} body
    LetRec bindings body -> LetRec <$> traverse recurBinding bindings <*> recur bindingLvl body
      where
        bindingLvl = lvl `incLevel` length bindings
        recurBinding = \case
            ValueB name bindingBody -> ValueB name <$> recur bindingLvl bindingBody
            FunctionB name args fnBody ->
                let newLevel = bindingLvl `incLevel` sum (fmap (patternArity . snd) args)
                 in FunctionB name args <$> recur newLevel fnBody
    Case arg branches -> Case <$> recur lvl arg <*> for branches \(pat, body) -> (pat,) <$> recur (lvl `incLevel` patternArity pat) body
    Match branches ->
        Match <$> for branches \(pats, body) ->
            let innerLevel = lvl `incLevel` sum (fmap (patternArity . unTyped) pats)
             in (pats,) <$> recur innerLevel body
    If cond true false -> If <$> recur lvl cond <*> recur lvl true <*> recur lvl false
    Record row -> Record <$> traverse (recur lvl) row
    RecordAccess lhs field -> RecordAccess <$> recur lvl lhs <*> pure field
    List itemType items -> List <$> recur lvl itemType <*> traverse (recur lvl) items
    Sigma vis lhs rhs -> Sigma vis <$> recur lvl lhs <*> recur lvl rhs
    Do{} -> error "elabTraversal: do-notation not supported yet"
    Q q v e var body -> Q q v e var <$> recur (succ lvl) body
    VariantT row -> VariantT <$> traverse (recur lvl) row
    RecordT row -> RecordT <$> traverse (recur lvl) row
    Core coreTerm -> Core <$> recurCore lvl coreTerm
    Var index -> pure $ Var index
    Name name -> pure $ Name name
    Literal lit -> pure $ Literal lit
    Variant name -> pure $ Variant name

elabTraversalPureWithLevel :: (Level -> ETerm -> ETerm) -> (Level -> CoreTerm -> CoreTerm) -> Level -> ETerm -> ETerm
elabTraversalPureWithLevel recur recurCore lvl = runIdentity . elabTraversalWithLevel (\lvl -> pure . recur lvl) (\lvl -> pure . recurCore lvl) lvl

elabTraversalPure :: (ETerm -> ETerm) -> (CoreTerm -> CoreTerm) -> ETerm -> ETerm
elabTraversalPure recur recurCore = elabTraversalPureWithLevel (const recur) (const recurCore) (Level 0)
-}
