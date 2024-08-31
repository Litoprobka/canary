{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

module TypeChecker where

import NameResolution (Id (..))
import Relude
import Syntax.All
import Syntax.Expression qualified as E
import Syntax.Pattern qualified as P
import Syntax.Type qualified as T
import qualified Data.IntMap.Strict as IntMap

newtype TypeVar = TypeVar Int

-- don't feel like creating a separate file atm
data Monotype
    = Var Id
    | Name Id
    | UnsolvedVar TypeVar
    | Function Monotype Monotype
    | Application Monotype Monotype

-- records and variants are to come later

data VarState
    = Unsolved
    | Forall -- do I need this?
    | Solved Monotype -- partially solved

data InfState = InfState
    { nextVar :: TypeVar
    , knownTypes :: IntMap (Either (Type' Id) TypeVar)
    , varState :: IntMap VarState
    }

type InfMonad = State InfState

intType :: Type' Id
intType = undefined

textType :: Type' Id
textType = undefined

charType :: Type' Id
charType = undefined

boolType :: Type' Id
boolType = undefined

listType :: Type' Id -> Type' Id
listType = undefined

-- | creates an existential type variable
unsolved :: InfMonad TypeVar
unsolved = do
    var <- gets nextVar
    modify \InfState{..} ->
        InfState
            { nextVar = var + 1
            , varState = IntMap.insert var Unsolved
            }
    pure var

forallVar :: InfMonad TypeVar
forallVar = do
    var <- gets nextVar
    modify \InfState{..} ->
        InfState
            { nextVar = var + 1
            , varState = IntMap.insert var Forall
            }
    pure var

addKnownType :: Id -> Type' Id -> InfMonad ()
addKnownType (Id n) ty = modify f
  where
    f InfState{..} =
        InfState{knownTypes = knownTypes & IntMap.insert n (Left ty)}

assignVar :: Id -> TypeVar -> InfMonad ()
assignVar (Id n) var = modify f
  where
    f InfState{..} =
        InfState{knownTypes = knownTypes & IntMap.insert n (Right var)}

{- | just like the similary named function in NameResolution,
it discards all state changes except for id changes
(not sure whether it's okay to ignore the id changes as well in this case)
-}
scoped :: InfMonad a -> InfMonad a
scoped action = do
    state <- get
    output <- action
    newNextVar <- gets nextVar
    put $ state{nextVar = newNextVar}
    pure output

check :: Expression Id -> Type' Id -> InfMonad ()
check expr (T.Forall varId body) = scoped do
    var <- existential
    assignVar varId var
check expr (T.Exists var body) = scoped do undefined
check (E.Lambda arg body) (T.Function inTy outTy) = scoped do
    addKnownType arg inTy -- not quite
    check body
check expr ty = case expr of
    E.Let binding body -> undefined
    E.Case body matches -> undefined
    E.Match matches -> undefined
    E.If cond true false -> do
        check cond boolType
        check true ty
        check false ty
    E.Annotation body ty2 -> do
        ty2 `subtypeOf` ty
        check body ty2
    E.Constructor name -> undefined
    E.Variant name -> do
        rowTy <- undefined -- make an open row variable somehow
        openVariant <- undefined rowTy -- figure out argument count and types
        openVariant `subtypeOf` ty
    E.Record fields -> do
        fieldTypes <- traverse infer fields
        T.Record fieldTypes `subtypeOf` ty
    E.List xs -> traverse_ (`check` ty) xs
    other -> do
        otherTy <- infer other
        otherTy `subtypeOf` ty

subtypeOf :: Type' Id -> Type' Id -> InfMonad ()
subtypeOf (T.Name lhs) (T.Name rhs) = do
    lhsTy <- lookupType lhs
    rhsTy <- lookupType rhs
    lhsTy `subtypeOf` rhsTy
-- I *think* that we have to do an extra lookup because of aliases
subtypeOf (T.Variant alts) (T.Variant alts2) =
    undefined -- unify the variants, idk
subtypeOf (T.Record fields1) (T.Record fields2) = undefined
subtypeOf (T.Var var) rhs = undefined
subtypeOf lhs (T.Var var) = undefined
--
-- some more cases
--
subtypeOf lhs rhs = undefined "not a subtype"

{-
= Name n
    | Var n
    | Application (Type' n) (NonEmpty (Type' n))
    -- | unlike the multi-arg Application, taking exactly one argument
    -- sounds like a better approach here
    | Function (Type' n) (Type' n)
    | Forall [n] (Type' n)
    | Exists [n] (Type' n)
    | Variant (HashMap OpenName [Type' n])
    | Record (HashMap OpenName (Type' n))
-}

lookupType :: Id -> InfMonad (Type' Id)
lookupType = undefined

checkPattern :: Pattern Id -> Type' Id -> InfMonad ()
checkPattern (P.Var name) _ = pass -- a new variable matches any type
checkPattern (P.Constructor name args) ty = do
    -- the sub rule probably works here
    conTy <- lookupType name
    conTy `subtypeOf` ty
    undefined
-- check arg count
-- check each argument
checkPattern (P.Variant name arg) (T.Variant alts) = do
    case HashMap.lookup name alts of
        Nothing -> undefined "type error"
        Just ty -> check arg ty -- doesn't quite work with polymorphic types
checkPattern (P.Record bindings) (T.Record fields) = do
    for_ bindings \(name, arg) -> do
        case HashMap.lookup name fields of
            Nothing -> undefined "type error"
            Just ty -> check arg ty
checkPattern (P.List xs) ty@(T.Application _ tyArg) = do
    traverse_ (`check` tyArg) xs
    listType tyArg `subtypeOf` ty
checkPattern other ty = do
    inferred <- inferPattern other
    inferred `subtypeOf` ty

-- this shouldn't return a full-fledged type
inferPattern :: Pattern Id -> InfMonad (Type' Id)
inferPattern (P.Var name) = undefined "an unsolved var"
inferPattern (P.Constructor name args) = do
    conTy <- lookupType name
    undefined
-- check that arg count matches constructor arity
-- check the type of each pattern? (what to with parametrised types?)
inferPattern (P.Variant name arg) = do
    argTy <- inferPattern arg
    pure $ T.Variant $ fromList [(name, argTy)]
-- todo: this should use a free row variable
inferPattern (P.Record bindings) = T.Record <$> forM binding (traverse inferPattern) -- I don't think this infers stuff like { x : a, y : a }
inferPattern (P.List xs) = undefined -- we have to unify all arg types somehow
inferPattern (P.IntLiteral _) = pure intType
inferPattern (P.TextLiteral _) = pure textType
inferPattern (P.CharLiteral _) = pure charType

{-
Var n
    | Constructor n [Pattern n]
    | Variant OpenName (Pattern n)
    | Record (HashMap OpenName (Pattern n))
    | List [Pattern n]
    | IntLiteral Int
    | TextLiteral Text
    | CharLiteral Text
-}

infer :: Expression Id -> InfMonad (Type' Id)
infer = \case
    E.Lambda arg body -> do
        -- should this be scoped?
        bodyTy <- scoped do
            argTy <- fresh
            infer body
        undefined
    E.Let binding body -> do undefined

{-
Lambda (NonEmpty (Pattern n)) (Expression n)
    | Application (Expression n) (Expression n)
    | Let (Binding n) (Expression n)
    | Case (Expression n) [(Pattern n, Expression n)]
    | -- | Haskell's \cases
      Match [([Pattern n], Expression n)]
    | If (Expression n) (Expression n) (Expression n)
    | -- | value : Type
      Annotation (Expression n) (Type' n)
    | Name n
    | -- | .field.otherField.thirdField
      RecordLens (NonEmpty OpenName)
    | Constructor n
    | -- | 'Constructor
      -- unlike the rest of the cases, variant tags and record fields
      -- don't need any kind of name resolution
      Variant OpenName
    | Record (HashMap OpenName (Expression n))
    | List [Expression n]
    | IntLiteral Int
    | TextLiteral Text
    | CharLiteral Text
-}