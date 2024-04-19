{-# LANGUAGE LambdaCase #-}

module NameResolution where

import Relude

import Data.IntMap.Strict qualified as IntMap
import Syntax.All
import Syntax.Declaration qualified as D

newtype Id = Id Int

data Env = Env {maxId :: Id, names :: IntMap Text}
newtype LocalEnv = LocalEnv (HashMap Text [Id])

newId :: Text -> State Env Id
newId = undefined

resolveNames :: [Declaration Text] -> ([Declaration Id], Env)
resolveNames decls = traverse resolveDec decls `runState` globalScope
  where
    globalScope = (`execState` Env (Id 0) IntMap.empty) $ for_ decls \case
        D.Value name _ _ _ ->
        D.Type name vars constrs ->
        D.Alias alias name ->
        D.Signature name ty ->

    resolveDec = undefined