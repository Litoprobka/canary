{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}

module NameGen (runNameGen, freshId, freshName, freshName_, NameGen) where

import Common (Id (..), Located (..), Name, Name_ (..), SimpleName, SimpleName_ (..))
import Effectful.Dispatch.Dynamic (reinterpret_)
import Effectful.State.Static.Local (evalState, get, modify)
import LangPrelude

data NameGen :: Effect where
    FreshId :: NameGen m Id

makeEffect ''NameGen

freshName :: NameGen :> es => SimpleName -> Eff es Name
freshName (name :@ loc) = (:@ loc) <$> freshName_ name

freshName_ :: NameGen :> es => SimpleName_ -> Eff es Name_
freshName_ = \case
    Name' name -> Name name <$> freshId
    Wildcard' name -> Wildcard name <$> freshId

runNameGen :: Eff (NameGen : es) a -> Eff es a
runNameGen = reinterpret_ (evalState $ Id 0) \FreshId -> get <* modify (succ @Id)
