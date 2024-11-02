{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DeriveAnyClass #-}
module NameGen (runNameGen, freshId, freshName, freshName_, NameGen) where

import Relude hiding (evalState, get, modify)
import Common (Id (..), inc, Name, SimpleName, SimpleName_(..), Located (..), Name_ (..))
import Effectful
import Effectful.TH
import Effectful.State.Static.Local (evalState, get, modify)
import Effectful.Dispatch.Dynamic (reinterpret)

data NameGen :: Effect where
    FreshId :: NameGen m Id

makeEffect ''NameGen

freshName :: (NameGen :> es) => SimpleName -> Eff es Name
freshName (Located loc name) = Located loc <$> freshName_ name

freshName_ :: NameGen :> es => SimpleName_ -> Eff es Name_
freshName_ = \case
    Name' name -> Name name <$> freshId
    Wildcard' n -> Wildcard n <$> freshId

runNameGen :: Eff (NameGen : es) a -> Eff es a
runNameGen = reinterpret (evalState $ Id 0) \_ FreshId -> get <* modify inc
