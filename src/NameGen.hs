{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
module NameGen (runNameGen, freshId, freshName, NameGen) where

import Relude hiding (evalState, get, modify)
import Common (Id (..), inc, Name (..), Loc)
import Effectful
import Effectful.TH
import Effectful.State.Static.Local (evalState, get, modify)
import Effectful.Dispatch.Dynamic (reinterpret)

data NameGen :: Effect where
    FreshId :: NameGen m Id

makeEffect ''NameGen

freshName :: (NameGen :> es) => Loc -> Text -> Eff es Name
freshName loc name = Name loc name <$> freshId

runNameGen :: Eff (NameGen : es) a -> Eff es a
runNameGen = reinterpret (evalState $ Id 0) \_ FreshId -> get <* modify inc
