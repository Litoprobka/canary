{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module ParsecEffect where

import Relude hiding (lift)
import Effectful
import Effectful.TH
import Text.Megaparsec
import Effectful.NonDet (NonDet)
import Effectful.Dispatch.Dynamic (interpret)


data Parser :: Effect where
    Lift :: ParsecT Void Text m a -> Parser m a

makeEffect ''Parser

--runParser :: Eff (Parser : es) a -> Eff es (Either (ParseErrorBundle Text Void) a)
--runParser = interpret \_ (Lift action) -> _fix $ runParserT action

{-
unlift :: (Parser :> es, NonDet :> es) => Eff es a -> ParsecT e s (Eff es) a
unlift = undefined



instance (NonDet :> es) => MonadParsec Void Text (Eff (Parser : es)) where
  parseError = lift . parseError
  label str action = lift $ label str $ unlift action
  hidden = lift . hidden . unlift
  try = lift . try . unlift
  lookAhead = lift . lookAhead . unlift
  notFollowedBy = lift . notFollowedBy . unlift
  withRecovery recover action = lift $ withRecovery (unlift . recover) $ unlift action
  observing = lift . observing . unlift
  eof = lift eof
  token match' errs = lift $ token match' errs
  tokens cmp tok = lift $ tokens cmp tok
  takeWhileP lbl p = lift $ takeWhileP lbl p
  takeWhile1P lbl p = lift $ takeWhile1P lbl p 
  takeP lbl n = lift $ takeP lbl n
  getParserState = lift getParserState
  updateParserState = lift . updateParserState
  mkParsec = lift . mkParsec
-}
