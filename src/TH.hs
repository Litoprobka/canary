{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TemplateHaskell #-}

module TH (matches) where

import Language.Haskell.TH
import Relude
import Text.Megaparsec (ErrorItem (Tokens), anySingle, unexpected)

matches :: Name -> Q Exp
matches con =
    -- fourmolu is being weird today
    [|
        try $
            anySingle >>= \case
                $conCase -> pure $(varE txt)
                tok -> unexpected $ Tokens $ tok :| []
        |]
  where
    conCase = pure $ ConP con [] [VarP txt]
    txt = mkName "txt"