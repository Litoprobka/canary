{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}

module Diagnostic (Diagnose, runDiagnose, runDiagnose', dummy, nonFatal, fatal) where

import Effectful
import Effectful.Dispatch.Dynamic
import Effectful.Error.Static (runErrorNoCallStack, throwError)
import Effectful.State.Static.Shared (modify, runState)
import Effectful.TH
import Error.Diagnose
import Prettyprinter (Doc)
import Relude hiding (modify, runState)
import Prettyprinter.Render.Terminal (AnsiStyle)

data Diagnose :: Effect where
    NonFatal :: Report (Doc AnsiStyle) -> Diagnose m ()
    Fatal :: Report (Doc AnsiStyle) -> Diagnose m a

makeEffect ''Diagnose

runDiagnose :: IOE :> es => (FilePath, Text) -> Eff (Diagnose : es) a -> Eff es (Maybe a)
runDiagnose file action = do
  (mbVal, diagnostic) <- runDiagnose' file action
  printDiagnostic' stdout WithUnicode (TabSize 4) defaultStyle diagnostic
  pure mbVal

runDiagnose' :: (FilePath, Text) -> Eff (Diagnose : es) a -> Eff es (Maybe a, Diagnostic (Doc AnsiStyle))
runDiagnose' (filePath, fileContents) = reinterpret
    (fmap eitherToPair . runErrorNoCallStack . runState (addFile mempty filePath $ toString fileContents))
    \_ -> \case
        NonFatal report -> modify $ flip addReport report
        Fatal report -> throwError report
  where
    eitherToPair = \case
        Left fatalError -> (Nothing, addReport mempty fatalError)
        Right (val, reports) -> (Just val, reports)

dummy :: Doc style -> Report (Doc style)
dummy msg = Err Nothing msg [] []