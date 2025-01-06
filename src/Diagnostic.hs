{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}

module Diagnostic (Diagnose, runDiagnose, runDiagnose', dummy, nonFatal, fatal, reportsFromBundle) where

import Data.DList (DList)
import Data.DList qualified as DList
import Effectful
import Effectful.Dispatch.Dynamic
import Effectful.Error.Static (runErrorNoCallStack, throwError)
import Effectful.TH
import Effectful.Writer.Static.Shared (runWriter, tell)
import Error.Diagnose
import Prettyprinter.Render.Terminal (AnsiStyle)
import LangPrelude
import Text.Megaparsec qualified as MP

-- I'm not sure why fourmolu decided to use 2-space idents for this file

data Diagnose :: Effect where
  NonFatal :: Report (Doc AnsiStyle) -> Diagnose m ()
  Fatal :: NonEmpty (Report (Doc AnsiStyle)) -> Diagnose m a

makeEffect ''Diagnose

runDiagnose :: IOE :> es => (FilePath, Text) -> Eff (Diagnose : es) a -> Eff es (Maybe a)
runDiagnose file action = do
  (mbVal, diagnostic) <- runDiagnose' file action
  printDiagnostic' stdout WithUnicode (TabSize 4) defaultStyle diagnostic
  pure mbVal

runDiagnose' :: (FilePath, Text) -> Eff (Diagnose : es) a -> Eff es (Maybe a, Diagnostic (Doc AnsiStyle))
runDiagnose' (filePath, fileContents) = reinterpret
  (fmap (joinReports . second diagnosticFromReports) . runWriter . runErrorNoCallStack)
  -- (addFile mempty filePath $ toString fileContents)
  \_ -> \case
    NonFatal report -> tell $ DList.singleton report
    Fatal reports -> throwError reports
 where
  baseDiagnostic = addFile mempty filePath $ toString fileContents
  diagnosticFromReports = foldl' @DList addReport baseDiagnostic
  joinReports = \case
    (Left fatalErrors, diagnostic) -> (Nothing, foldl' @NonEmpty addReport diagnostic fatalErrors)
    (Right val, diagnostic) -> (Just val, diagnostic)

dummy :: Doc style -> Report (Doc style)
dummy msg = Err Nothing msg [] []

-- this is 90% copypasted from Error.Diagnose.Compat.Megaparsec, because enabling the feature flag
-- hangs the compiler for some reason

reportsFromBundle
  :: forall s e
   . (MP.ShowErrorComponent e, MP.VisualStream s, MP.TraversableStream s)
  => MP.ParseErrorBundle s e
  -> NonEmpty (Report (Doc AnsiStyle))
reportsFromBundle MP.ParseErrorBundle{..} =
  toLabeledPosition <$> bundleErrors
 where
  toLabeledPosition :: MP.ParseError s e -> Report (Doc AnsiStyle)
  toLabeledPosition parseError =
    let (_, pos) = MP.reachOffset (MP.errorOffset parseError) bundlePosState
        source = fromSourcePos (MP.pstateSourcePos pos)
        msgs = fmap (pretty @_ @AnsiStyle . toString) $ lines $ toText (MP.parseErrorTextPretty parseError)
     in flip
          (Err Nothing "Parse error")
          []
          case msgs of
            [m] -> [(source, This m)]
            [m1, m2] -> [(source, This m1), (source, Where m2)]
            _ -> [(source, This "<<Unknown error>>")]

  fromSourcePos :: MP.SourcePos -> Position
  fromSourcePos MP.SourcePos{..} =
    let start = bimap MP.unPos MP.unPos (sourceLine, sourceColumn)
        end = second (+ 1) start
     in Position start end sourceName
