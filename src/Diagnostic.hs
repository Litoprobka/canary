{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Diagnostic (Diagnose, runDiagnose, runDiagnose', dummy, nonFatal, fatal, noErrors, reportsFromBundle, internalError, reportExceptions, guardNoErrors) where

import Common (Loc, mkNotes)
import Data.DList (DList)
import Data.DList qualified as DList
import Effectful
import Effectful.Dispatch.Dynamic
import Effectful.Error.Static (runErrorNoCallStack, throwError_)
import Effectful.State.Static.Local (gets, modify, runState)
import Effectful.TH
import Effectful.Exception (handle, ErrorCall)
import Error.Diagnose
import LangPrelude
import Prettyprinter.Render.Terminal (AnsiStyle)
import Text.Megaparsec qualified as MP

data Diagnose :: Effect where
    NonFatal :: Report (Doc AnsiStyle) -> Diagnose m ()
    Fatal :: [Report (Doc AnsiStyle)] -> Diagnose m a
    NoErrors :: Diagnose m Bool

makeEffect ''Diagnose

runDiagnose :: IOE :> es => (FilePath, Text) -> Eff (Diagnose : es) a -> Eff es (Maybe a)
runDiagnose file action = do
    (mbVal, diagnostic) <- runDiagnose' file action
    printDiagnostic' stdout WithUnicode (TabSize 4) defaultStyle diagnostic
    pure mbVal

runDiagnose' :: (FilePath, Text) -> Eff (Diagnose : es) a -> Eff es (Maybe a, Diagnostic (Doc AnsiStyle))
runDiagnose' (filePath, fileContents) = reinterpret
    (fmap (joinReports . second diagnosticFromReports) . runState DList.empty . runErrorNoCallStack)
    (\_ -> \case
        NonFatal report -> modify (`DList.snoc` report)
        Fatal reports -> throwError_ reports
        NoErrors ->
            gets @(DList (Report (Doc AnsiStyle)))
                ( all \case
                    Err{} -> False
                    Warn{} -> True
                )
    ) . reportExceptions @ErrorCall
  where
    baseDiagnostic = addFile mempty filePath $ toString fileContents
    diagnosticFromReports = foldl' @DList addReport baseDiagnostic
    joinReports = \case
        (Left fatalErrors, diagnostic) -> (Nothing, foldl' @[] addReport diagnostic fatalErrors)
        (Right val, diagnostic) -> (Just val, diagnostic)

-- apparently `withSync` catches internal exceptions that are used by the Error effect. meh.
reportExceptions :: forall exc es a. (Diagnose :> es, Exception exc) => Eff es a -> Eff es a
reportExceptions = handle @exc \exc -> fatal . one $ Err Nothing ("An exception has occured:" <+> pretty (displayException exc)) [] []

dummy :: Doc style -> Report (Doc style)
dummy msg = Err Nothing msg [] []

-- | An internal error. That is, something that may only be caused by a compiler bug
internalError :: Diagnose :> es => Loc -> Doc AnsiStyle -> Eff es a
internalError loc msg = fatal . one $ Err Nothing ("Internal error:" <+> msg) (mkNotes [(loc, This "arising from")]) []

-- | treat accumulated errors as fatal
guardNoErrors :: Diagnose :> es => Eff es ()
guardNoErrors = do
    ok <- noErrors
    unless ok $ fatal []

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
