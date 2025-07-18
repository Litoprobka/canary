{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}

module Diagnostic (
    Diagnose,
    runDiagnose,
    runDiagnoseWith,
    runDiagnose',
    runDiagnoseWith',
    nonFatal,
    fatal,
    noErrors,
    currentLoc,
    localLoc,
    internalError,
    internalError',
    reportExceptions,
    guardNoErrors,
) where

import Common (Loc, mkNotes)
import Data.DList (DList)
import Data.DList qualified as DList
import Effectful
import Effectful.Dispatch.Dynamic
import Effectful.Error.Static (runErrorNoCallStack, throwError_)
import Effectful.Exception (ErrorCall, handle)
import Effectful.Reader.Static (ask, local, runReader)
import Effectful.State.Static.Local (gets, modify, runState)
import Effectful.TH
import Error.Diagnose
import LangPrelude
import Prettyprinter.Render.Terminal (AnsiStyle)

data Diagnose :: Effect where
    NonFatal :: Report (Doc AnsiStyle) -> Diagnose m ()
    Fatal :: [Report (Doc AnsiStyle)] -> Diagnose m a
    LocalLoc :: Loc -> m a -> Diagnose m a
    CurrentLoc :: Diagnose m (Maybe Loc)
    NoErrors :: Diagnose m Bool

makeEffect ''Diagnose

-- | run `Diagnose` by printing all accumulated diagnostics to stdout
runDiagnose :: IOE :> es => [(FilePath, Text)] -> Eff (Diagnose : es) a -> Eff es (Maybe a)
runDiagnose files action = do
    (mbVal, diagnostic) <- runDiagnose' files action
    printDiagnostic' stdout WithUnicode (TabSize 4) defaultStyle diagnostic
    pure mbVal

-- | like `runDiagnose`, but with an initial non-empty diagnostic
runDiagnoseWith :: IOE :> es => Diagnostic (Doc AnsiStyle) -> Eff (Diagnose : es) a -> Eff es (Maybe a)
runDiagnoseWith baseDiagnostic action = do
    (mbVal, diagnostic) <- runDiagnoseWith' baseDiagnostic action
    printDiagnostic' stdout WithUnicode (TabSize 4) defaultStyle diagnostic
    pure mbVal

-- | run `Diagnose` by returning all accumulated diagnostics
runDiagnose' :: [(FilePath, Text)] -> Eff (Diagnose : es) a -> Eff es (Maybe a, Diagnostic (Doc AnsiStyle))
runDiagnose' files = runDiagnoseWith' baseDiagnostic
  where
    baseDiagnostic = foldr (\(filePath, fileContents) acc -> addFile acc filePath (toString fileContents)) mempty files

-- | like `runDiagnose'`, but with an initial non-empty diagnostic
runDiagnoseWith' :: Diagnostic (Doc AnsiStyle) -> Eff (Diagnose : es) a -> Eff es (Maybe a, Diagnostic (Doc AnsiStyle))
runDiagnoseWith' baseDiagnostic =
    reinterpret
        ( fmap (joinReports . second diagnosticFromReports) . runState DList.empty . runReader @(Maybe Loc) Nothing . runErrorNoCallStack
        )
        ( \env -> \case
            NonFatal report -> modify (`DList.snoc` report)
            Fatal reports -> throwError_ reports
            LocalLoc loc action -> local (const $ Just loc) (localSeqUnlift env \unlift -> unlift action)
            CurrentLoc -> ask
            NoErrors ->
                gets @(DList (Report (Doc AnsiStyle)))
                    ( all \case
                        Err{} -> False
                        Warn{} -> True
                    )
        )
        . reportExceptions @ErrorCall
  where
    diagnosticFromReports = foldl' @DList addReport baseDiagnostic
    joinReports = \case
        (Left fatalErrors, diagnostic) -> (Nothing, foldl' @[] addReport diagnostic fatalErrors)
        (Right val, diagnostic) -> (Just val, diagnostic)

-- apparently `handleSync` catches internal exceptions that are used by the Error effect. meh.
reportExceptions :: forall exc es a. (Diagnose :> es, Exception exc) => Eff es a -> Eff es a
reportExceptions = handle @exc \exc -> do
    -- not sure whether this call to `currentLoc` would pick up the right location
    mbLoc <- currentLoc
    let notes = mkNotes $ maybeToList $ mbLoc <&> (,This "arising from")
    fatal . one $ Err Nothing ("An exception has occured:" <+> pretty (displayException exc)) notes []

-- | An internal error. That is, something that may only be caused by a compiler bug
internalError :: Diagnose :> es => Loc -> Doc AnsiStyle -> Eff es a
internalError loc msg = fatal . one $ Err Nothing ("Internal error:" <+> msg) (mkNotes [(loc, This "arising from")]) []

-- | An internal error with no explicit location information
internalError' :: Diagnose :> es => Doc AnsiStyle -> Eff es a
internalError' msg = do
    mbLoc <- currentLoc
    let notes = mkNotes $ maybeToList $ mbLoc <&> (,This "arising from")
    fatal . one $ Err Nothing ("Internal error:" <+> msg) notes []

-- | treat accumulated errors as fatal
guardNoErrors :: Diagnose :> es => Eff es ()
guardNoErrors = do
    ok <- noErrors
    unless ok $ fatal []
