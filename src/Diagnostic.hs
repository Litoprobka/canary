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
    runDiagnose',
    dummy,
    nonFatal,
    fatal,
    noErrors,
    internalError,
    reportExceptions,
    guardNoErrors,
    internalError',
) where

import Common (Loc, mkNotes)
import Data.DList (DList)
import Data.DList qualified as DList
import Effectful
import Effectful.Dispatch.Dynamic
import Effectful.Error.Static (runErrorNoCallStack, throwError_)
import Effectful.Exception (ErrorCall, handle)
import Effectful.State.Static.Local (gets, modify, runState)
import Effectful.TH
import Error.Diagnose
import LangPrelude
import Prettyprinter.Render.Terminal (AnsiStyle)

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
runDiagnose' (filePath, fileContents) =
    reinterpret
        (fmap (joinReports . second diagnosticFromReports) . runState DList.empty . runErrorNoCallStack)
        ( \_ -> \case
            NonFatal report -> modify (`DList.snoc` report)
            Fatal reports -> throwError_ reports
            NoErrors ->
                gets @(DList (Report (Doc AnsiStyle)))
                    ( all \case
                        Err{} -> False
                        Warn{} -> True
                    )
        )
        . reportExceptions @ErrorCall
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

-- | An internal error without location info
internalError' :: Diagnose :> es => Doc AnsiStyle -> Eff es a
internalError' msg = fatal . one $ Err Nothing ("Internal error:" <+> msg) [] []

-- | treat accumulated errors as fatal
guardNoErrors :: Diagnose :> es => Eff es ()
guardNoErrors = do
    ok <- noErrors
    unless ok $ fatal []

{-
-- this is 90% copypasted from Error.Diagnose.Compat.Megaparsec, because enabling the feature flag
-- hangs the compiler for some reason

reportsFromBundle
    :: forall s e
     . (MP.ShowErrorComponent e, MP.VisualStream s, HasLoc (MP.Token s))
    => MP.ParseErrorBundle s e
    -> NonEmpty (Report (Doc AnsiStyle))
reportsFromBundle MP.ParseErrorBundle{..} =
    toLabeledPosition <$> bundleErrors
  where
    toLabeledPosition :: MP.ParseError s e -> Report (Doc AnsiStyle)
    toLabeledPosition parseError =
        let source = case parseError of
                MP.TrivialError _ (Just (MP.Tokens (tok :| _))) _ -> getLoc tok
                _ -> C.Blank
            msgs = fmap (pretty @_ @AnsiStyle . toString) $ lines $ toText (MP.parseErrorTextPretty parseError)
         in flip
                (Err Nothing "Parse error")
                []
                case msgs of
                    [m] -> mkNotes [(source, This m)]
                    (m1 : rest) -> mkNotes $ (source, This m1) : map ((source,) . Where) rest
                    [] -> mkNotes [(source, This "no error message")]
-}
