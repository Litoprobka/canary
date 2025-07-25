{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}

module Trace where

import Data.DList (DList)
import Data.DList qualified as DList
import Effectful.Dispatch.Dynamic (interpret, localSeqUnlift, reinterpret)
import Effectful.State.Static.Local
import LangPrelude
import Prettyprinter (hardline, indent)
import Prettyprinter.Render.Terminal (AnsiStyle, putDoc)

data Trace :: Effect where
    TraceScope :: (a -> Doc AnsiStyle) -> m a -> Trace m a
    Trace :: Doc AnsiStyle -> Trace m ()

makeEffect ''Trace

traceScope_ :: Trace :> es => Doc AnsiStyle -> Eff es a -> Eff es a
traceScope_ doc = traceScope (const doc)

data TraceTree
    = Branch (Doc AnsiStyle) [TraceTree]

-- | run 'Trace' effect by ignoring all produced traces
skipTrace :: Eff (Trace : es) a -> Eff es a
skipTrace = interpret \env -> \case
    TraceScope _ action -> localSeqUnlift env \unlift -> unlift action
    Trace _ -> pass

runTrace :: Eff (Trace : es) a -> Eff es (a, [TraceTree])
runTrace = reinterpret (fmap (second toList) . runState @(DList TraceTree) mempty) \env -> \case
    Trace doc -> modify (`DList.snoc` Branch doc [])
    TraceScope mkDoc action -> do
        -- todo: I think we lose the whole branch on exception
        (output, traces) <- scoped $ localSeqUnlift env \unlift -> unlift action
        modify (`DList.snoc` Branch (mkDoc output) (toList traces))
        pure output
  where
    -- effectful doesn't provide 'censor' for its writer effect, so we have to stick to State
    -- plain 'runWriter' could work instead, but juggling effects is annoying
    scoped action = do
        current <- get
        put @(DList TraceTree) mempty
        output <- action
        new <- get @(DList TraceTree)
        put @(DList TraceTree) current
        pure (output, new)

-- | run 'Trace' effect by printing collected traces to stdout
runTraceIO :: IOE :> es => Eff (Trace : es) a -> Eff es a
runTraceIO action = do
    (output, traceForest) <- runTrace action
    unless (null traceForest) do
        liftIO $ putTextLn "\nTrace:"
        liftIO (putDoc $ prettyTraces traceForest <> hardline)
    pure output

prettyTraces :: [TraceTree] -> Doc AnsiStyle
prettyTraces = \case
    [] -> ""
    [child] -> "╰╴" <> prettyTrace child
    (child : rest) -> "├╴" <> prettyTrace child <> hardline <> prettyTraces rest
  where
    prettyTrace = \case
        Branch doc [] -> doc
        Branch doc nested -> doc <> hardline <> indent 2 (prettyTraces nested)
