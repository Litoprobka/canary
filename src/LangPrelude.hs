module LangPrelude (module Reexport, (.>)) where

-- Relude becomes inconvenient the moment I want to use effectful over mtl

import Relude as Reexport hiding (State, get, gets, put, modify, modify', state, Op, runState, evalState, execState, Reader, ask, asks, local, runReader, some, many)
import Effectful as Reexport
import Effectful.TH as Reexport
import Prettyprinter as Reexport (Doc, Pretty(..), (<+>))

infixl 9 .>

(.>) :: (a -> b) -> (b -> c) -> a -> c
(.>) = flip (.)