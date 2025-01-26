module LangPrelude (module Reexport, (.>)) where

-- Relude becomes inconvenient the moment I want to use effectful over mtl

import Effectful as Reexport
import Effectful.TH as Reexport
import Prettyprinter as Reexport (Doc, Pretty (..), (<+>))
import Relude as Reexport hiding (
    Op,
    Reader,
    State,
    Type,
    ask,
    asks,
    evalState,
    execState,
    get,
    gets,
    local,
    many,
    modify,
    modify',
    put,
    runReader,
    runState,
    some,
    state,
 )

infixl 9 .>

(.>) :: (a -> b) -> (b -> c) -> a -> c
(.>) = flip (.)
