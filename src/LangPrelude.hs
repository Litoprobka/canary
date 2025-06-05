{-# LANGUAGE ApplicativeDo #-}

module LangPrelude (module Reexport, (.>), traverseFold) where

-- Relude becomes inconvenient the moment I want to use effectful over mtl

import Data.EnumMap as Reexport (EnumMap)
import Data.EnumSet as Reexport (EnumSet)
import Effectful as Reexport
import Effectful.TH as Reexport
import IdMap as Reexport (IdMap)
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

traverseFold :: (Traversable t, Applicative f, Monoid m) => (a -> f (m, b)) -> t a -> f (m, t b)
traverseFold f t = do
    t' <- traverse f t
    pure (foldMap fst t', snd <$> t')
