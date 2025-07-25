{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE ViewPatterns #-}

module LangPrelude (module Reexport, (.>), traverseFold, pattern (:<), pattern (:>), pattern Nil) where

-- Relude becomes inconvenient the moment I want to use effectful over mtl

import Data.EnumMap as Reexport (EnumMap)
import Data.EnumSet as Reexport (EnumSet)
import Data.IdMap as Reexport (IdMap)
import Data.Traversable as Reexport (for)
import Data.Vector as Reexport (Vector)
import Data.Vector qualified as Vec
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
    trace,
 )

infixl 9 .>
infixr 5 :<
infixl 5 :>

(.>) :: (a -> b) -> (b -> c) -> a -> c
(.>) = flip (.)

traverseFold :: (Traversable t, Applicative f, Monoid m) => (a -> f (m, b)) -> t a -> f (m, t b)
traverseFold f t = do
    t' <- traverse f t
    pure (foldMap fst t', snd <$> t')

pattern Nil :: Vector a
pattern Nil <- (Vec.null -> True)
    where
        Nil = Vec.empty

pattern (:<) :: a -> Vector a -> Vector a
pattern x :< xs <- (Vec.uncons -> Just (x, xs))
    where
        (:<) = Vec.cons

pattern (:>) :: Vector a -> a -> Vector a
pattern xs :> x <- (Vec.unsnoc -> Just (xs, x))
    where
        (:>) = Vec.snoc
