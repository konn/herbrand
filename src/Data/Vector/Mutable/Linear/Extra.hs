{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Data.Vector.Mutable.Linear.Extra (
  imapAccumL',
  find,
  module Data.Vector.Mutable.Linear,
) where

import Data.Unrestricted.Linear
import Data.Vector.Mutable.Linear
import Prelude.Linear ((&))

imapAccumL' ::
  forall s a.
  (Int -> s %1 -> a -> (s, Ur a)) ->
  s %1 ->
  Vector a %1 ->
  (s, Vector a)
imapAccumL' f = go 0
  where
    go :: Int -> s %1 -> Vector a %1 -> (s, Vector a)
    go !i !s !v =
      size v & \(Ur l, v') ->
        if i >= l
          then (s, v')
          else
            unsafeGet i v' & \(Ur a, v'') ->
              f i s a & \(s', Ur a') ->
                go (i + 1) s' (unsafeSet i a' v'')

find :: forall a. (a -> Bool) -> Vector a %1 -> (Ur (Maybe (a, Int)), Vector a)
find p = go 0
  where
    go :: Int -> Vector a %1 -> (Ur (Maybe (a, Int)), Vector a)
    go !i !v =
      size v & \(Ur l, v) ->
        if i >= l
          then (Ur Nothing, v)
          else
            unsafeGet i v & \(Ur a, v) ->
              if p a
                then (Ur (Just (a, i)), v)
                else go (i + 1) v
