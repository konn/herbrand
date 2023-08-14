{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Data.Vector.Mutable.Linear.Extra (
  imapAccumL',
  findWith,
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

findWith ::
  forall a b c.
  (b %1 -> Int -> a -> (Ur (Maybe c), b)) ->
  b %1 ->
  Vector a %1 ->
  (Ur (Maybe (c, Int)), b, Vector a)
findWith p = go 0
  where
    go :: Int -> b %1 -> Vector a %1 -> (Ur (Maybe (c, Int)), b, Vector a)
    go !i !b !v =
      size v & \(Ur l, v) ->
        if i >= l
          then (Ur Nothing, b, v)
          else
            unsafeGet i v & \(Ur a, v) ->
              p b i a & \case
                (Ur (Just c), b) -> (Ur (Just (c, i)), b, v)
                (Ur Nothing, b) -> go (i + 1) b v
