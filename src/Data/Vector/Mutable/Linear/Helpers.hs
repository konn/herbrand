{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Data.Vector.Mutable.Linear.Helpers (
  module Data.Vector.Mutable.Linear.Extra,
  allFirstN,
  unsafeFindAtWith,
) where

import Data.Unrestricted.Linear
import Data.Vector.Mutable.Linear.Extra
import Prelude.Linear

unsafeFindAtWith ::
  forall a b c.
  (b %1 -> a -> (Ur (Maybe c), b)) ->
  b %1 ->
  [Int] ->
  Vector a %1 ->
  (Ur (Maybe (c, Int)), b, Vector a)
unsafeFindAtWith p = go
  where
    go :: b %1 -> [Int] -> Vector a %1 -> (Ur (Maybe (c, Int)), b, Vector a)
    go !b [] !v = (Ur Nothing, b, v)
    go !b (!i : !is) !v =
      unsafeGet i v & \(Ur a, v) ->
        p b a & \case
          (Ur (Just c), b) -> (Ur (Just (c, i)), b, v)
          (Ur Nothing, b) -> go b is v

allFirstN :: Int -> (a -> Bool) -> Vector a %1 -> (Ur Bool, Vector a)
allFirstN n0 (p :: a -> Bool) v = size v & \(Ur n, v) -> go 0 (max 0 $ min n n0) v
  where
    go :: Int -> Int -> Vector a %1 -> (Ur Bool, Vector a)
    go !i !n !v
      | i == n = (Ur True, v)
      | otherwise =
          unsafeGet i v & \(Ur x, v) ->
            p x & \case
              True -> go (i + 1) n v
              False -> (Ur False, v)
