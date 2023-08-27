{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Data.Vector.Mutable.Linear.Helpers (
  imapAccumL',
  findWith,
  module Data.Vector.Mutable.Linear.Extra,
  ifindIndexM,
  ifindWithIndexM,
  allFirstN,
  unsafeFindAtWith,
) where

import Control.Functor.Linear (Monad, pure)
import qualified Control.Functor.Linear as C
import Data.Unrestricted.Linear
import Data.Vector.Mutable.Linear.Extra
import Prelude.Linear

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
  (b %1 -> a -> (Ur (Maybe c), b)) ->
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
              p b a & \case
                (Ur (Just c), b) -> (Ur (Just (c, i)), b, v)
                (Ur Nothing, b) -> go (i + 1) b v

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

ifindWithIndexM :: (Monad m) => (Int -> a -> m (Ur (Maybe b))) -> Vector a %1 -> m (Ur (Maybe (b, Int)), Vector a)
ifindWithIndexM (p :: Int -> a -> m (Ur (Maybe b))) v = size v & \(Ur sz, v) -> go 0 sz v
  where
    go :: Int -> Int -> Vector a %1 -> m (Ur (Maybe (b, Int)), Vector a)
    go !i !j !arr
      | i == j = pure (Ur Nothing, arr)
      | otherwise =
          unsafeGet i arr & \(Ur a, arr) -> C.do
            Ur mb <- p i a
            case mb of
              Nothing -> go (i + 1) j arr
              Just b -> pure (Ur (Just (b, i)), arr)

ifindIndexM :: (Monad m) => (Int -> a -> m Bool) -> Vector a %1 -> m (Ur (Maybe Int), Vector a)
ifindIndexM (p :: Int -> a -> m Bool) v = size v & \(Ur sz, v) -> go 0 sz v
  where
    go :: Int -> Int -> Vector a %1 -> m (Ur (Maybe Int), Vector a)
    go !i !j !arr
      | i == j = pure (Ur Nothing, arr)
      | otherwise =
          unsafeGet i arr & \(Ur a, arr) -> C.do
            b <- p i a
            if b
              then pure (Ur (Just i), arr)
              else go (i + 1) j arr

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
