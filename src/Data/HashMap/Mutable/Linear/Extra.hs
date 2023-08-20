{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Data.HashMap.Mutable.Linear.Extra (
  lookups,
  emptyL,
  fromListL,
  module Data.HashMap.Mutable.Linear,
) where

import Data.Alloc.Linearly.Token
import qualified Data.Array.Polarized.Push as Push
import Data.HashMap.Mutable.Linear
import Data.Hashable (Hashable)
import qualified Data.Vector as V
import qualified Data.Vector.Unboxed as U
import GHC.Stack (HasCallStack)
import Prelude.Linear hiding (lookup)
import qualified Unsafe.Linear as Unsafe
import Prelude hiding (lookup, mempty, seq, ($), (.))

lookups ::
  forall key v.
  (HasCallStack, Hashable key, U.Unbox key) =>
  U.Vector key ->
  HashMap key v %1 ->
  (V.Vector (Maybe v), HashMap key v)
{-# INLINE lookups #-}
lookups = go mempty
  where
    go :: (HasCallStack) => Push.Array (Maybe v) %1 -> U.Vector key -> HashMap key v %1 -> (V.Vector (Maybe v), HashMap key v)
    go !arr !uv !hm
      | U.null uv = (Push.alloc arr, hm)
      | otherwise =
          lookup (U.unsafeHead uv) hm & \(Ur m, hm) ->
            go (Push.snoc m arr) (U.unsafeTail uv) hm

emptyL :: (Keyed k) => Linearly %1 -> Int -> HashMap k v
emptyL l n = l `lseq` unur (empty n (Unsafe.toLinear Ur))

fromListL :: (Keyed k) => Linearly %1 -> [(k, v)] -> HashMap k v
fromListL l n = l `lseq` unur (fromList n (Unsafe.toLinear Ur))
