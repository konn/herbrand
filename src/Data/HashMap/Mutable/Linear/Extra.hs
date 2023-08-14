{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Data.HashMap.Mutable.Linear.Extra (
  backpermute,
  module Data.HashMap.Mutable.Linear,
) where

import qualified Data.Array.Polarized.Push as Push
import Data.HashMap.Mutable.Linear
import Data.Hashable (Hashable)
import qualified Data.Vector.Unboxed as U
import GHC.Stack (HasCallStack)
import Prelude.Linear hiding (lookup)
import qualified Unsafe.Linear as Unsafe
import Prelude hiding (lookup, mempty, seq, ($), (.))

backpermute ::
  forall key v.
  (HasCallStack, Hashable key, U.Unbox key, Consumable v, U.Unbox v) =>
  U.Vector key ->
  HashMap key v %1 ->
  (U.Vector v, HashMap key v)
{-# INLINE backpermute #-}
backpermute = go mempty
  where
    go :: (HasCallStack) => Push.Array v %1 -> U.Vector key -> HashMap key v %1 -> (U.Vector v, HashMap key v)
    go !arr !uv !hm
      | U.null uv = (Unsafe.toLinear U.convert (Push.alloc arr), hm)
      | otherwise =
          lookup (U.unsafeHead uv) hm & \case
            (Ur Nothing, hm) -> Push.alloc arr `lseq` hm `lseq` error "backpermute: Index out of bounds"
            (Ur (Just v), hm) ->
              go (Push.snoc v arr) (U.unsafeTail uv) hm
