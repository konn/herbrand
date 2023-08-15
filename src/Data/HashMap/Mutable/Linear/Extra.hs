{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Data.HashMap.Mutable.Linear.Extra (
  lookups,
  module Data.HashMap.Mutable.Linear,
) where

import qualified Data.Array.Polarized.Push as Push
import Data.HashMap.Mutable.Linear
import Data.Hashable (Hashable)
import qualified Data.Vector as V
import qualified Data.Vector.Unboxed as U
import GHC.Stack (HasCallStack)
import Prelude.Linear hiding (lookup)
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
