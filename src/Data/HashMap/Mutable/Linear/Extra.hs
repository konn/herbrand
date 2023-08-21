{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}

module Data.HashMap.Mutable.Linear.Extra (
  lookups,
  emptyL,
  fromListL,
  module Data.HashMap.Mutable.Linear,
) where

import Data.Alloc.Linearly.Token
import qualified Data.Array.Mutable.Linear.Extra as Array
import qualified Data.Array.Polarized.Push as Push
import Data.HashMap.Mutable.Linear
import Data.HashMap.Mutable.Linear.Internal
import Data.Hashable (Hashable)
import qualified Data.Vector as V
import qualified Data.Vector.Unboxed as U
import GHC.Stack (HasCallStack)
import Prelude.Linear hiding (lookup)
import Prelude hiding (lookup, mempty, seq, ($), (.))
import qualified Prelude as P

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
emptyL l size =
  let cap = P.max 1 size
   in HashMap 0 cap (Array.allocL l cap Nothing)

fromListL :: (Keyed k) => Linearly %1 -> [(k, v)] -> HashMap k v
fromListL l (xs :: [(k, v)]) =
  let cap =
        P.max
          1
          (ceiling @Float @Int (fromIntegral (Prelude.length xs) / constMaxLoadFactor))
   in insertAll
        xs
        (HashMap 0 cap (Array.allocL l cap Nothing))
