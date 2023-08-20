{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Data.Set.Mutable.Linear.Extra (
  module Data.Set.Mutable.Linear,
  emptyL,
  fromListL,
) where

import Data.Alloc.Linearly.Token
import Data.Set.Mutable.Linear
import Prelude.Linear hiding (lookup)
import qualified Unsafe.Linear as Unsafe
import Prelude hiding (lookup, mempty, seq, ($), (.))

emptyL :: (Keyed a) => Linearly %1 -> Int -> Set a
emptyL l cap = l `lseq` unur (empty cap (Unsafe.toLinear Ur))

fromListL :: (Keyed a) => Linearly %1 -> [a] -> Set a
fromListL l as = l `lseq` unur (fromList as (Unsafe.toLinear Ur))
