{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}

module Data.Set.Mutable.Linear.Extra (
  module Data.Set.Mutable.Linear,
  emptyL,
  fromListL,
) where

import Data.Alloc.Linearly.Token
import qualified Data.HashMap.Mutable.Linear.Extra as LHM
import Data.Set.Mutable.Linear
import Data.Set.Mutable.Linear.Internal
import Prelude.Linear hiding (lookup)
import qualified Prelude.Linear as P
import Prelude hiding (lookup, mempty, seq, ($), (.))

emptyL :: (Keyed a) => Linearly %1 -> Int -> Set a
emptyL l cap = Set (LHM.emptyL l cap)

fromListL :: (Keyed a) => Linearly %1 -> [a] -> Set a
fromListL l as = Set (LHM.fromListL l (P.map (,()) as))
