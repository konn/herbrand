{-# LANGUAGE GHC2021 #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}

module Logic.Theory.Decision.DPLL.Abstract where

import Control.DeepSeq
import Data.Hashable (Hashable)
import GHC.Generics (Generic, Generic1)

-- | A literal is mere a atomic formula or its negation.
data Literal a = Positive !a | Negative !a
  deriving (Show, Eq, Ord, Generic, Generic1, Functor, Foldable, Traversable)
  deriving anyclass (Hashable, NFData)

data Context atom = Assumption [atom]
  deriving (Show, Eq, Ord, Generic)
