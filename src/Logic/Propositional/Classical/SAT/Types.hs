{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingVia #-}

module Logic.Propositional.Classical.SAT.Types (
  Model (..),
  ProofResult (..),
  SatResult (..),
) where

import Control.DeepSeq (NFData)
import Data.HashSet (HashSet)
import Data.Hashable (Hashable)
import GHC.Generics

data Model a = Model {positive :: HashSet a, negative :: HashSet a}
  deriving (Show, Eq, Ord, Generic, Generic1, Foldable)
  deriving (Semigroup, Monoid) via Generically (Model a)
  deriving anyclass (Hashable, NFData)

data ProofResult a = Proven | Refuted a
  deriving (Show, Eq, Ord, Generic, Generic1, Foldable, Functor, Traversable)
  deriving anyclass (Hashable, NFData)

data SatResult a = Satisfiable a | Unsat
  deriving (Show, Eq, Ord, Generic, Generic1, Functor, Foldable, Traversable)
  deriving anyclass (Hashable, NFData)
