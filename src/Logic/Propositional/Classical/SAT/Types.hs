{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

module Logic.Propositional.Classical.SAT.Types (
  Model (..),
  ProofResult (..),
  SatResult (..),
  eval,
) where

import Control.DeepSeq (NFData)
import Data.Functor.Foldable
import Data.HashSet (HashSet)
import qualified Data.HashSet as HS
import Data.Hashable (Hashable)
import GHC.Generics
import Logic.Propositional.Syntax.General

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

eval :: (Hashable v) => Model v -> Formula e v -> Maybe Bool
eval Model {..} = cata \case
  AtomF v
    | v `HS.member` positive -> Just True
    | v `HS.member` negative -> Just False
    | otherwise -> Nothing
  BotF {} -> Just False
  TopF {} -> Just True
  NotF _ a -> not <$> a
  ImplF _ l r -> orM (not <$> l) r
  Just True ::\/ _ -> Just True
  _ ::\/ Just True -> Just True
  l ::\/ r -> orM l r
  Just False ::/\ _ -> Just False
  Just True ::/\ r -> r
  _ ::/\ Just False -> Just False
  l ::/\ Just True -> l
  l ::/\ r -> (&&) <$> l <*> r

orM :: Maybe Bool -> Maybe Bool -> Maybe Bool
orM (Just True) _ = Just True
orM (Just False) r = r
orM _ (Just True) = Just True
orM l (Just False) = l
orM Nothing Nothing = Nothing
