{-# LANGUAGE GHC2021 #-}
{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -funbox-strict-fields #-}

module Types (
  Criteria (..),
  Criterion (..),
  Prioritised (..),
  Priorities (..),
  Winner (..),
  BenchCase (..),
  BranchName (..),
  CommitHash (..),
  PullRequest (..),
  pullReqOptsP,
  winnerCountL,
  getMinArg,
  getMinObj,
) where

import Control.DeepSeq
import Control.Foldl qualified as L
import Control.Lens
import Data.Aeson
import Data.Bifunctor qualified as Bi
import Data.ByteString qualified as BS
import Data.Coerce (coerce)
import Data.Csv qualified as Csv
import Data.Generics.Labels ()
import Data.Hashable (Hashable)
import Data.Map.Strict qualified as Map
import Data.Maybe
import Data.Ord (Down (..), comparing)
import Data.Proxy (Proxy (..))
import Data.Reflection
import Data.Semigroup (Arg (..), ArgMin, Min (..))
import Data.String
import Data.Text qualified as T
import Data.Vector qualified as V
import GHC.Generics (Generic, Generic1)
import GHC.Generics.Generically
import Lucid (ToHtml)
import Options.Applicative qualified as Opt

newtype Prioritised s a = Prioritised {unprioritise :: a}
  deriving (Eq, Show)

data Priorities a = NoPrio | Prioritise (V.Vector a)
  deriving (Show, Eq, Ord, Generic)

instance (Reifies s (Priorities a), Ord a) => Ord (Prioritised s a) where
  compare = case reflect @s Proxy of
    NoPrio -> coerce $ compare @a
    Prioritise vec -> comparing $ prioritise vec . unprioritise

prioritise :: (Eq a) => V.Vector a -> a -> (Down (Maybe (Down Int)), a)
prioritise vec = (,) <$> coerce . (`V.elemIndex` vec) <*> id

data Winner a = Winner
  { timeWinner :: {-# UNPACK #-} !(ArgMin a T.Text)
  , allocWinner :: {-# UNPACK #-} !(ArgMin a T.Text)
  , copiedWinner :: {-# UNPACK #-} !(ArgMin a T.Text)
  }
  deriving (Show, Eq, Ord, Generic)
  deriving anyclass (NFData)
  deriving (Semigroup) via Generically (Winner a)

instance Functor Winner where
  fmap f (Winner x y z) = Winner (fmap (Bi.first f) x) (fmap (Bi.first f) y) (fmap (Bi.first f) z)

instance Foldable Winner where
  foldMap f (Winner (Min (Arg x _)) (Min (Arg y _)) (Min (Arg z _))) =
    f x <> f y <> f z

data BenchCase = BenchCase
  { fullName :: !T.Text
  , mean :: !Integer
  , stddev2 :: !Integer
  , alloc, copied, peakMem :: !(Maybe Integer)
  }
  deriving (Show, Eq, Ord, Generic)
  deriving anyclass (NFData)

instance Csv.DefaultOrdered BenchCase where
  headerOrder =
    const
      $ V.fromList
        [ nameF
        , meanF
        , stddev2F
        , allocF
        , copiedF
        , peakF
        ]

nameF, meanF, stddev2F, allocF, peakF, copiedF :: BS.ByteString
nameF = "Name"
meanF = "Mean (ps)"
stddev2F = "2*Stdev (ps)"
allocF = "Allocated"
copiedF = "Copied"
peakF = "Peak Memory"

instance Csv.ToNamedRecord BenchCase where
  toNamedRecord BenchCase {..} =
    Csv.namedRecord
      $ [ (nameF, Csv.toField fullName)
        , (meanF, Csv.toField mean)
        , (stddev2F, Csv.toField stddev2)
        ]
      ++ mapMaybe
        sequenceA
        [ (allocF, Csv.toField <$> alloc)
        , (copiedF, Csv.toField <$> copied)
        , (peakF, Csv.toField <$> peakMem)
        ]

instance Csv.FromNamedRecord BenchCase where
  parseNamedRecord recd = do
    fullName <- recd Csv..: nameF
    mean <- recd Csv..: meanF
    stddev2 <- recd Csv..: stddev2F
    alloc <- recd Csv..: allocF
    copied <- recd Csv..: copiedF
    peakMem <- recd Csv..: peakF
    pure BenchCase {..}

winnerCountL :: L.Fold (ArgMin x T.Text) (Map.Map T.Text Int)
winnerCountL = L.premap ((,1 :: Int) . getMinArg) $ L.foldByKeyMap L.sum

getMinArg :: ArgMin w a -> a
getMinArg (Min (Arg _ a)) = a

getMinObj :: ArgMin w a -> w
getMinObj (Min (Arg w _)) = w

data Criterion = Time | Alloc | Copied
  deriving (Show, Eq, Ord, Generic, Enum, Bounded)
  deriving anyclass (NFData, Hashable)

instance FunctorWithIndex Criterion Criteria

instance FoldableWithIndex Criterion Criteria

instance TraversableWithIndex Criterion Criteria where
  itraverse f p = do
    timePlot <- f Time $ timePlot p
    allocPlot <- traverse (f Alloc) $ allocPlot p
    copiedPlot <- traverse (f Copied) $ copiedPlot p
    pure Criteria {..}

data Criteria a = Criteria
  { timePlot :: !a
  , allocPlot :: !(Maybe a)
  , copiedPlot :: !(Maybe a)
  }
  deriving (Show, Eq, Ord, Generic, Generic1, Functor, Foldable, Traversable)
  deriving anyclass (NFData)

newtype BranchName = BranchName {runBranchName :: T.Text}
  deriving (Show, Eq, Ord, Generic)
  deriving newtype (FromJSON, ToJSON, Hashable, IsString, FromJSONKey, ToJSONKey, NFData, ToHtml)

newtype CommitHash = CommitHash {runCommitHash :: T.Text}
  deriving (Show, Eq, Ord, Generic)
  deriving newtype (FromJSON, ToJSON, Hashable, IsString, FromJSONKey, ToJSONKey, NFData, ToHtml)

data PullRequest = PullRequest
  { pullNumber :: Word
  , pullTitle :: T.Text
  , baseBranch :: BranchName
  , baseCommit :: CommitHash
  }
  deriving (Show, Eq, Ord, Generic)
  deriving anyclass (FromJSON, ToJSON, NFData)

pullReqOptsP :: Opt.Parser PullRequest
pullReqOptsP = do
  pullNumber <-
    Opt.option Opt.auto
      $ Opt.long "pull-number"
      <> Opt.metavar "NUM"
      <> Opt.help "Pull Request Number"
  pullTitle <-
    Opt.strOption
      $ Opt.long "pull-title"
      <> Opt.metavar "TITLE"
      <> Opt.help "Pull Request Title"
  baseBranch <-
    Opt.strOption
      $ Opt.long "pull-base-branch"
      <> Opt.metavar "REF_NAME"
      <> Opt.help "Pull Request base branch"
  baseCommit <-
    Opt.strOption
      $ Opt.long "pull-base-commit"
      <> Opt.metavar "SHA"
      <> Opt.help "Pull Request base commit"
  pure PullRequest {..}
