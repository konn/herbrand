{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -funbox-strict-fields #-}

module Types (
  Prioritised (..),
  Priorities (..),
  Winner (..),
  BenchCase (..),
  winnerCountL,
  getMinArg,
  getMinObj,
) where

import Control.DeepSeq
import qualified Control.Foldl as L
import qualified Data.Bifunctor as Bi
import qualified Data.ByteString as BS
import Data.Coerce (coerce)
import qualified Data.Csv as Csv
import Data.Generics.Labels ()
import qualified Data.Map.Strict as Map
import Data.Maybe
import Data.Ord (Down (..), comparing)
import Data.Proxy (Proxy (..))
import Data.Reflection
import Data.Semigroup (Arg (..), ArgMin, Min (..))
import qualified Data.Text as T
import qualified Data.Vector as V
import GHC.Generics (Generic)
import GHC.Generics.Generically

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
