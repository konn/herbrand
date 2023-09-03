{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -funbox-strict-fields #-}

module Report (buildReport) where

import qualified Control.Foldl as L
import Control.Lens hiding ((<.>))
import Data.Generics.Labels ()
import Data.List (sortOn)
import qualified Data.Map.Strict as Map
import Data.Ord (Down (..))
import qualified Data.Text as T
import GitHash
import qualified Lucid
import qualified Lucid.Html5 as H5
import Types

buildReport :: Maybe T.Text -> Maybe GitInfo -> Map.Map [T.Text] (FilePath, Winner Integer) -> Lucid.Html ()
buildReport mReportName mGit benchs = Lucid.doctypehtml_ do
  let resultName =
        case mReportName of
          Nothing -> "Benchmark Result"
          Just txt -> "Benchmark Result for " <> txt
      (timeRank, allocRank, peakRank) =
        L.fold
          ( L.premap snd
              $ (,,)
              <$> L.premap timeWinner winnerCountL
              <*> L.premap allocWinner winnerCountL
              <*> L.premap peakWinner winnerCountL
          )
          benchs
  H5.head_ do
    H5.title_ $ Lucid.toHtml resultName
    H5.meta_ [H5.charset_ "UTF-8"]
    H5.meta_
      [ H5.name_ "viewport"
      , H5.content_ "width=device-width, initial-scale=1.0"
      ]
    H5.link_ [H5.rel_ "stylesheet", H5.href_ "https://cdn.simplecss.org/simple.min.css"]
  H5.body_ do
    H5.h1_ $ Lucid.toHtml resultName
    H5.section_ do
      H5.h2_ "Metadata"
      case mGit of
        Nothing -> H5.p_ "N/A"
        Just ginfo -> H5.table_ $ H5.tbody_ do
          H5.tr_ do
            H5.th_ "Branch"
            H5.td_ $ H5.code_ $ Lucid.toHtml $ giBranch ginfo
          H5.tr_ do
            H5.th_ "Commit"
            H5.td_ $ H5.code_ $ Lucid.toHtml $ giHash ginfo
          H5.tr_ do
            H5.th_ "Description"
            H5.td_ $ H5.code_ $ Lucid.toHtml $ giDescribe ginfo
          H5.tr_ do
            H5.th_ "Commit Message"
            H5.td_ $ H5.code_ $ Lucid.toHtml $ giCommitMessage ginfo
    H5.h2_ "Summary: Overall Winning Ranking"
    let renderRanking :: Lucid.Html () -> Map.Map T.Text Int -> Lucid.Html ()
        renderRanking name rank = do
          H5.h3_ name
          H5.table_ do
            H5.thead_ $ H5.tr_ $ do
              H5.th_ "Rank"
              H5.th_ "Name"
              H5.th_ "Score"
            H5.tbody_ $ iforM_ (take 3 $ sortOn (Down . snd) $ Map.toList rank) \i (algo, score) ->
              H5.tr_ do
                H5.td_ $ "#" <> Lucid.toHtml (show $ i + 1)
                H5.td_ $ Lucid.toHtml algo
                H5.td_ $ Lucid.toHtml $ show score <> " / " <> show (Map.size benchs)
    renderRanking "Time" timeRank
    renderRanking "Alloc" allocRank
    renderRanking "Peak" peakRank

    H5.h2_ "Results"
    iforM_ benchs \k (v, win) -> H5.section_ do
      H5.h3_ $ H5.code_ $ Lucid.toHtml $ T.intercalate "-" k
      H5.table_ do
        let renderWinner lab crit = H5.tr_ do
              H5.th_ lab
              H5.td_ $ H5.code_ $ Lucid.toHtml $ getMinArg $ crit win
              H5.td_ $ H5.code_ $ Lucid.toHtml $ show $ getMinObj $ crit win
        H5.thead_ $ H5.tr_ $ H5.th_ "Criterion" <> H5.th_ "Winner" <> H5.th_ "Score"
        H5.tbody_ do
          renderWinner "Time" timeWinner
          renderWinner "Alloc" allocWinner
          renderWinner "Peak" peakWinner
      H5.p_
        $ H5.figure_
        $ H5.a_ [H5.href_ (T.pack v)]
        $ H5.img_ [H5.src_ (T.pack v), H5.alt_ "Bar chart"]
