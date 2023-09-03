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
import Control.Monad (forM_)
import qualified Data.DList.DNonEmpty as DLNE
import Data.Generics.Labels ()
import Data.List (sortOn)
import qualified Data.Map.Strict as Map
import Data.Ord (Down (..))
import qualified Data.Text as T
import GitHash
import Lucid
import Plot
import Types

type BaselineDescr = T.Text

buildReport :: Maybe T.Text -> Maybe GitInfo -> Maybe BaselineDescr -> Map.Map [T.Text] (Criteria FilePath, Winner Integer) -> Html ()
buildReport mReportName mGit mbase benchs = doctypehtml_ do
  let resultName =
        case mReportName of
          Nothing -> "Benchmark Result"
          Just txt -> "Benchmark Result for " <> txt
      (timeRank, allocRank, copiedRank) =
        L.fold
          ( L.premap snd
              $ (,,)
              <$> L.premap timeWinner winnerCountL
              <*> L.premap allocWinner winnerCountL
              <*> L.premap copiedWinner winnerCountL
          )
          benchs
  head_ do
    title_ $ toHtml resultName
    meta_ [charset_ "UTF-8"]
    meta_
      [ name_ "viewport"
      , content_ "width=device-width, initial-scale=1.0"
      ]
    link_ [rel_ "stylesheet", href_ "https://cdn.simplecss.org/simple.min.css"]
  body_ do
    h1_ $ toHtml resultName
    section_ do
      h2_ "Metadata"
      let metas =
            DLNE.toNonEmpty
              <$> foldMap
                ( \ginfo ->
                    Just
                      $ DLNE.fromList
                        [ ("Branch", T.pack $ giBranch ginfo)
                        , ("Commit", T.pack $ giHash ginfo)
                        , ("Commit Message", T.pack $ giCommitMessage ginfo)
                        ]
                )
                mGit
              <> foldMap (\base -> Just $ DLNE.singleton ("Baseline", base)) mbase
      case metas of
        Nothing -> p_ "N/A"
        Just m -> table_ $ tbody_ $ forM_ m $ \(lab, col) ->
          tr_ do
            th_ lab
            td_ $ code_ $ toHtml col
    h2_ "Summary: Overall Winning Ranking"
    let renderRanking :: Html () -> Map.Map T.Text Int -> Html ()
        renderRanking name rank = do
          h3_ name
          table_ do
            thead_ $ tr_ $ do
              th_ "Rank"
              th_ "Name"
              th_ "Score"
            tbody_ $ iforM_ (take 3 $ sortOn (Down . snd) $ Map.toList rank) \i (algo, score) ->
              tr_ do
                td_ $ "#" <> toHtml (show $ i + 1)
                td_ $ toHtml algo
                td_ $ toHtml $ show score <> " / " <> show (Map.size benchs)
    renderRanking "Time" timeRank
    renderRanking "Alloc" allocRank
    renderRanking "Copied" copiedRank

    h2_ "Results"
    iforM_ benchs \k (plots, win) -> section_ do
      h3_ $ code_ $ toHtml $ T.intercalate "-" k
      table_ do
        let renderWinner lab crit = tr_ do
              th_ lab
              td_ $ code_ $ toHtml $ getMinArg $ crit win
              td_ $ code_ $ toHtml $ show $ getMinObj $ crit win
        thead_ $ tr_ $ th_ "Criterion" <> th_ "Winner" <> th_ "Score"
        tbody_ do
          renderWinner "Time" timeWinner
          renderWinner "Alloc" allocWinner
          renderWinner "Copied" copiedWinner
      iforM_ plots \tag v -> do
        let chartTitle = T.pack $ show tag
        h4_ $ toHtml chartTitle
        p_
          $ figure_
          $ a_ [href_ (T.pack v)]
          $ img_ [width_ "100%", src_ (T.pack v), alt_ "Bar chart"]
