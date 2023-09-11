{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -funbox-strict-fields #-}

module Report (
  SingleReportOpts (..),
  singleReportOptsP,
  generateSingleReport,
) where

import Chart hiding (abs, (<.>))
import Control.Applicative (optional)
import Control.DeepSeq
import Control.Exception
import qualified Control.Foldl as L
import Control.Lens hiding ((<.>))
import Control.Monad (forM_)
import qualified Data.DList.DNonEmpty as DLNE
import Data.Generics.Labels ()
import Data.List (sortOn)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust, fromMaybe)
import Data.Ord (Down (..))
import Data.Semigroup (Arg (..), Min (..))
import qualified Data.Text as T
import qualified Data.Vector as V
import GHC.Generics (Generic)
import GitHash
import Lucid
import qualified Options.Applicative as Opt
import Parse (Benchs, decodeBenchs)
import Plot
import System.Directory
import System.FilePath
import System.IO
import Types
import UnliftIO (evaluateDeep, pooledForConcurrently)

type BaselineDescr = T.Text

data SingleReportOpts = SingleReportOpts
  { input :: !FilePath
  , output :: !FilePath
  , repo :: !T.Text
  , sufficesToStrip :: !(Maybe Int)
  , reportName :: !(Maybe T.Text)
  , gitInspect :: !Bool
  , baseline :: !(Maybe FilePath)
  , baselineDescr :: !(Maybe T.Text)
  , pull :: !(Maybe PullRequest)
  }
  deriving (Show, Eq, Ord, Generic)

singleReportOptsP :: Opt.Parser SingleReportOpts
singleReportOptsP = do
  repo <-
    Opt.strOption
      $ Opt.long "repo"
      <> Opt.metavar "OWNER/REPO"
      <> Opt.help "Repository full name"
  input <-
    Opt.strOption
      $ Opt.long "input"
      <> Opt.short 'i'
      <> Opt.metavar "FILE"
      <> Opt.help "Input CSV file"
  output <-
    Opt.strOption
      $ Opt.long "output"
      <> Opt.short 'o'
      <> Opt.metavar "DIR"
      <> Opt.help "Output directory"
  sufficesToStrip <-
    optional
      $ Opt.option Opt.auto
      $ Opt.long "strip-suffices"
      <> Opt.short 's'
      <> Opt.metavar "NUM"
      <> Opt.help "Number of prefix to drop."
  reportName <-
    optional
      $ Opt.strOption
      $ Opt.long "report-name"
      <> Opt.short 'R'
      <> Opt.metavar "TITLE"
      <> Opt.help "Optional Report Name"
  gitInspect <- Opt.switch $ Opt.long "git" <> Opt.help "Inspects git metadata and includes in the report"
  baseline <-
    Opt.optional
      $ Opt.strOption
      $ Opt.long "baseline"
      <> Opt.short 'B'
      <> Opt.metavar "FILE"
      <> Opt.help "Optional path to the baseline CSV to compare with"
  baselineDescr <-
    Opt.optional
      $ Opt.strOption
      $ Opt.long "baseline-desc"
      <> Opt.metavar "FILE"
      <> Opt.help "Description for the baseline"
  pull <- Opt.optional pullReqOptsP
  pure SingleReportOpts {..}

generateSingleReport :: SingleReportOpts -> IO ()
generateSingleReport SingleReportOpts {..} = do
  !trie <-
    evaluateDeep . pruneSuffices sufficesToStrip =<< decodeBenchs input
  !mbases <-
    evaluateDeep
      . fmap (pruneSuffices sufficesToStrip)
      =<< mapM decodeBenchs baseline
  let colorMap = buildColorMap trie
  createDirectoryIfMissing True output
  let baseDesc = fromMaybe "Baseline" baselineDescr
  svgs <- pooledForConcurrently (Map.mapWithKey (,) trie) \(k, bg) -> do
    let mbase = (baseDesc,) <$> (Map.lookup k =<< mbases)
    !plots <- evaluate $ mkPlots colorMap k mbase bg
    !mWinner <-
      evaluate
        $ force
        $ fromJust
        $ ifoldMap
          ( \i BenchCase {..} ->
              Just
                Winner
                  { timeWinner = Min $ Arg mean i
                  , allocWinner = Min $ Arg (fromMaybe 0 alloc) i
                  , copiedWinner = Min $ Arg (fromMaybe 0 copied) i
                  }
          )
          bg
    paths <- iforM plots \crit chart -> do
      let typeStr = case crit of
            Time -> "time"
            Alloc -> "alloc"
            Copied -> "copied"
          baseName = T.unpack (T.intercalate "-" k) </> typeStr <.> "svg"
          outPath = output </> baseName
      createDirectoryIfMissing True $ takeDirectory outPath
      writeChartOptions outPath chart
      hPutStrLn stderr $ "Written: " <> outPath
      pure baseName
    pure (paths, mWinner)

  mGit <-
    if gitInspect
      then
        either throwIO (pure . Just)
          =<< either throwIO getGitInfo
          =<< getGitRoot
          =<< getCurrentDirectory
      else pure Nothing
  let reportHtml = output </> "index.html"
  print
    $ L.fold
      ( L.premap snd
          $ (,,)
          <$> L.premap timeWinner winnerCountL
          <*> L.premap allocWinner winnerCountL
          <*> L.premap copiedWinner winnerCountL
      )
      svgs
  Lucid.renderToFile reportHtml
    $ buildReport repo reportName mGit (baseDesc <$ baseline) pull svgs
  hPutStrLn stderr $ "Report Written to: " <> reportHtml

pruneSuffices :: Maybe Int -> Benchs -> Benchs
pruneSuffices = maybe id \c ->
  Map.mapKeysMonotonic
    ( \(V.fromList -> xs) ->
        V.toList $ V.take (max 0 (V.length xs - c)) xs
    )

buildColorMap :: (Foldable t) => t (Map.Map T.Text a) -> Map.Map T.Text Colour
buildColorMap =
  Map.fromList
    . flip zip (cycle paletteR)
    . L.fold
      ( L.premap Map.keysSet
          $ L.handles folded L.list
      )

buildReport ::
  T.Text ->
  Maybe T.Text ->
  Maybe GitInfo ->
  Maybe BaselineDescr ->
  Maybe PullRequest ->
  Map.Map [T.Text] (Criteria FilePath, Winner Integer) ->
  Html ()
buildReport repo mReportName mGit mbase pull benchs = doctypehtml_ do
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
                        [
                          ( "Branch"
                          , a_ [href_ $ "https://github.com/" <> repo <> "/tree/" <> T.pack (giBranch ginfo)]
                              $ toHtml
                              $ giBranch ginfo
                          )
                        ,
                          ( "Commit"
                          , a_ [href_ $ "https://github.com/" <> repo <> "/tree/" <> T.pack (giHash ginfo)]
                              $ toHtml
                              $ giHash ginfo
                          )
                        , ("Commit Message", toHtml $ giCommitMessage ginfo)
                        ]
                )
                mGit
              <> foldMap (\base -> Just $ DLNE.singleton ("Baseline", toHtml base)) mbase
              <> foldMap
                ( \PullRequest {..} ->
                    Just
                      $ DLNE.singleton
                        ( "Pull Request"
                        , a_ [href_ $ "https://github.com/" <> repo <> "/pull/" <> T.pack (show pullNumber)]
                            $ "#"
                            <> toHtml (show pullNumber)
                            <> ": "
                            <> toHtml pullTitle
                        )
                )
                pull
      case metas of
        Nothing -> p_ "N/A"
        Just m -> table_ $ tbody_ $ forM_ m $ \(lab, col) ->
          tr_ do
            th_ lab
            td_ $ code_ col
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
