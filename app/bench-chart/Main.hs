{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE DisambiguateRecordFields #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -funbox-strict-fields #-}

module Main (main) where

import Chart hiding (abs, (<.>))
import Control.Applicative (optional, (<**>))
import Control.DeepSeq
import Control.Exception
import qualified Control.Foldl as L
import Control.Lens hiding ((<.>))
import Data.Generics.Labels ()
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust, fromMaybe)
import Data.Semigroup (Arg (..), Min (..))
import qualified Data.Text as T
import qualified Data.Vector as V
import GHC.Generics (Generic)
import GitHash
import qualified Lucid
import Options.Applicative ((<|>))
import qualified Options.Applicative as Opt
import Pages
import Parse (Benchs, decodeBenchs)
import Plot
import Report
import System.Directory
import System.FilePath
import System.IO
import Types
import UnliftIO (evaluateDeep, pooledForConcurrently)

data Opts = Opts
  { input :: !FilePath
  , output :: !FilePath
  , sufficesToStrip :: !(Maybe Int)
  , reportName :: !(Maybe T.Text)
  , gitInspect :: !Bool
  , baseline :: !(Maybe FilePath)
  , baselineDescr :: !(Maybe T.Text)
  }
  deriving (Show, Eq, Ord, Generic)

main :: IO ()
main = do
  hSetBuffering stderr LineBuffering
  cmd <- Opt.execParser optsP
  case cmd of
    SingleReport opts -> generateSingleReport opts
    UpdateReportPages opts -> updateReportPages opts

generateSingleReport :: Opts -> IO ()
generateSingleReport Opts {..} = do
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
  Lucid.renderToFile reportHtml $ buildReport reportName mGit (baseDesc <$ baseline) svgs
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

data Cmd
  = SingleReport !Opts
  | UpdateReportPages !PagesOpts
  deriving (Show, Eq, Ord, Generic)

optsP :: Opt.ParserInfo Cmd
optsP = Opt.info (p <**> Opt.helper <|> genRep) $ Opt.progDesc "Converts tasty-bench output to  bar charts, scaling per-group not global."
  where
    genRep =
      Opt.hsubparser
        $ Opt.command "update-report-pages"
        $ Opt.info updateP
        $ Opt.progDesc "Updates GitHub Pages reports"
    p =
      SingleReport <$> do
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
        pure Opts {..}
    updateP =
      UpdateReportPages <$> do
        configPath <-
          Opt.strOption
            $ Opt.long "config"
            <> Opt.short 'c'
            <> Opt.metavar "PATH"
            <> Opt.help "The path to the reports.json"
        input <-
          Opt.strOption
            $ Opt.long "input"
            <> Opt.short 'i'
            <> Opt.metavar "DIR"
            <> Opt.help "The directory containing input report directories"
        output <-
          Opt.strOption
            $ Opt.long "output"
            <> Opt.short 'o'
            <> Opt.metavar "DIR"
            <> Opt.help "The deploy path"
        repo <-
          Opt.strOption
            $ Opt.long "repo"
            <> Opt.short 'R'
            <> Opt.metavar "OWNER/REPO"
            <> Opt.help "Repository full name"
        pull <- Opt.optional do
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
        pure PagesOpts {..}
