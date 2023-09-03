{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
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
import qualified Options.Applicative as Opt
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
  }
  deriving (Show, Eq, Ord, Generic)

main :: IO ()
main = do
  Opts {..} <- Opt.execParser optsP
  hSetBuffering stderr LineBuffering
  !trie <-
    evaluateDeep
      . pruneSuffices sufficesToStrip
      =<< decodeBenchs input
  !mbases <-
    evaluateDeep
      . fmap (pruneSuffices sufficesToStrip)
      =<< mapM decodeBenchs baseline
  let colorMap = buildColorMap trie
  createDirectoryIfMissing True output
  svgs <- pooledForConcurrently (Map.mapWithKey (,) trie) \(k, bg) -> do
    let mbase = Map.lookup k =<< mbases
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
  let reportHtml = output </> "report.html"
  print
    $ L.fold
      ( L.premap snd
          $ (,,)
          <$> L.premap timeWinner winnerCountL
          <*> L.premap allocWinner winnerCountL
          <*> L.premap copiedWinner winnerCountL
      )
      svgs
  Lucid.renderToFile reportHtml $ buildReport reportName mGit svgs
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

optsP :: Opt.ParserInfo Opts
optsP = Opt.info (p <**> Opt.helper) $ Opt.progDesc "Converts tasty-bench output to  bar charts, scaling per-group not global."
  where
    p = do
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
      pure Opts {..}
