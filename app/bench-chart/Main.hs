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
import qualified Data.Bifunctor as Bi
import qualified Data.ByteString.Lazy as LBS
import Data.Coerce (coerce)
import qualified Data.Csv as Csv
import Data.Foldable (foldMap')
import Data.Generics.Labels ()
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust, fromMaybe)
import Data.Semigroup (Arg (..), First (..), Min (..))
import qualified Data.Text as T
import qualified Data.Trie.Map as Trie
import qualified Data.Trie.Map.Internal as Trie
import qualified Data.Vector as V
import GHC.Generics (Generic)
import GitHash
import qualified Lucid
import qualified Options.Applicative as Opt
import Plot
import Report
import System.Directory
import System.FilePath
import System.IO
import Types
import UnliftIO (pooledForConcurrently)

data Opts = Opts
  { input :: !FilePath
  , output :: !FilePath
  , stripSuffices :: !(Maybe Int)
  , reportName :: !(Maybe T.Text)
  , gitInspect :: !Bool
  }
  deriving (Show, Eq, Ord, Generic)

main :: IO ()
main = do
  Opts {..} <- Opt.execParser optsP
  hSetBuffering stderr LineBuffering
  (_, !rows) <-
    either error (evaluate . force) . Csv.decodeByName @BenchCase =<< LBS.readFile input
  !trie <-
    evaluate
      $ force
      $ coerce
      $ Map.filter (not . Map.null)
      $ Map.mapKeysMonotonic
        ( \(V.fromList -> xs) ->
            V.toList $ V.take (max 0 (V.length xs - fromMaybe 0 stripSuffices)) xs
        )
      $ flatKeys
      $ stripCommonPrefices
      $ foldMap' (Trie.singleton <$> T.splitOn "." . fullName <*> First) rows
  let colorMap = buildColorMap trie
  createDirectoryIfMissing True output
  svgs <- pooledForConcurrently (Map.mapWithKey (,) trie) \(k, bg) -> do
    !plots <- evaluate $ mkPlots colorMap k bg
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
    svgs <- iforM plots \plotType chart -> do
      let typeStr = case plotType of
            TimePlot -> "time"
            AllocPlot -> "alloc"
            CopiedPlot -> "copied"
          baseName = T.unpack (T.intercalate "-" k) </> typeStr <.> "svg"
          outPath = output </> baseName
      createDirectoryIfMissing True $ takeDirectory outPath
      writeChartOptions outPath chart
      hPutStrLn stderr $ "Written: " <> outPath
      pure baseName
    pure (svgs, mWinner)

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

buildColorMap :: (Foldable t) => t (Map.Map T.Text a) -> Map.Map T.Text Colour
buildColorMap =
  Map.fromList
    . flip zip (cycle paletteR)
    . L.fold
      ( L.premap Map.keysSet
          $ L.handles folded L.list
      )

stripCommonPrefices :: Trie.TMap T.Text a -> Trie.TMap T.Text a
stripCommonPrefices = go
  where
    go tr@(Trie.TMap (Trie.Node Nothing dic)) =
      if Map.size dic == 1 then go $ snd $ Map.findMin dic else tr
    go tr@(Trie.TMap (Trie.Node Just {} _)) = tr

flatKeys :: (Semigroup a) => Trie.TMap T.Text a -> Map.Map [T.Text] (Map.Map T.Text a)
flatKeys = go . Trie.getNode
  where
    go tr@(Trie.Node _ chs)
      | any ((== 1) . Trie.count) chs =
          Map.singleton [] $ Map.fromListWith (<>) $ map (Bi.first $ T.intercalate ".") $ Trie.toList $ Trie.TMap tr
      | otherwise =
          ifoldMapBy
            (Map.unionWith (<>))
            Map.empty
            (Map.mapKeysMonotonic . (:))
            (go . Trie.getNode <$> chs)

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
      stripSuffices <-
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
      pure Opts {..}

-- Stolen from Chart-svg, but load font from local
