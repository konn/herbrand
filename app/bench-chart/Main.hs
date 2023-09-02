{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ParallelListComp #-}
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
import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as LBS
import Data.Coerce (coerce)
import Data.Csv (ToNamedRecord (toNamedRecord))
import qualified Data.Csv as Csv
import qualified Data.DList as DL
import Data.Foldable (foldMap')
import Data.Generics.Labels ()
import Data.List (sortOn)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust, fromMaybe, mapMaybe)
import Data.Ord (Down (..), comparing)
import Data.Proxy (Proxy (..))
import Data.Reflection
import Data.Semigroup (Arg (..), ArgMin, First (..), Max (..), Min (..))
import qualified Data.Text as T
import qualified Data.Trie.Map as Trie
import qualified Data.Trie.Map.Internal as Trie
import qualified Data.Vector as V
import GHC.Generics (Generic)
import GHC.Generics.Generically
import GitHash
import qualified Lucid
import qualified Lucid.Html5 as H5
import Math.NumberTheory.Logarithms (integerLog10')
import qualified Options.Applicative as Opt
import System.Directory
import System.FilePath
import System.IO
import UnliftIO (pooledForConcurrently)

data Opts = Opts
  { input :: !FilePath
  , output :: !FilePath
  , stripSuffices :: !(Maybe Int)
  , reportName :: !(Maybe T.Text)
  , gitInspect :: !Bool
  }
  deriving (Show, Eq, Ord, Generic)

data Winner a = Winner
  { timeWinner :: {-# UNPACK #-} !(ArgMin a T.Text)
  , allocWinner :: {-# UNPACK #-} !(ArgMin a T.Text)
  , peakWinner :: {-# UNPACK #-} !(ArgMin a T.Text)
  }
  deriving (Show, Eq, Ord, Generic)
  deriving anyclass (NFData)
  deriving (Semigroup) via Generically (Winner a)

instance Functor Winner where
  fmap f (Winner x y z) = Winner (fmap (Bi.first f) x) (fmap (Bi.first f) y) (fmap (Bi.first f) z)

instance Foldable Winner where
  foldMap f (Winner (Min (Arg x _)) (Min (Arg y _)) (Min (Arg z _))) =
    f x <> f y <> f z

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
    let baseName = T.unpack (T.intercalate "-" k) <.> "svg"
        outPath = output </> baseName
    createDirectoryIfMissing True $ takeDirectory outPath
    !plots <- evaluate $ mkPlot colorMap k bg
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
                  , peakWinner = Min $ Arg (fromMaybe 0 peakMem) i
                  }
          )
          bg
    writeChartOptions outPath plots
    hPutStrLn stderr $ "Written: " <> outPath
    pure (baseName, mWinner)

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
          <*> L.premap peakWinner winnerCountL
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

winnerCountL :: L.Fold (ArgMin x T.Text) (Map.Map T.Text Int)
winnerCountL = L.premap ((,1 :: Int) . getMinArg) $ L.foldByKeyMap L.sum

getMinArg :: ArgMin w a -> a
getMinArg (Min (Arg _ a)) = a

getMinObj :: ArgMin w a -> w
getMinObj (Min (Arg w _)) = w

mkPlot ::
  Map.Map T.Text Colour ->
  [T.Text] ->
  Map.Map T.Text BenchCase ->
  ChartOptions
mkPlot colMap k bg =
  let title = "Time (fill): " <> T.intercalate "/" k
      (timeSI, allocSI) =
        foldMap ((,) <$> detectSISuffix Pico . mean <*> detectSISuffix Unit . fromMaybe 0 . alloc) bg
          & both %~ fromMaybe Unit
      mkBarRow BenchCase {..} =
        let mean' = adjustSITo Pico mean timeSI
            alloc' = adjustSITo Unit (fromMaybe 0 alloc) allocSI
            dev' = adjustSITo Pico (stddev2 `quot` 2) timeSI
         in (DL.singleton mean', DL.singleton alloc', DL.singleton dev')
      (times, allocs, devs) = foldMap mkBarRow bg
      timeBars =
        BarData
          { barData = map pure $ DL.toList times
          , barRowLabels = []
          , barColumnLabels = Map.keys bg
          }
      barOpts =
        defaultBarOptions
          & #displayValues .~ False
          & #barRectStyles
            .~ map
              ( \nam ->
                  let col = fromMaybe (grey 0.5 0.4) $ Map.lookup nam colMap
                   in defaultRectStyle
                        & #color .~ col
                        & #borderSize .~ 0.0
              )
              (Map.keys bg)
      barXYes =
        timeBars
          ^.. #barData
            . to (barRects barOpts)
            . folded
            . folded
            . to \(Rect x0 x1 _ y1) ->
              (Point ((x0 + x1) / 2) y1, x1 - x0)
      timeLabel =
        defaultTitle ("Time [" <> T.pack (showPrefix timeSI) <> "s]")
          & #place .~ PlaceLeft
          & #anchor .~ AnchorMiddle
          & #style . #size %~ (/ 2)
      scat =
        zipWith
          ( \(Point x y, w) sigma ->
              let sty = defaultLineStyle & #size .~ 0.003
                  !y0 = y - sigma
                  !y1 = y + sigma
                  !dx = w / 10
               in LineChart
                    sty
                    [ [Point (x - dx) y0, Point (x + dx) y0]
                    , [Point x y0, Point x y1]
                    , [Point (x - dx) y1, Point (x + dx) y1]
                    ]
          )
          barXYes
          $ DL.toList devs
      theBar = barChart barOpts timeBars
      xAxis =
        defaultAxisOptions
          & #ticks . #ltick .~ Nothing
          & #ticks . #style .~ TickLabels (Map.keys bg)
      yAxis = defaultAxisOptions & #place .~ PlaceLeft
   in theBar
        & #hudOptions . #chartAspect .~ FixedAspect ((1 + sqrt 5) / 2)
        & #hudOptions . #axes .~ [(5, xAxis), (5, yAxis)]
        & #hudOptions . #titles
          .~ [ (6, defaultTitle title)
             , (11, timeLabel)
             ]
        & #hudOptions . #frames .~ [(11, defaultFrameOptions & #buffer .~ 0.075)]
        & #charts <>~ named "errors" scat

stripCommonPrefices :: Trie.TMap T.Text a -> Trie.TMap T.Text a
stripCommonPrefices = go
  where
    go tr@(Trie.TMap (Trie.Node Nothing dic)) =
      if Map.size dic == 1 then go $ snd $ Map.findMin dic else tr
    go tr@(Trie.TMap (Trie.Node Just {} _)) = tr

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

data SIPrefix = Pico | Nano | Micro | Mili | Unit | Kilo | Mega | Giga
  deriving (Show, Eq, Ord, Generic, Enum, Bounded)
  deriving (Semigroup) via Max SIPrefix

showPrefix :: SIPrefix -> String
showPrefix Pico = "p"
showPrefix Nano = "n"
showPrefix Micro = "u"
showPrefix Mili = "m"
showPrefix Unit = ""
showPrefix Kilo = "k"
showPrefix Mega = "M"
showPrefix Giga = "G"

adjustSITo :: SIPrefix -> Integer -> SIPrefix -> Double
adjustSITo _ 0 _ = 0.0
adjustSITo std i new =
  fromInteger i * 10 ^^ (3 * (fromEnum std - fromEnum new))

detectSISuffix :: SIPrefix -> Integer -> Maybe SIPrefix
detectSISuffix _ 0 = Nothing
detectSISuffix orig i =
  let ub = fromEnum (maxBound :: SIPrefix)
      lvl = integerLog10' (abs i) `quot` 3 + fromEnum orig
   in if lvl > ub
        then Just Giga
        else Just $ toEnum lvl

-- Stolen from Chart-svg, but load font from local
