{-# LANGUAGE GHC2021 #-}
{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -funbox-strict-fields #-}

module Plot (mkPlots, Plots (..), PlotType (..)) where

import Chart hiding (abs, (<.>))
import Control.Applicative (Applicative (..))
import Control.Arrow ((&&&))
import Control.DeepSeq (NFData)
import Control.Lens hiding ((<.>))
import Data.DList qualified as DL
import Data.Generics.Labels ()
import Data.Hashable (Hashable)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromMaybe)
import Data.Text qualified as T
import GHC.Generics (Generic, Generic1)
import Types
import Units

data PlotType = TimePlot | AllocPlot | CopiedPlot
  deriving (Show, Eq, Ord, Generic, Enum, Bounded)
  deriving anyclass (NFData, Hashable)

instance FunctorWithIndex PlotType Plots

instance FoldableWithIndex PlotType Plots

instance TraversableWithIndex PlotType Plots where
  itraverse f p = do
    timePlot <- f TimePlot $ timePlot p
    allocPlot <- traverse (f AllocPlot) $ allocPlot p
    copiedPlot <- traverse (f CopiedPlot) $ copiedPlot p
    pure Plots {..}

data Plots a = Plots
  { timePlot :: !a
  , allocPlot :: !(Maybe a)
  , copiedPlot :: !(Maybe a)
  }
  deriving (Show, Eq, Ord, Generic, Generic1, Functor, Foldable, Traversable)
  deriving anyclass (NFData)

mkPlots ::
  Map.Map T.Text Colour ->
  [T.Text] ->
  Map.Map T.Text BenchCase ->
  Plots ChartOptions
mkPlots colMap k bg =
  let caseName = T.intercalate "/" k
      Identity timePlot =
        makeBarChart
          ChartDef
            { chartTitle = "Time"
            , chartUnit = "s"
            , defaultSIPrefix = Pico
            , valueL = #mean . to Identity
            , errorL = Just #stddev2
            }
          caseName
          colMap
          bg
      allocPlot =
        makeBarChart
          ChartDef
            { chartTitle = "Alloc"
            , chartUnit = "B"
            , defaultSIPrefix = Unit
            , valueL = #alloc
            , errorL = Nothing
            }
          caseName
          colMap
          bg
      copiedPlot =
        makeBarChart
          ChartDef
            { chartTitle = "Copied"
            , chartUnit = "B"
            , defaultSIPrefix = Unit
            , valueL = #copied
            , errorL = Nothing
            }
          caseName
          colMap
          bg
   in Plots {..}

data ChartDef t = ChartDef
  { chartTitle :: !T.Text
  , defaultSIPrefix :: !SIPrefix
  , chartUnit :: !T.Text
  , valueL :: Getter BenchCase (t Integer)
  , errorL :: Maybe (Getter BenchCase Integer)
  }

makeBarChart ::
  (Applicative t) =>
  ChartDef t ->
  T.Text ->
  Map.Map T.Text Colour ->
  Map.Map T.Text BenchCase ->
  t ChartOptions
makeBarChart ChartDef {..} caseName colMap bg0 =
  traverse (liftA2 (,) <$> pure <*> view valueL) bg0 <&> \bg ->
    let
      mkBarRow !b !val =
        let mean' = adjustSITo defaultSIPrefix val targetSI
            dev' =
              fmap
                ( \l ->
                    DL.singleton
                      $ adjustSITo defaultSIPrefix (b ^. l `quot` 2) targetSI
                )
                errorL
         in (DL.singleton mean', dev')
      (fromMaybe Unit -> !targetSI, (values, devs)) =
        foldMap
          (detectSIPrefix defaultSIPrefix . snd &&& uncurry mkBarRow)
          bg
      theBars =
        BarData
          { barData = map pure $ DL.toList values
          , barRowLabels = []
          , barColumnLabels = Map.keys bg
          }
      xAxis =
        defaultAxisOptions
          & #ticks . #ltick .~ Nothing
          & #ticks . #style .~ TickLabels (Map.keys bg)
      yAxis = defaultAxisOptions & #place .~ PlaceLeft
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
      theBar = barChart barOpts theBars
      barXYes =
        theBars
          ^.. #barData
            . to (barRects barOpts)
            . folded
            . folded
            . to \(Rect x0 x1 _ y1) ->
              (Point ((x0 + x1) / 2) y1, x1 - x0)
      errs =
        foldMap
          ( zipWith
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
              . DL.toList
          )
          devs
      yAxisLabel =
        defaultTitle (chartTitle <> " [" <> T.pack (showPrefix targetSI) <> chartUnit <> "]")
          & #place .~ PlaceLeft
          & #anchor .~ AnchorMiddle
          & #style . #size %~ (/ 2)
      title = chartTitle <> ": " <> caseName
     in
      theBar
        & #hudOptions . #chartAspect .~ FixedAspect ((1 + sqrt 5) / 2)
        & #hudOptions . #axes .~ [(5, xAxis), (5, yAxis)]
        & #hudOptions . #titles
          .~ [ (6, defaultTitle title)
             , (11, yAxisLabel)
             ]
        & #hudOptions . #frames .~ [(11, defaultFrameOptions & #buffer .~ 0.2)]
        & #charts <>~ named "errors" errs
