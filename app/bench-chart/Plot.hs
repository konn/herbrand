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
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -funbox-strict-fields #-}

module Plot (mkPlot) where

import Chart hiding (abs, (<.>))
import Control.Lens hiding ((<.>))
import qualified Data.DList as DL
import Data.Generics.Labels ()
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)
import qualified Data.Text as T
import Types
import Units

mkPlot ::
  Map.Map T.Text Colour ->
  [T.Text] ->
  Map.Map T.Text BenchCase ->
  ChartOptions
mkPlot colMap k bg =
  let title = "Time (fill): " <> T.intercalate "/" k
      (timeSI, allocSI) =
        foldMap ((,) <$> detectSIPrefix Pico . mean <*> detectSIPrefix Unit . fromMaybe 0 . alloc) bg
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
