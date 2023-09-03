{-# LANGUAGE GHC2021 #-}
{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -funbox-strict-fields #-}

module Plot (mkPlots, Criteria (..), Criterion (..)) where

import Chart hiding (abs, (<.>))
import Control.Applicative (Applicative (..))
import Control.Arrow ((&&&))
import Control.Lens hiding ((<.>))
import Data.Align (alignWith)
import Data.DList qualified as DL
import Data.Filtrable (catMaybes)
import Data.Foldable (fold)
import Data.Generics.Labels ()
import Data.Map.Strict qualified as Map
import Data.Maybe (fromMaybe)
import Data.Text qualified as T
import Data.These (These (..))
import GHC.Generics (Generic, Generic1)
import Types
import Units

mkPlots ::
  Map.Map T.Text Colour ->
  [T.Text] ->
  Maybe (Map.Map T.Text BenchCase) ->
  Map.Map T.Text BenchCase ->
  Criteria ChartOptions
mkPlots colMap k mbase bg =
  let caseName = T.intercalate "/" k
      benchWithBase =
        maybe
          (fmap Current)
          ( fmap catMaybes . alignWith \case
              This {} -> Nothing
              That a -> Just $ Current a
              These a b -> Just $ b `WithBase` a
          )
          mbase
          bg
      Identity timePlot =
        makeBarChart
          ChartDef
            { chartTitle = "Time"
            , chartRadix = Decimal
            , chartUnit = "s"
            , defaultSIPrefix = Pico
            , valueL = #mean . to Identity
            , errorL = Just #stddev2
            }
          caseName
          colMap
          benchWithBase
      allocPlot =
        makeBarChart
          ChartDef
            { chartTitle = "Alloc"
            , chartRadix = Binary
            , chartUnit = "B"
            , defaultSIPrefix = Unit
            , valueL = #alloc
            , errorL = Nothing
            }
          caseName
          colMap
          benchWithBase
      copiedPlot =
        makeBarChart
          ChartDef
            { chartTitle = "Copied"
            , chartRadix = Binary
            , chartUnit = "B"
            , defaultSIPrefix = Unit
            , valueL = #copied
            , errorL = Nothing
            }
          caseName
          colMap
          benchWithBase
   in Criteria {..}

data ChartDef t = ChartDef
  { chartTitle :: !T.Text
  , chartRadix :: !Radix
  , defaultSIPrefix :: !SIPrefix
  , chartUnit :: !T.Text
  , valueL :: Getter BenchCase (t Integer)
  , errorL :: Maybe (Getter BenchCase Integer)
  }

data WithBase a = Current a | a `WithBase` a
  deriving (Show, Eq, Ord, Generic, Generic1, Functor, Foldable, Traversable)

getCurrent :: WithBase a -> a
getCurrent (Current a) = a
getCurrent (WithBase a _) = a

getBase :: WithBase a -> Maybe a
getBase Current {} = Nothing
getBase (_ `WithBase` b) = Just b

makeBarChart ::
  (Applicative t, Foldable t) =>
  ChartDef t ->
  T.Text ->
  Map.Map T.Text Colour ->
  Map.Map T.Text (WithBase BenchCase) ->
  t ChartOptions
makeBarChart ChartDef {..} caseName colMap bg0 =
  traverse (liftA2 (,) <$> pure <*> view valueL . getCurrent) bg0 <&> \bg ->
    let
      mkBarRow !nam !targ !val =
        let cur = getCurrent targ
            mbase = getBase targ
            mBaseVal = preview (valueL . folded) =<< mbase
            valStyle =
              let col = fromMaybe (grey 0.5 0.4) $ Map.lookup nam colMap
               in defaultRectStyle
                    & #color .~ col
                    & #borderSize .~ 0.0
            baseStyle =
              let col = fromMaybe (grey 0.5 0.4) $ Map.lookup nam colMap
               in case col of
                    Colour r g b a ->
                      defaultRectStyle
                        & #color .~ Colour r g b (a * 0.25)
                        & #borderSize .~ 0.001
                        & #borderColor .~ col
            styles = DL.cons valStyle $ fold $ DL.singleton baseStyle <$ mBaseVal
            vals =
              adjustSITo chartRadix defaultSIPrefix targetSI
                <$> DL.cons val (foldMap DL.singleton mBaseVal)
            labs = DL.cons nam $ foldMap (const $ DL.singleton (nam <> ", Baseline")) mBaseVal
            dev' =
              fmap
                ( \l ->
                    adjustSITo chartRadix defaultSIPrefix targetSI
                      <$> DL.cons
                        (cur ^. l `quot` 2)
                        ( foldMap
                            (DL.singleton . (`quot` 2) . view l)
                            mbase
                        )
                )
                errorL
         in (vals, dev', labs, styles)
      (fromMaybe Unit -> !targetSI, (values, devs, labels, rectStyles)) =
        ifoldMap
          ( \i ->
              (detectSIPrefix chartRadix defaultSIPrefix . snd)
                &&& uncurry (mkBarRow i)
          )
          bg
      theBars =
        BarData
          { barData = map pure $ DL.toList values
          , barRowLabels = []
          , barColumnLabels = DL.toList labels
          }
      barXYes =
        theBars
          ^.. #barData
            . to (barRects barOpts)
            . folded
            . folded
            . to \(Rect x0 x1 _ y1) ->
              (Point ((x0 + x1) / 2) y1, x1 - x0)
      xAxis =
        defaultAxisOptions
          & #ticks . #ltick .~ Nothing
          & #ticks . #style
            .~ TickPlaced
              (zip (map (_x . fst) barXYes) $ DL.toList labels)
      yAxis = defaultAxisOptions & #place .~ PlaceLeft
      barOpts =
        defaultBarOptions
          & #displayValues .~ False
          & #barRectStyles .~ DL.toList rectStyles
          & #barLegendOptions . #place .~ PlaceAbsolute (Point 1.0 (-0.5))
          & #barLegendOptions . #overallScale .~ 0.175
      theBar = barChart barOpts theBars
      errs =
        foldMap
          ( zipWith
              ( \(Point x y, w) sigma ->
                  let sty = defaultLineStyle & #size .~ 0.0015
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
        defaultTitle (chartTitle <> " [" <> T.pack (showPrefix chartRadix targetSI) <> chartUnit <> "]")
          & #place .~ PlaceLeft
          & #anchor .~ AnchorMiddle
          & #style . #size %~ (/ 2)
      title = chartTitle <> ": " <> caseName
     in
      theBar
        & #hudOptions . #chartAspect .~ FixedAspect ((1 + sqrt 5) / 2)
        & #hudOptions . #axes .~ [(5, xAxis), (5, yAxis)]
        & #hudOptions . #titles .~ [(6, defaultTitle title), (11, yAxisLabel)]
        & #hudOptions . #frames .~ [(11, defaultFrameOptions & #buffer .~ 0.2)]
        & #charts <>~ named "errors" errs
