{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -funbox-strict-fields #-}

module Main (main) where

import Control.Applicative ((<**>))
import Data.Generics.Labels ()
import GHC.Generics (Generic)
import Options.Applicative ((<|>))
import qualified Options.Applicative as Opt
import Pages
import Report
import System.IO

main :: IO ()
main = do
  hSetBuffering stderr LineBuffering
  cmd <- Opt.execParser optsP
  case cmd of
    SingleReport opts -> generateSingleReport opts
    UpdateReportPages opts -> updateReportPages opts

data Cmd
  = SingleReport !SingleReportOpts
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
    p = SingleReport <$> singleReportOptsP
    updateP = UpdateReportPages <$> pagesOptsP
