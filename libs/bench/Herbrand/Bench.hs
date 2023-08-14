{-# LANGUAGE OverloadedStrings #-}

module Herbrand.Bench (
  defaultMain,
  benchResultDir,
  withSats,
  findSatsIn,
  module Test.Tasty.Bench,
  allowFailureBecause,
) where

import Control.Exception.Safe (throwString)
import Control.Lens hiding ((<.>))
import qualified Data.ByteString.Lazy as LBS
import Data.List (sortOn)
import Data.Maybe (fromMaybe)
import Logic.Propositional.Classical.SAT.Format.DIMACS
import Logic.Propositional.Syntax.General
import System.Directory
import System.Environment
import System.Exit
import System.FilePath
import System.FilePath.Glob
import Test.Tasty (withResource)
import Test.Tasty.Bench hiding (defaultMain)
import Test.Tasty.ExpectedFailure (wrapTest)
import Test.Tasty.Ingredients
import Test.Tasty.Options
import Test.Tasty.Runners

benchResultDir :: FilePath
benchResultDir = "bench-results"

findSatsIn :: FilePath -> IO [FilePath]
findSatsIn dir =
  sortOn takeFileName <$> globDir1 "**.sat" dir

withSats :: String -> [FilePath] -> (IO (Formula Full Word) -> [Benchmark]) -> Benchmark
withSats name chs act =
  bgroup
    name
    [ withResource
      (either throwString (pure . view _3) . parseSATLazy =<< LBS.readFile inp)
      mempty
      $ bgroup (takeFileName inp)
      . act
    | inp <- chs
    ]

defaultMain :: [Benchmark] -> IO ()
defaultMain b = do
  prog <- dropExtensions . takeFileName <$> getProgName
  let bs = bgroup prog b
  opts <- parseOptions benchIngredients bs
  createDirectoryIfMissing True benchResultDir
  let opts' =
        changeOption
          (Just . fromMaybe (SvgPath $ benchResultDir </> prog <.> "svg"))
          $ changeOption
            (Just . fromMaybe (CsvPath $ benchResultDir </> prog <.> "csv"))
            opts
  case tryIngredients benchIngredients opts' bs of
    Nothing -> exitFailure
    Just mb -> mb >>= \ok -> if ok then exitSuccess else exitFailure

allowFailureBecause :: String -> TestTree -> TestTree
allowFailureBecause reason = wrapTest $ fmap change
  where
    change r
      | resultSuccessful r = r
      | otherwise =
          r
            { resultOutcome = Success
            , resultDescription = resultDescription r <> " (allowed failure)"
            , resultShortDescription = resultShortDescription r <> " (allowed failure: " <> reason <> ")"
            }
