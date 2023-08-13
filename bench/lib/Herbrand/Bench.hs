module Herbrand.Bench (
  defaultMain,
  benchResultDir,
  module Test.Tasty.Bench,
) where

import Data.Maybe (fromMaybe)
import System.Directory
import System.Environment
import System.Exit
import System.FilePath
import Test.Tasty.Bench hiding (defaultMain)
import Test.Tasty.Ingredients
import Test.Tasty.Options
import Test.Tasty.Runners

benchResultDir :: FilePath
benchResultDir = "bench-results"

defaultMain :: [Benchmark] -> IO ()
defaultMain b = do
  prog <- dropExtensions . takeFileName <$> getProgName
  let bs = bgroup prog b
  opts <- parseOptions benchIngredients bs
  createDirectoryIfMissing True benchResultDir
  let opts' =
        changeOption
          (Just . fromMaybe (CsvPath $ benchResultDir </> prog <.> "csv"))
          opts
  case tryIngredients benchIngredients opts' bs of
    Nothing -> exitFailure
    Just mb -> mb >>= \ok -> if ok then exitSuccess else exitFailure
