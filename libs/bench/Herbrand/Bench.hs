{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}

module Herbrand.Bench (
  defaultMain,
  allowFailureBecause,
  benchResultDir,
  withSats,
  findSatsIn,
  withCnfs,
  withFileTree,
  globTree,
  findCnfsIn,
  module Test.Tasty.Bench,
  FileTrie (..),
  timeout,
) where

import Control.DeepSeq (NFData, force)
import Control.Exception (evaluate)
import Control.Exception.Safe (throwString)
import Control.Lens hiding ((<.>))
import Control.Monad ((<=<))
import qualified Data.ByteString.Lazy as LBS
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)
import Data.String (IsString (..))
import qualified Data.Text as T
import Data.Text.Lens (packed)
import GHC.Generics (Generic)
import Logic.Propositional.Classical.SAT.Format.DIMACS
import Logic.Propositional.Syntax.General
import Logic.Propositional.Syntax.NormalForm.Classical.Conjunctive
import System.Directory
import System.Environment
import System.Exit
import System.FilePath
import System.FilePath.Glob
import Test.Tasty (Timeout (..), localOption, withResource)
import Test.Tasty.Bench hiding (defaultMain)
import Test.Tasty.ExpectedFailure (wrapTest)
import Test.Tasty.Ingredients
import Test.Tasty.Options
import Test.Tasty.Runners

benchResultDir :: FilePath
benchResultDir = "bench-results"

newtype FileTrie a = FTree {unFTree :: Map.Map String (Maybe a, FileTrie a)}
  deriving (Show, Eq, Ord, Generic)
  deriving newtype (Semigroup, Monoid)
  deriving newtype (NFData)

singletonFTs :: [FilePath] -> a -> FileTrie a
singletonFTs fps0 x = go fps0
  where
    go [] = error "Empty path"
    go [fp] = FTree $ Map.singleton fp (Just x, mempty)
    go (fp : fps) = FTree $ Map.singleton fp (Nothing, go fps)

insertFT :: FilePath -> a -> FileTrie a -> FileTrie a
insertFT fp (x :: a) = go (splitPath' fp)
  where
    go :: [FilePath] -> FileTrie a -> FileTrie a
    go [] = error "Must be non-empty path!"
    go [p] = FTree . Map.insert p (Just x, mempty) . unFTree
    go (p : xs) =
      FTree
        . Map.alter
          (maybe (Just (Nothing, singletonFTs xs x)) (Just . fmap (go xs)))
          p
        . unFTree

splitPath' :: FilePath -> [FilePath]
splitPath' = map (packed %~ T.dropWhileEnd (== '/')) . splitPath

globTree :: String -> FilePath -> IO (FileTrie FilePath)
globTree ext dir =
  foldr
    (insertFT <$> makeRelative dir <*> id)
    mempty
    <$> globDir1 (fromString $ "**/*" <.> ext) dir

findSatsIn :: FilePath -> IO (FileTrie FilePath)
findSatsIn = globTree "sat"

findCnfsIn :: FilePath -> IO (FileTrie FilePath)
findCnfsIn = globTree "cnf"

withFileTree :: (FilePath -> IO a) -> String -> FileTrie FilePath -> (IO a -> [Benchmark]) -> Benchmark
withFileTree alloc name0 trie act = go name0 trie
  where
    go name chs =
      bgroup
        name
        [ case mv of
          Just inp ->
            withResource (alloc inp) mempty $ bgroup label . act
          Nothing -> go label chs'
        | (label, (mv, chs')) <- Map.toList $ unFTree chs
        ]

withSats :: String -> FileTrie FilePath -> (IO (Formula Full Word) -> [Benchmark]) -> Benchmark
withSats =
  withFileTree
    $ either throwString (evaluate . force . view _3)
    . parseSATLazy
    <=< LBS.readFile

withCnfs :: String -> FileTrie FilePath -> (IO (CNF Word, Formula Full Word) -> [Benchmark]) -> Benchmark
withCnfs =
  withFileTree
    $ either
      throwString
      (evaluate . force . ((,) <$> id <*> toFormula) . view _3)
    . parseCNFLazy
    <=< LBS.readFile

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

timeout :: Integer -> TestTree -> TestTree
timeout n = localOption (Timeout (n * 10 ^ (6 :: Int)) $ show n <> "s")
