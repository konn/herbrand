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
  filterFileTreeRoots,
  globTree,
  findCnfsIn,
  module Test.Tasty.Bench.CodSpeed,
  FileTrie (..),
  timeout,
  isMeasuring,
  unlessMeasuring,
) where

import CodSpeed.Instrument (Mode (..), detectMode)
import Control.DeepSeq (NFData, force)
import Control.Exception (evaluate)
import Control.Exception.Safe (throwString)
import Control.Lens hiding ((<.>))
import Control.Monad ((<=<))
import qualified Data.ByteString.Lazy as LBS
import qualified Data.Map.Strict as Map
import Data.String (IsString (..))
import qualified Data.Text as T
import Data.Text.Lens (packed)
import GHC.Generics (Generic)
import Logic.Propositional.Classical.SAT.Format.DIMACS
import Logic.Propositional.Syntax.General
import Logic.Propositional.Syntax.NormalForm.Classical.Conjunctive
import System.Directory
import System.Environment
import System.FilePath
import System.FilePath.Glob
import Test.Tasty (Timeout (..), localOption, withResource)
import Test.Tasty.Bench.CodSpeed hiding (defaultMain)
import qualified Test.Tasty.Bench.CodSpeed as CodSpeed
import Test.Tasty.ExpectedFailure (wrapTest)
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

filterFileTreeRoots :: (String -> Bool) -> FileTrie a -> FileTrie a
filterFileTreeRoots keep =
  FTree . Map.filterWithKey (\name _ -> keep name) . unFTree

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
  withFileTree $
    either throwString (evaluate . force . view _3)
      . parseSATLazy
      <=< LBS.readFile

withCnfs :: String -> FileTrie FilePath -> (IO (CNF Word, Formula Full Word) -> [Benchmark]) -> Benchmark
withCnfs =
  withFileTree $
    either
      throwString
      (evaluate . force . ((,) <$> id <*> toFormula) . view _3)
      . parseCNFLazy
      <=< LBS.readFile

{- | Run a benchmark tree, reporting each leaf to CodSpeed when a runner is
attached and behaving exactly like @tasty-bench@ when one is not.

This defers to "Test.Tasty.Bench.CodSpeed" rather than driving the ingredients
itself, because that runner has to own option parsing: it rewrites the tree to
open a measurement window around every leaf, and drops @tasty-bench@'s default
100-second timeout, which under CPU simulation is reached by half a second of
native work.

The @bench-results/@ defaults this used to install via 'changeOption' are
therefore supplied as arguments instead. They are only appended when absent, so
an explicit @--csv@ or @--svg@ still wins.

Note the tasty path is now rooted at @All@ rather than at the executable name;
the suite is identified to CodSpeed by the component prefix instead.
-}
defaultMain :: [Benchmark] -> IO ()
defaultMain b = do
  prog <- dropExtensions . takeFileName <$> getProgName
  createDirectoryIfMissing True benchResultDir
  args <- getArgs
  let withDefault flag ext as
        | flag `elem` as = as
        | otherwise = as <> [flag, benchResultDir </> prog <.> ext]
  withArgs (withDefault "--csv" "csv" $ withDefault "--svg" "svg" args) $
    CodSpeed.defaultMain b

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

{- | Whether CodSpeed will measure each benchmark leaf in this run.

Mirrors the two conditions "Test.Tasty.Bench.CodSpeed" itself takes the
measurement path on: a runner is attached (@CODSPEED_RUNNER_MODE@), or the
one-iteration path was forced for a side-car run (@CODSPEED_HS_DETERMINISTIC@).
-}
isMeasuring :: IO Bool
isMeasuring = do
  mode <- detectMode
  deterministic <- lookupEnv "CODSPEED_HS_DETERMINISTIC"
  pure $
    mode /= NotInstrumented
      || maybe False (\v -> v /= "" && v /= "0") deterministic

{- | Apply a benchmark wrapper only when CodSpeed is /not/ measuring.

Both of the wrappers this suite uses have to be dropped under measurement, for
different reasons, and dropping only one of them is worse than dropping neither.

'timeout' is a wall-clock cap, and simulation runs roughly 200x slower than
native — so a 100-second timeout is reached by half a second of real work. The
benchmark is cut short and the instrument still reports the instruction count of
the truncated run; because the cap is wall-clock, /which/ benchmarks get
truncated shifts with runner load. That is why "Test.Tasty.Bench.CodSpeed"
installs no default timeout when instrumented, but an explicit 'localOption' is
still honoured, so a suite setting its own has to opt out itself.

'allowFailureBecause' is the sharper problem, because it fails silently.
@instrumentTree@ finds benchmarks by @cast@ing each leaf to @Benchmarkable@, and
@wrapTest@ replaces the leaf with @tasty-expected-failure@'s own test type. The
cast then fails, the leaf is left alone, and __nothing is reported to CodSpeed__
— while the suite still runs, still prints results and still exits zero. The
only symptom is an empty run on the dashboard.
-}
unlessMeasuring :: (Benchmark -> Benchmark) -> IO (Benchmark -> Benchmark)
unlessMeasuring f = do
  measuring <- isMeasuring
  pure $ if measuring then id else f
