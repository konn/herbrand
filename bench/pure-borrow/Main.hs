{-# LANGUAGE GHC2021 #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Main (main) where

import CdfMultiStoreScan qualified as MultiStore
import Control.Functor.Linear qualified as Control
import Control.Monad.Borrow.Pure
import Control.Syntax.DataFlow qualified as DataFlow
import Data.Vector qualified as V
import Data.Vector.Mutable qualified as MV
import Data.Vector.Unboxed qualified as U
import Data.Vector.Unboxed.Mutable qualified as UM
import GHC.IO (unsafePerformIO)
import Logic.Propositional.Classical.SAT.CDCL.Propagation.Internal qualified as Propagation
import Logic.Propositional.Classical.SAT.CDCL.Store.Internal qualified as Store
import Prelude.Linear
import Test.Tasty.Bench (bench, defaultMain, nf)
import Prelude qualified as NonLinear

main :: NonLinear.IO ()
main =
  defaultMain
    [ bench "multi-store-scan/direct/4096" $
        nf MultiStore.directRoot MultiStore.standardInput
    , bench "multi-store-scan/direct-header-matched/4096" $
        nf MultiStore.directHeaderMatchedRoot MultiStore.standardInput
    , bench "multi-store-scan/pure-borrow-direct/4096" $
        nf MultiStore.pureBorrowDirectRoot MultiStore.standardInput
    , bench "multi-store-scan/pure-borrow-nested/4096" $
        nf MultiStore.pureBorrowNestedRoot MultiStore.standardInput
    , bench "multi-store-scan/pure-borrow-unrestricted-direct/4096" $
        nf MultiStore.pureBorrowUnrestrictedDirectRoot MultiStore.standardInput
    , bench "multi-store-scan/pure-borrow-unrestricted-nested/4096" $
        nf MultiStore.pureBorrowUnrestrictedNestedRoot MultiStore.standardInput
    , bench "direct-io-watch-kernel/4096" $
        nf baselineWatchCount 4096
    , bench "pure-borrow-watch-kernel/4096" $
        nf borrowedWatchCount 4096
    ]

baselineWatchCount :: Int -> Int
{-# NOINLINE baselineWatchCount #-}
baselineWatchCount count =
  unsafePerformIO do
    valuation <- UM.replicate 2 (1 :: Int)
    trail <- UM.replicate 2 (0 :: Int)
    bodies <- UM.replicate count (encodedBody 0 1)
    literals <-
      MV.replicate
        count
        (U.fromList [1, 2] :: U.Vector Int)
    heads <- UM.replicate 4 (-1 :: Int)
    tails <- UM.replicate 4 (-1 :: Int)
    nexts <-
      U.thaw $
        U.generate (2 * count) \index ->
          if NonLinear.even index && index + 2 < 2 * count
            then index + 2
            else -1
    UM.unsafeWrite heads 1 (if count == 0 then -1 else 0)
    UM.unsafeWrite tails 1 (if count == 0 then -1 else 2 * (count - 1))
    first <- UM.unsafeRead heads 1
    UM.unsafeWrite heads 1 (-1)
    UM.unsafeWrite tails 1 (-1)
    visited <-
      let loop !total !occurrence
            | occurrence < 0 = NonLinear.pure total
            | otherwise = do
                nextOccurrence <- UM.unsafeRead nexts occurrence
                let clauseId = occurrence `NonLinear.div` 2
                body <- UM.unsafeRead bodies clauseId
                clause <- MV.unsafeRead literals clauseId
                variable <- UM.unsafeRead valuation 1
                oldTail <- UM.unsafeRead tails 1
                UM.unsafeWrite nexts occurrence (-1)
                if oldTail < 0
                  then UM.unsafeWrite heads 1 occurrence
                  else UM.unsafeWrite nexts oldTail occurrence
                UM.unsafeWrite tails 1 occurrence
                body `NonLinear.seq`
                  U.length clause `NonLinear.seq`
                    variable `NonLinear.seq`
                      loop (total + 1) nextOccurrence
       in loop 0 first
    frozenValuation <- U.unsafeFreeze valuation
    frozenTrail <- U.unsafeFreeze trail
    frozenBodies <- U.unsafeFreeze bodies
    frozenLiterals <- V.unsafeFreeze literals
    frozenHeads <- U.unsafeFreeze heads
    frozenTails <- U.unsafeFreeze tails
    frozenNexts <- U.unsafeFreeze nexts
    NonLinear.pure $
      visited
        + U.length frozenValuation
        + U.length frozenTrail
        + U.length frozenBodies
        + V.length frozenLiterals
        + U.length frozenHeads
        + U.length frozenTails
        + U.length frozenNexts

borrowedWatchCount :: Int -> Int
{-# NOINLINE borrowedWatchCount #-}
borrowedWatchCount count =
  unur $
    linearly \linear -> DataFlow.do
      (allocationLinear, borrowLinear) <- dup linear
      store <-
        Store.newCDCLStore
          (watchSeed count)
          allocationLinear
      runBO borrowLinear Control.do
        (storeBorrow, lender) <- borrowM store
        (Ur evidence, control, storeBorrow) <-
          Propagation.propagateWatchSpike
            Propagation.ResumePropagation
            (Propagation.PropagationControl 0 1)
            storeBorrow
        let !(Ur _) = share storeBorrow
        pureAfter
          (finishBorrowedCount evidence control (reclaim lender))

finishBorrowedCount ::
  Propagation.KernelEvidence ->
  Propagation.PropagationControl %1 ->
  Store.CDCLStore s %1 ->
  Ur Int
finishBorrowedCount evidence control store =
  case move control of
    Ur _ ->
      case Store.freezeCDCLStore store of
        Ur snapshot ->
          Ur
            ( Propagation.kernelVisited evidence
                + U.length (Store.snapshotValuation snapshot)
                + U.length (Store.snapshotTrail snapshot)
                + U.length (Store.snapshotClauseBodies snapshot)
                + V.length (Store.snapshotClauseLiterals snapshot)
                + U.length (Store.snapshotWatchHeads snapshot)
                + U.length (Store.snapshotWatchTails snapshot)
                + U.length (Store.snapshotWatchNexts snapshot)
            )

watchSeed :: Int -> Store.CDCLSeed
watchSeed count =
  Store.CDCLSeed
    { Store.seedValuation = U.fromList [1, 1]
    , Store.seedTrail = U.fromList [0, 0]
    , Store.seedLevelStarts = U.singleton 0
    , Store.seedClauseLiterals =
        V.replicate count (Ur (U.fromList [1, 2]))
    , Store.seedClauseBodies =
        U.replicate count (encodedBody 0 1)
    , Store.seedWatchHeads =
        U.fromList [-1, if count == 0 then -1 else 0, -1, -1]
    , Store.seedWatchTails =
        U.fromList
          [ -1
          , if count == 0 then -1 else 2 * (count - 1)
          , -1
          , -1
          ]
    , Store.seedWatchNexts =
        U.generate (2 * count) \index ->
          if NonLinear.even index && index + 2 < 2 * count
            then index + 2
            else -1
    , Store.seedVSIDSVisits = 0
    }

encodedBody :: Int -> Int -> Int
encodedBody watched1 watched2 =
  (watched1 + 1) * 65536 + watched2 + 1
