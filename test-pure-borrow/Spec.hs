{-# LANGUAGE GHC2021 #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Main (main) where

import Control.Functor.Linear qualified as Control
import Control.Monad.Borrow.Pure
import Control.Syntax.DataFlow qualified as DataFlow
import Data.Array.Mutable.Linear.Unboxed.Borrow.Internal qualified as Fixed
import Data.Vector qualified as V
import Data.Vector.Mutable.Linear.Boxed.Borrow.Internal qualified as Boxed
import Data.Vector.Mutable.Linear.Unboxed.Borrow.Internal qualified as Grow
import Data.Vector.Unboxed qualified as U
import Logic.Propositional.Classical.SAT.CDCL.PureBorrow.Propagation.Internal qualified as Propagation
import Logic.Propositional.Classical.SAT.CDCL.PureBorrow.Store.Internal qualified as Store
import Prelude.Linear
import Test.Tasty (defaultMain, testGroup)
import Test.Tasty.HUnit (testCase, (@?=))
import Prelude qualified as NonLinear

main :: NonLinear.IO ()
main =
  defaultMain $
    testGroup
      "Pure Borrow stores"
      [ testCase "fixed write/read/reclaim" $
          fixedRoundTrip
            @?= (17, U.fromList [0, 17, 0])
      , testCase "unboxed forced growth preserves prefix" $
          growRoundTrip
            @?= U.fromList [0 .. 127]
      , testCase "boxed forced growth preserves prefix" $
          boxedRoundTrip
            @?= V.fromList [0 .. 127]
      , testCase "one pin spans a long no-growth write/read loop" $
          pinnedRoundTrip
            @?= (128, 256, 142, U.fromList [16 .. 143])
      , testCase "optimized allocations remain distinct" $
          distinctRoundTrip
            @?= (U.singleton 11, U.singleton 22)
      , testCase "five-field split pins every propagation root once" $
          architectureRoundTrip
            @?= architectureExpected
      , testCase "watch spike moves a watch and reaches fixpoint" $
          watchRoundTrip
            Propagation.ResumePropagation
            (Propagation.PropagationControl 0 1)
            moveSeed
            @?= moveExpected
      , testCase "watch spike enqueues and drains a unit chain" $
          watchRoundTrip
            Propagation.ResumePropagation
            (Propagation.PropagationControl 0 1)
            unitSeed
            @?= unitExpected
      , testCase "watch spike restores current and unread suffix on conflict" $
          watchRoundTrip
            Propagation.ResumePropagation
            (Propagation.PropagationControl 0 1)
            clauseConflictSeed
            @?= clauseConflictExpected
      , testCase "watch spike reports a root assertion conflict" $
          watchRoundTrip
            (Propagation.SeedRootUnit 7 0)
            (Propagation.PropagationControl 0 0)
            assertionConflictSeed
            @?= assertionConflictExpected
      ]

fixedRoundTrip :: (Int, U.Vector Int)
fixedRoundTrip =
  unur $
    linearly \linear -> DataFlow.do
      (allocationLinear, borrowLinear) <- dup linear
      array <- Fixed.constant 3 (0 :: Int) allocationLinear
      runBO borrowLinear Control.do
        (mutableArray, lender) <- borrowM array
        mutableArray <- Fixed.unsafeWrite 1 17 mutableArray
        (Ur observed, mutableArray) <-
          Fixed.unsafeCopyAtMut 1 mutableArray
        let !(Ur _) = share mutableArray
        pureAfter (freezeFixedResult observed (reclaim lender))

growRoundTrip :: U.Vector Int
growRoundTrip =
  unur $
    linearly \linear -> DataFlow.do
      (allocationLinear, borrowLinear) <- dup linear
      vector <- Grow.empty allocationLinear
      runBO borrowLinear Control.do
        (mutableVector, lender) <- borrowM vector
        mutableVector <- pushUnboxed [0 .. 127] mutableVector
        let !(Ur _) = share mutableVector
        pureAfter (Grow.toVector (reclaim lender))

pushUnboxed ::
  [Int] ->
  Mut lifetime (Grow.Vector Int) %1 ->
  BO lifetime (Mut lifetime (Grow.Vector Int))
pushUnboxed [] vector = Control.pure vector
pushUnboxed (value : rest) vector = Control.do
  vector <- Grow.push value vector
  pushUnboxed rest vector

boxedRoundTrip :: V.Vector Int
boxedRoundTrip =
  unur $
    linearly \linear -> DataFlow.do
      (allocationLinear, borrowLinear) <- dup linear
      vector <- Boxed.empty allocationLinear
      runBO borrowLinear Control.do
        (mutableVector, lender) <- borrowM vector
        mutableVector <- pushBoxed [0 .. 127] mutableVector
        let !(Ur _) = share mutableVector
        pureAfter (Boxed.toVector (reclaim lender))

pushBoxed ::
  [Int] ->
  Mut lifetime (Boxed.Vector Int) %1 ->
  BO lifetime (Mut lifetime (Boxed.Vector Int))
pushBoxed [] vector = Control.pure vector
pushBoxed (value : rest) vector = Control.do
  vector <- Boxed.push value vector
  pushBoxed rest vector

distinctRoundTrip :: (U.Vector Int, U.Vector Int)
distinctRoundTrip =
  unur $
    linearly \linear -> DataFlow.do
      (firstLinear, secondLinear, borrowLinear) <- dup3 linear
      first <- Fixed.constant 1 (0 :: Int) firstLinear
      second <- Fixed.constant 1 (0 :: Int) secondLinear
      runBO borrowLinear Control.do
        (firstBorrow, firstLender) <- borrowM first
        (secondBorrow, secondLender) <- borrowM second
        firstBorrow <- Fixed.unsafeWrite 0 11 firstBorrow
        secondBorrow <- Fixed.unsafeWrite 0 22 secondBorrow
        let !(Ur _) = share firstBorrow
        let !(Ur _) = share secondBorrow
        pureAfter
          ( freezeFixedPair
              (reclaim firstLender)
              (reclaim secondLender)
          )

freezeFixedResult ::
  Int ->
  Fixed.UArray Int %1 ->
  Ur (Int, U.Vector Int)
freezeFixedResult observed array =
  case Fixed.toVector array of
    Ur vector -> Ur (observed, vector)

freezeFixedPair ::
  Fixed.UArray Int %1 ->
  Fixed.UArray Int %1 ->
  Ur (U.Vector Int, U.Vector Int)
freezeFixedPair first second =
  case Fixed.toVector first of
    Ur firstVector ->
      case Fixed.toVector second of
        Ur secondVector ->
          Ur (firstVector, secondVector)

pinnedRoundTrip :: (Int, Int, Int, U.Vector Int)
pinnedRoundTrip =
  unur $
    linearly \linear -> DataFlow.do
      (allocationLinear, borrowLinear) <- dup linear
      vector <-
        Grow.fromVector
          (U.generate 256 id)
          allocationLinear
      runBO borrowLinear Control.do
        (vectorBorrow, lender) <- borrowM vector
        ((Ur logicalSize, Ur capacity, Ur observed), vectorBorrow) <-
          Grow.withPinned
            ( \initialPinned -> Control.do
                modifiedPinned <- modifyPinned 0 initialPinned
                let %1 !truncatedPinned =
                      Grow.pinnedTruncate 128 modifiedPinned
                let %1 !(Ur logicalSize, sizedPinned) =
                      Grow.pinnedSize truncatedPinned
                let %1 !(Ur capacity, capacityPinned) =
                      Grow.pinnedCapacity sizedPinned
                (Ur observed, finalPinned) <-
                  Grow.pinnedUnsafeCopyAt 126 capacityPinned
                Control.pure
                  ( (Ur logicalSize, Ur capacity, Ur observed)
                  , finalPinned
                  )
            )
            vectorBorrow
        let !(Ur _) = share vectorBorrow
        pureAfter
          ( freezePinnedResult
              logicalSize
              capacity
              observed
              (reclaim lender)
          )

modifyPinned ::
  Int ->
  Grow.Pinned pin Int %1 ->
  BO scope (Grow.Pinned pin Int)
modifyPinned iteration pinned
  | iteration == 4096 = Control.pure pinned
  | otherwise = Control.do
      (Ur (), pinned) <-
        Grow.pinnedUnsafeModify
          (\value -> (value + 1, ()))
          (iteration `mod` 256)
          pinned
      modifyPinned (iteration + 1) pinned

freezePinnedResult ::
  Int ->
  Int ->
  Int ->
  Grow.Vector Int %1 ->
  Ur (Int, Int, Int, U.Vector Int)
freezePinnedResult logicalSize capacity observed vector =
  case Grow.toVector vector of
    Ur frozen ->
      Ur (logicalSize, capacity, observed, frozen)

architectureRoundTrip ::
  ( Propagation.PropagationEvidence
  , Propagation.PropagationControl
  , Store.CDCLSnapshot
  )
architectureRoundTrip =
  unur $
    linearly \linear -> DataFlow.do
      (allocationLinear, borrowLinear) <- dup linear
      store <- Store.newCDCLStore architectureSeed allocationLinear
      runBO borrowLinear Control.do
        (storeBorrow, lender) <- borrowM store
        (Ur evidence, control, storeBorrow) <-
          Propagation.propagateArchitectureSpike
            (Propagation.PropagationControl 0 2)
            storeBorrow
        let !(Ur _) = share storeBorrow
        pureAfter
          ( freezeArchitectureResult
              evidence
              control
              (reclaim lender)
          )

freezeArchitectureResult ::
  Propagation.PropagationEvidence ->
  Propagation.PropagationControl %1 ->
  Store.CDCLStore s %1 ->
  Ur
    ( Propagation.PropagationEvidence
    , Propagation.PropagationControl
    , Store.CDCLSnapshot
    )
freezeArchitectureResult evidence control store =
  case move control of
    Ur unrestrictedControl ->
      case Store.freezeCDCLStore store of
        Ur snapshot ->
          Ur (evidence, unrestrictedControl, snapshot)

architectureSeed :: Store.CDCLSeed
architectureSeed =
  Store.CDCLSeed
    { Store.seedValuation = U.fromList [7, 8]
    , Store.seedTrail = U.fromList [0, 1]
    , Store.seedLevelStarts = U.fromList [0, 2]
    , Store.seedClauseLiterals =
        V.fromList
          [ Ur (U.fromList [0, 2])
          , Ur (U.fromList [1, 3, 5])
          ]
    , Store.seedClauseBodies = U.fromList [10, 20]
    , Store.seedWatchHeads = U.fromList [2, 3]
    , Store.seedWatchTails = U.fromList [4, 5]
    , Store.seedWatchNexts = U.fromList [-1, -1]
    , Store.seedVSIDSVisits = 0
    }

architectureExpected ::
  ( Propagation.PropagationEvidence
  , Propagation.PropagationControl
  , Store.CDCLSnapshot
  )
architectureExpected =
  ( Propagation.PropagationEvidence
      { Propagation.visitedOccurrences = 2
      , Propagation.observationChecksum = 63
      }
  , Propagation.PropagationControl 2 2
  , Store.CDCLSnapshot
      { Store.snapshotValuation = U.fromList [7, 8]
      , Store.snapshotTrail = U.fromList [0, 1]
      , Store.snapshotLevelStarts = U.fromList [0, 2]
      , Store.snapshotClauseLiterals =
          V.fromList
            [ U.fromList [0, 2]
            , U.fromList [1, 3, 5]
            ]
      , Store.snapshotClauseBodies = U.fromList [11, 21]
      , Store.snapshotWatchHeads = U.fromList [2, 3]
      , Store.snapshotWatchTails = U.fromList [4, 5]
      , Store.snapshotWatchNexts = U.fromList [-1, -1]
      , Store.snapshotVSIDSVisits = 2
      }
  )

data WatchObservation = WatchObservation
  { observedKernelEvidence :: !Propagation.KernelEvidence
  , observedKernelControl :: !Propagation.PropagationControl
  , observedValuation :: !(U.Vector Int)
  , observedTrail :: !(U.Vector Int)
  , observedClauseBodies :: !(U.Vector Int)
  , observedWatchHeads :: !(U.Vector Int)
  , observedWatchTails :: !(U.Vector Int)
  , observedWatchNexts :: !(U.Vector Int)
  , observedVSIDSVisits :: {-# UNPACK #-} !Int
  }
  deriving (NonLinear.Show, NonLinear.Eq)

watchRoundTrip ::
  Propagation.PropagationStart ->
  Propagation.PropagationControl %1 ->
  Store.CDCLSeed ->
  WatchObservation
watchRoundTrip start control seed =
  unur $
    linearly \linear -> DataFlow.do
      (allocationLinear, borrowLinear) <- dup linear
      store <- Store.newCDCLStore seed allocationLinear
      runBO borrowLinear Control.do
        (storeBorrow, lender) <- borrowM store
        (Ur evidence, control, storeBorrow) <-
          Propagation.propagateWatchSpike
            start
            control
            storeBorrow
        let !(Ur _) = share storeBorrow
        pureAfter
          ( freezeWatchResult
              evidence
              control
              (reclaim lender)
          )

freezeWatchResult ::
  Propagation.KernelEvidence ->
  Propagation.PropagationControl %1 ->
  Store.CDCLStore s %1 ->
  Ur WatchObservation
freezeWatchResult evidence control store =
  case move control of
    Ur unrestrictedControl ->
      case Store.freezeCDCLStore store of
        Ur snapshot ->
          Ur
            WatchObservation
              { observedKernelEvidence = evidence
              , observedKernelControl = unrestrictedControl
              , observedValuation = Store.snapshotValuation snapshot
              , observedTrail = Store.snapshotTrail snapshot
              , observedClauseBodies =
                  Store.snapshotClauseBodies snapshot
              , observedWatchHeads =
                  Store.snapshotWatchHeads snapshot
              , observedWatchTails =
                  Store.snapshotWatchTails snapshot
              , observedWatchNexts =
                  Store.snapshotWatchNexts snapshot
              , observedVSIDSVisits =
                  Store.snapshotVSIDSVisits snapshot
              }

encodedBody :: Int -> Int -> Int
encodedBody watched1 watched2 =
  (watched1 + 1) * 65536 + watched2 + 1

spikeSeed ::
  U.Vector Int ->
  U.Vector Int ->
  [U.Vector Int] ->
  U.Vector Int ->
  U.Vector Int ->
  U.Vector Int ->
  U.Vector Int ->
  Store.CDCLSeed
spikeSeed valuation trail clauses bodies heads tails nexts =
  Store.CDCLSeed
    { Store.seedValuation = valuation
    , Store.seedTrail = trail
    , Store.seedLevelStarts = U.singleton 0
    , Store.seedClauseLiterals =
        V.fromList (NonLinear.fmap Ur clauses)
    , Store.seedClauseBodies = bodies
    , Store.seedWatchHeads = heads
    , Store.seedWatchTails = tails
    , Store.seedWatchNexts = nexts
    , Store.seedVSIDSVisits = 0
    }

moveSeed :: Store.CDCLSeed
moveSeed =
  spikeSeed
    (U.fromList [1, 0, 0])
    (U.fromList [0, 0, 0])
    [U.fromList [1, 2, 4]]
    (U.singleton (encodedBody 0 1))
    (U.fromList [-1, 0, -1, -1, -1, -1])
    (U.fromList [-1, 0, -1, -1, -1, -1])
    (U.fromList [-1, -1])

moveExpected :: WatchObservation
moveExpected =
  WatchObservation
    { observedKernelEvidence =
        Propagation.KernelEvidence
          { Propagation.kernelExit =
              Propagation.PropagationComplete
          , Propagation.kernelVisited = 1
          , Propagation.kernelMoves = 1
          , Propagation.kernelEnqueues = 0
          }
    , observedKernelControl =
        Propagation.PropagationControl 1 1
    , observedValuation = U.fromList [1, 0, 0]
    , observedTrail = U.fromList [0, 0, 0]
    , observedClauseBodies =
        U.singleton (encodedBody 2 1)
    , observedWatchHeads =
        U.fromList [-1, -1, -1, -1, 0, -1]
    , observedWatchTails =
        U.fromList [-1, -1, -1, -1, 0, -1]
    , observedWatchNexts = U.fromList [-1, -1]
    , observedVSIDSVisits = 1
    }

unitSeed :: Store.CDCLSeed
unitSeed =
  spikeSeed
    (U.fromList [1, 0])
    (U.fromList [0, 0])
    [U.fromList [1, 2]]
    (U.singleton (encodedBody 0 1))
    (U.fromList [-1, 0, -1, -1])
    (U.fromList [-1, 0, -1, -1])
    (U.fromList [-1, -1])

unitExpected :: WatchObservation
unitExpected =
  WatchObservation
    { observedKernelEvidence =
        Propagation.KernelEvidence
          { Propagation.kernelExit =
              Propagation.PropagationComplete
          , Propagation.kernelVisited = 1
          , Propagation.kernelMoves = 0
          , Propagation.kernelEnqueues = 1
          }
    , observedKernelControl =
        Propagation.PropagationControl 2 2
    , observedValuation = U.fromList [1, 1]
    , observedTrail = U.fromList [0, 2]
    , observedClauseBodies =
        U.singleton (encodedBody 0 1)
    , observedWatchHeads = U.fromList [-1, 0, -1, -1]
    , observedWatchTails = U.fromList [-1, 0, -1, -1]
    , observedWatchNexts = U.fromList [-1, -1]
    , observedVSIDSVisits = 1
    }

clauseConflictSeed :: Store.CDCLSeed
clauseConflictSeed =
  spikeSeed
    (U.fromList [1, -1])
    (U.fromList [0, 0])
    [ U.fromList [1, 2]
    , U.fromList [1, 3]
    ]
    (U.fromList [encodedBody 0 1, encodedBody 0 1])
    (U.fromList [-1, 0, -1, -1])
    (U.fromList [-1, 2, -1, -1])
    (U.fromList [2, -1, -1, -1])

clauseConflictExpected :: WatchObservation
clauseConflictExpected =
  WatchObservation
    { observedKernelEvidence =
        Propagation.KernelEvidence
          { Propagation.kernelExit =
              Propagation.PropagationConflict
                Propagation.ClauseConflict
                0
                2
          , Propagation.kernelVisited = 1
          , Propagation.kernelMoves = 0
          , Propagation.kernelEnqueues = 0
          }
    , observedKernelControl =
        Propagation.PropagationControl 1 1
    , observedValuation = U.fromList [1, -1]
    , observedTrail = U.fromList [0, 0]
    , observedClauseBodies =
        U.fromList [encodedBody 0 1, encodedBody 0 1]
    , observedWatchHeads = U.fromList [-1, 0, -1, -1]
    , observedWatchTails = U.fromList [-1, 2, -1, -1]
    , observedWatchNexts = U.fromList [2, -1, -1, -1]
    , observedVSIDSVisits = 1
    }

assertionConflictSeed :: Store.CDCLSeed
assertionConflictSeed =
  spikeSeed
    (U.singleton (-1))
    (U.singleton 0)
    []
    U.empty
    (U.fromList [-1, -1])
    (U.fromList [-1, -1])
    U.empty

assertionConflictExpected :: WatchObservation
assertionConflictExpected =
  WatchObservation
    { observedKernelEvidence =
        Propagation.KernelEvidence
          { Propagation.kernelExit =
              Propagation.PropagationConflict
                Propagation.AssertionConflict
                7
                0
          , Propagation.kernelVisited = 0
          , Propagation.kernelMoves = 0
          , Propagation.kernelEnqueues = 0
          }
    , observedKernelControl =
        Propagation.PropagationControl 0 0
    , observedValuation = U.singleton (-1)
    , observedTrail = U.singleton 0
    , observedClauseBodies = U.empty
    , observedWatchHeads = U.fromList [-1, -1]
    , observedWatchTails = U.fromList [-1, -1]
    , observedWatchNexts = U.empty
    , observedVSIDSVisits = 0
    }
