{-# LANGUAGE GHC2021 #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Main (main) where

import Control.Functor.Linear qualified as Control
import Control.Monad.Borrow.Pure
import Control.Syntax.DataFlow qualified as DataFlow
import Data.Array.Mutable.Linear.Unboxed qualified as LegacyFixed
import Data.Vector qualified as V
import Data.Vector.Mutable qualified as MV
import Data.Vector.Mutable.Linear.Unboxed qualified as LegacyGrow
import Data.Vector.Unboxed qualified as U
import Data.Vector.Unboxed.Mutable qualified as UM
import GHC.IO (unsafePerformIO)
import Linear.Token.Linearly qualified as Legacy
import Logic.Propositional.Classical.SAT.CDCL.PureBorrow.Propagation.Internal qualified as Propagation
import Logic.Propositional.Classical.SAT.CDCL.PureBorrow.Store.Internal qualified as Store
import Prelude.Linear
import Test.Tasty.Bench (bench, defaultMain, nf)
import Prelude qualified as NonLinear

main :: NonLinear.IO ()
main =
  defaultMain
    [ bench "direct-io-watch-kernel/4096" $
        nf baselineWatchCount 4096
    , bench "legacy-linear-watch-kernel/4096" $
        nf legacyWatchCount 4096
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

legacyWatchCount :: Int -> Int
{-# NOINLINE legacyWatchCount #-}
legacyWatchCount count =
  unur (Legacy.linearly (legacyWatchCountOwned count))

legacyWatchCountOwned :: Int -> Legacy.Linearly %1 -> Ur Int
legacyWatchCountOwned count linear =
  let !clauses =
        V.replicate
          count
          (U.fromList [1, 2] :: U.Vector Int)
      %1 !kernel = newLegacyKernel count linear
   in detachLegacyBucket kernel
        & \(Ur first, kernel) ->
          legacyOccurrenceLoop 0 first clauses kernel
            & \(Ur visited, kernel) ->
              freezeLegacyCount visited clauses kernel

data LegacyKernel where
  LegacyKernel ::
    LegacyFixed.UArray Int %1 ->
    LegacyFixed.UArray Int %1 ->
    LegacyGrow.Vector Int %1 ->
    LegacyFixed.UArray Int %1 ->
    LegacyFixed.UArray Int %1 ->
    LegacyGrow.Vector Int %1 ->
    LegacyKernel

newLegacyKernel :: Int -> Legacy.Linearly %1 -> LegacyKernel
newLegacyKernel count linear =
  Legacy.besides
    linear
    (LegacyFixed.fromVectorL (U.fromList [1, 1]))
    & \(valuation, linear) ->
      Legacy.besides
        linear
        (LegacyFixed.fromVectorL (U.fromList [0, 0]))
        & \(trail, linear) ->
          Legacy.besides
            linear
            ( LegacyGrow.fromVectorL
                (U.replicate count (encodedBody 0 1))
            )
            & \(bodies, linear) ->
              Legacy.besides
                linear
                ( LegacyFixed.fromVectorL
                    ( U.fromList
                        [ -1
                        , if count == 0 then -1 else 0
                        , -1
                        , -1
                        ]
                    )
                )
                & \(heads, linear) ->
                  Legacy.besides
                    linear
                    ( LegacyFixed.fromVectorL
                        ( U.fromList
                            [ -1
                            , if count == 0
                                then -1
                                else 2 * (count - 1)
                            , -1
                            , -1
                            ]
                        )
                    )
                    & \(tails, linear) ->
                      LegacyKernel
                        valuation
                        trail
                        bodies
                        heads
                        tails
                        ( LegacyGrow.fromVectorL
                            ( U.generate (2 * count) \index ->
                                if NonLinear.even index
                                  && index
                                  + 2
                                  < 2
                                  * count
                                  then index + 2
                                  else -1
                            )
                            linear
                        )

detachLegacyBucket :: LegacyKernel %1 -> (Ur Int, LegacyKernel)
detachLegacyBucket (LegacyKernel valuation trail bodies heads tails nexts) =
  LegacyFixed.unsafeGet 1 heads
    & \(Ur first, heads) ->
      ( Ur first
      , LegacyKernel
          valuation
          trail
          bodies
          (LegacyFixed.unsafeSet 1 (-1) heads)
          (LegacyFixed.unsafeSet 1 (-1) tails)
          nexts
      )

legacyOccurrenceLoop ::
  Int ->
  Int ->
  V.Vector (U.Vector Int) ->
  LegacyKernel %1 ->
  (Ur Int, LegacyKernel)
legacyOccurrenceLoop
  !visited
  !occurrence
  clauses
  (LegacyKernel valuation trail bodies heads tails nexts) =
    if occurrence < 0
      then
        (Ur visited, LegacyKernel valuation trail bodies heads tails nexts)
      else
        LegacyGrow.unsafeGet occurrence nexts
          & \(Ur nextOccurrence, nexts) ->
            let !clauseId = occurrence `NonLinear.div` 2
             in LegacyGrow.unsafeGet clauseId bodies
                  & \(Ur body, bodies) ->
                    let !clause = V.unsafeIndex clauses clauseId
                        !otherIndex =
                          body `NonLinear.mod` 65536 - 1
                        !otherLiteral =
                          U.unsafeIndex clause otherIndex
                     in LegacyFixed.unsafeGet
                          (otherLiteral `NonLinear.div` 2)
                          valuation
                          & \(Ur variable, valuation) ->
                            LegacyFixed.unsafeGet 1 tails
                              & \(Ur oldTail, tails) ->
                                if oldTail < 0
                                  then
                                    variable `lseq`
                                      legacyOccurrenceLoop
                                        (visited + 1)
                                        nextOccurrence
                                        clauses
                                        ( LegacyKernel
                                            valuation
                                            trail
                                            bodies
                                            ( LegacyFixed.unsafeSet
                                                1
                                                occurrence
                                                heads
                                            )
                                            ( LegacyFixed.unsafeSet
                                                1
                                                occurrence
                                                tails
                                            )
                                            ( LegacyGrow.unsafeSet
                                                occurrence
                                                (-1)
                                                nexts
                                            )
                                        )
                                  else
                                    variable `lseq`
                                      legacyOccurrenceLoop
                                        (visited + 1)
                                        nextOccurrence
                                        clauses
                                        ( LegacyKernel
                                            valuation
                                            trail
                                            bodies
                                            heads
                                            ( LegacyFixed.unsafeSet
                                                1
                                                occurrence
                                                tails
                                            )
                                            ( LegacyGrow.unsafeSet
                                                oldTail
                                                occurrence
                                                ( LegacyGrow.unsafeSet
                                                    occurrence
                                                    (-1)
                                                    nexts
                                                )
                                            )
                                        )

freezeLegacyCount ::
  Int ->
  V.Vector (U.Vector Int) ->
  LegacyKernel %1 ->
  Ur Int
freezeLegacyCount
  visited
  clauses
  (LegacyKernel valuation trail bodies heads tails nexts) =
    case LegacyFixed.freeze valuation of
      Ur frozenValuation ->
        case LegacyFixed.freeze trail of
          Ur frozenTrail ->
            case LegacyGrow.freeze bodies of
              Ur frozenBodies ->
                case LegacyFixed.freeze heads of
                  Ur frozenHeads ->
                    case LegacyFixed.freeze tails of
                      Ur frozenTails ->
                        case LegacyGrow.freeze nexts of
                          Ur frozenNexts ->
                            Ur
                              ( visited
                                  + U.length frozenValuation
                                  + U.length frozenTrail
                                  + U.length frozenBodies
                                  + V.length clauses
                                  + U.length frozenHeads
                                  + U.length frozenTails
                                  + U.length frozenNexts
                              )

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
