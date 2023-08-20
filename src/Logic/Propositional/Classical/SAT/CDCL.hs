{-# LANGUAGE GHC2021 #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

-- | DPLL Algorithm, supercharged with Conflict-Driven Clause Learning (CDCL).
module Logic.Propositional.Classical.SAT.CDCL (propagateUnit) where

import Control.Applicative
import Control.Foldl qualified as L
import Control.Lens hiding (Index, (&))
import Control.Lens qualified as Lens
import Control.Lens.Extras qualified as Lens
import Data.Bifunctor.Linear qualified as BiL
import Data.Generics.Labels ()
import Data.HashMap.Mutable.Linear.Extra qualified as LHM
import Data.IntSet qualified as IS
import Data.Sequence (Seq (..))
import Data.Sequence qualified as Seq
import Data.Strict (Pair (..))
import Data.Vector.Mutable.Linear.Extra qualified as LV
import Data.Vector.Mutable.Linear.Unboxed qualified as LUV
import Data.Vector.Unboxed qualified as U
import Logic.Propositional.Classical.SAT.CDCL.Types
import Prelude.Linear hiding (not, (&&), (+), (-), (/=), (<), (==), (||))
import Prelude.Linear qualified as PL hiding ((+), (-))
import Unsafe.Linear qualified as Unsafe
import Prelude hiding (uncurry, ($))
import Prelude qualified as P

{-
unitPropInit :: CDLLState %1 -> (CDLLState, UnitResult)
unitPropInit (CDLLState steps clauses watches vals) =
  LV.findWith (uncurry findUnit) (steps, vals) clauses
    & \(m, (steps, vals), clauses) ->
      (CDLLState steps clauses watches vals, Ur.lift isJust m)
 -}

toClauseId :: Int -> ClauseId
toClauseId = fromIntegral

propagateUnit :: Maybe Lit -> CDLLState %1 -> (Ur PropResult, CDLLState)
propagateUnit = go IS.empty P.. P.maybe Seq.empty Seq.singleton
  where
    go :: IS.IntSet -> Seq.Seq Lit -> CDLLState %1 -> (Ur PropResult, CDLLState)
    go sats (l :<| rest) (CDLLState steps clauses watches vals) =
      LHM.lookup (litVar l) watches & \case
        (Ur Nothing, watches) -> go sats rest (CDLLState steps clauses watches vals)
        (Ur (Just targs), watches) ->
          loop sats (IS.toList targs) rest (CDLLState steps clauses watches vals)
      where
        loop :: IS.IntSet -> [Int] -> Seq.Seq Lit -> CDLLState %1 -> (Ur PropResult, CDLLState)
        loop !sats [] !rest !state = go sats rest state
        loop !sats (!i : !is) !rest (CDLLState steps clauses watches vals) =
          LV.unsafeGet i clauses & \(Ur c, clauses) ->
            propLit l vals c & \(Ur resl, vals) ->
              case resl of
                Nothing -> loop sats is rest (CDLLState steps clauses watches vals)
                Just (Conflict l) ->
                  ( Ur $ ConflictFound (toClauseId i) l
                  , CDLLState steps clauses watches vals
                  )
                Just (Satisfied Nothing) ->
                  loop (IS.insert i sats) is rest (CDLLState steps clauses watches vals)
                Just (Satisfied (Just ((w :!: old) :!: (new :!: newIdx)))) ->
                  Lens.set (watchVarL w) newIdx c & \c ->
                    LV.unsafeSet i c clauses & \clauses ->
                      moveWatchedFromTo i old new watches & \watches ->
                        loop (IS.insert i sats) is rest (CDLLState steps clauses watches vals)
                Just (WatchChangedFromTo w old new newIdx) ->
                  Lens.set (watchVarL w) newIdx c & \c ->
                    LV.unsafeSet i c clauses & \clauses ->
                      moveWatchedFromTo i old new watches & \watches ->
                        loop sats is rest (CDLLState steps clauses watches vals)
                Just (Unit l) ->
                  assertLit (toClauseId i) l steps vals & \(steps, vals) ->
                    loop
                      (IS.insert i sats)
                      is
                      (rest |> l)
                      (CDLLState steps clauses watches vals)
    go sats Seq.Empty (CDLLState steps clauses watches vals) =
      -- No literal given a priori. Find first literal.
      -- FIXME: Use heuristic for variable selection.
      LV.findWith
        (\vals i c -> if i `IS.notMember` sats then findUnit vals c else (Ur Nothing, vals))
        vals
        clauses
        & \(Ur resl, vals, clauses) ->
          case resl of
            Nothing -> (Ur NoMorePropagation, CDLLState steps clauses watches vals)
            Just (WatchChangedFromTo w old new newIdx, i) ->
              updateWatchLit i w newIdx clauses & \clauses ->
                moveWatchedFromTo i old new watches & \watches ->
                  go sats Seq.Empty (CDLLState steps clauses watches vals)
            Just (Satisfied Nothing, i) ->
              go (IS.insert i sats) Seq.Empty (CDLLState steps clauses watches vals)
            Just (Satisfied (Just ((w :!: old) :!: (new :!: newIdx))), i) ->
              updateWatchLit i w newIdx clauses & \clauses ->
                moveWatchedFromTo i old new watches & \watches ->
                  go (IS.insert i sats) Seq.Empty (CDLLState steps clauses watches vals)
            Just (Conflict ml, i) ->
              ( Ur (ConflictFound (toClauseId i) ml)
              , CDLLState steps clauses watches vals
              )
            Just (Unit l, i) ->
              assertLit (toClauseId i) l steps vals & \(steps, vals) ->
                go (IS.insert i sats) (Seq.singleton l) (CDLLState steps clauses watches vals)

updateWatchLit :: Int -> WatchVar -> Index -> Clauses %1 -> Clauses
updateWatchLit cid w vid =
  LV.modify_ (watchVarL w .~ vid) cid

assertLit :: ClauseId -> Lit -> LUV.Vector Step %1 -> Valuation %1 -> (LUV.Vector Step, Valuation)
assertLit antecedent lit stps vals =
  LUV.size stps & \(Ur len, stps) ->
    let curStp = len - 1
     in LUV.modify (\i -> (i + 1, fromIntegral curStp :!: i)) curStp stps
          & \(Ur introduced, stps) ->
            LHM.insert
              (litVar lit)
              Variable {value = isPositive lit, ..}
              vals
              & (stps,)

moveWatchedFromTo :: Int -> VarId -> VarId -> WatchMap %1 -> WatchMap
moveWatchedFromTo cid old new =
  LHM.alter (fmap $ IS.delete cid) old
    PL.. LHM.alter (fmap $ IS.insert cid) new

-- | Propagate Literal.
propLit :: Lit -> Valuation %1 -> Clause -> (Ur (Maybe UnitResult), Valuation)
propLit trueLit vals c@Clause {..} =
  let l = U.unsafeIndex lits watched1
   in if litVar l == litVar trueLit
        then -- Have the same variable as watched var #1

          if l == trueLit
            then (Ur (Just $ Satisfied Nothing), vals) -- Satisfied.
            else findNextAvailable vals W1 c -- False. Find next watched lit.
        else -- Otherwise it must be watched var #2

          if U.unsafeIndex lits watched2 == trueLit
            then (Ur (Just $ Satisfied Nothing), vals) -- Satisfied
            else findNextAvailable vals W2 c -- False. Find next watched lit.

findUnit ::
  Valuation %1 ->
  Clause ->
  (Ur (Maybe UnitResult), Valuation)
findUnit vals c@Clause {..}
  | watched2 < 0 -- Only the first literal is active.
    =
      let l = U.unsafeIndex lits watched1
       in evalLit l vals & \case
            (Just False, vals) ->
              (Ur $ Just (Conflict (Just l)), vals)
            (Just True, vals) ->
              (Ur $ Just $ Satisfied Nothing, vals)
            (Nothing, vals) ->
              (Ur $ Just (Unit l), vals)
  | otherwise -- The clause has more than two literals.
    =
      let l1 = U.unsafeIndex lits watched1
          l2 = U.unsafeIndex lits watched2
       in evalLit l1 vals & \case
            (Just True, vals) -> (Ur (Just $ Satisfied Nothing), vals) -- satisfied; nothing to do.
            (Just False, vals) ->
              -- Unsatisfiable literal: find next available literal for watched1
              findNextAvailable vals W1 c
            (Nothing, vals) ->
              -- Undetermined. Check for watched2
              evalLit l2 vals & \case
                (Just True, vals) ->
                  -- satisfied; nothing to do.
                  (Ur (Just $ Satisfied Nothing), vals)
                (Just False, vals) ->
                  -- Unsatisfiable literal: find next available literal for watched2
                  findNextAvailable vals W2 c
                (Nothing, vals) ->
                  -- No literal changed.
                  (Ur Nothing, vals)

getWatchedLit :: WatchVar -> Clause -> Lit
getWatchedLit W1 Clause {..} = U.unsafeIndex lits watched1
getWatchedLit W2 Clause {..} = U.unsafeIndex lits watched2

findNextAvailable :: Valuation %1 -> WatchVar -> Clause -> (Ur (Maybe UnitResult), Valuation)
findNextAvailable vals w c@Clause {..} =
  let lit = getWatchedLit w c
      origVar = litVar lit
   in unsafeMapMaybeL
        vals
        (P.curry P.. unassigned watched1 watched2)
        lits
        & \(Ur cands, vals) ->
          let (mSat, mUndet) =
                L.foldOver
                  (Lens.foldring U.foldr)
                  ( (,)
                      <$> (fmap fst <$> L.find ((== AssignedTrue) P.. P.snd))
                      <*> (fmap fst <$> L.find ((== Unassigned) P.. P.snd))
                  )
                  cands
           in case mSat of
                Just i ->
                  let v' = litVar $ U.unsafeIndex lits i
                   in (Ur (Just (Satisfied $ Just $ (w :!: origVar) :!: (v' :!: i))), vals)
                Nothing -> case mUndet of
                  Just i ->
                    let v' = litVar $ U.unsafeIndex lits i
                     in (Ur (Just $ WatchChangedFromTo w origVar v' i), vals)
                  Nothing -> (Ur (Just $ Conflict (Just lit)), vals)

unassigned :: Index -> Index -> Valuation -> (Int, Lit) -> Maybe AssignmentState
unassigned exc1 exc2 vals (cur, l)
  | cur == exc1 || cur == exc2 = Nothing
  | otherwise =
      evalLit l vals & \case
        (Nothing, _vals) -> Just Unassigned
        (Just True, _vals) -> Just AssignedTrue
        (Just False, _vals) -> Nothing

unsafeMapMaybeL ::
  forall a b s.
  (U.Unbox a, U.Unbox b) =>
  s %1 ->
  (s -> Int -> a -> Maybe b) ->
  U.Vector a ->
  (Ur (U.Vector (Int, b)), s)
unsafeMapMaybeL s p vs =
  Unsafe.toLinear (\s -> (Ur (p s), s)) s & \(Ur p, s) ->
    (Ur (U.imapMaybe (traverse P.. p) P.$ U.indexed vs), s)

evalLit :: Lit -> Valuation %1 -> (Maybe Bool, Valuation)
evalLit l vals =
  BiL.first
    ( \(Ur m) ->
        m
          <&> if Lens.is _PosL l
            then value
            else not P.. value
    )
    $ LHM.lookup (litVar l) vals
