{-# LANGUAGE GHC2021 #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

-- | DPLL Algorithm, supercharged with Conflict-Driven Clause Learning (CDCL).
module Logic.Propositional.Classical.SAT.CDCL (
  solveState,
  propagateUnit,
) where

import Control.Applicative
import Control.Foldl qualified as L
import Control.Functor.Linear.State.Extra qualified as S
import Control.Lens hiding (Index, lens, (&))
import Control.Lens qualified as Lens
import Control.Lens.Extras qualified as Lens
import Control.Monad (guard)
import Control.Optics.Linear (lens)
import Control.Optics.Linear qualified as Opt
import Data.Alloc.Linearly.Token (besides)
import Data.Array.Mutable.Linear.Unboxed qualified as LUA
import Data.Array.Polarized.Pull.Extra qualified as Pull
import Data.Bifunctor.Linear qualified as BiL
import Data.Function (fix)
import Data.Generics.Labels ()
import Data.HashMap.Mutable.Linear.Extra qualified as LHM
import Data.HashSet qualified as HS
import Data.IntSet qualified as IS
import Data.Sequence (Seq (..))
import Data.Sequence qualified as Seq
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Set.Mutable.Linear.Extra qualified as LSet
import Data.Strict (Pair (..))
import Data.Unrestricted.Linear qualified as Ur
import Data.Vector.Internal.Check
import Data.Vector.Mutable.Linear.Helpers qualified as LV
import Data.Vector.Mutable.Linear.Unboxed qualified as LUV
import Data.Vector.Unboxed qualified as U
import Logic.Propositional.Classical.SAT.CDCL.Types
import Logic.Propositional.Classical.SAT.Types
import Prelude.Linear hiding (not, (&&), (+), (-), (.), (/=), (<), (==), (||))
import Prelude.Linear qualified as PL
import Unsafe.Linear qualified as Unsafe
import Prelude hiding (uncurry, ($))
import Prelude qualified as P

solveState :: CDCLState %1 -> Ur (SatResult (Model VarId))
solveState = toSatResult PL.. S.execState (solverLoop Nothing)

solverLoop :: Maybe Lit -> S.State CDCLState ()
solverLoop = fix \go mlit -> S.do
  Ur resl <- propagateUnit mlit
  case resl of
    ConflictFound cid l ->
      -- Conflict found. Let's Backjump!
      backjump cid l
    NoMorePropagation -> S.do
      -- Decide indefinite variable
      -- FIXME: Use heuristics for variable selection.
      Ur mid <- S.uses valuationL (LUA.findIndex (Lens.is #_Indefinite))
      case mid of
        Nothing -> S.pure () -- No vacant variable - model is full!
        Just vid -> S.do
          Ur newDec <- S.uses stepsL LUV.size
          stepsL S.%= LUV.push 1
          valuationL
            S.%= LUA.unsafeSet
              vid
              Definite
                { value = True
                , decisionStep = fromIntegral newDec
                , decideLevel = 0
                , antecedent = Nothing
                }
          go (Just (PosL $ toEnum vid))

backjump ::
  ClauseId ->
  Lit ->
  S.State CDCLState ()
backjump confCls lit = undefined

resolve :: Lit -> Set Lit -> Set Lit -> Set Lit
resolve lit l r =
  Set.filter ((/= litVar lit) . litVar) l P.<> Set.filter ((/= litVar lit) . litVar) r

toSatResult :: CDCLState %1 -> Ur (SatResult (Model VarId))
toSatResult (CDCLState steps clauses watches vals) =
  steps
    `lseq` clauses
    `lseq` watches
    `lseq` ( LUA.freeze vals & Ur.lift do
              Satisfiable
                . Lens.foldMapOf
                  (Lens.foldring U.foldr)
                  ( \(k, var) ->
                      case var of
                        Definite {..} ->
                          if value
                            then P.mempty {positive = HS.singleton $ fromIntegral k}
                            else P.mempty {negative = HS.singleton $ fromIntegral k}
                        Indefinite -> P.mempty
                  )
                . U.indexed
           )

toClauseId :: Int -> ClauseId
toClauseId = fromIntegral

propagateUnit :: Maybe Lit -> S.State CDCLState (Ur PropResult)
propagateUnit ml = S.do
  Ur cap <- S.state numClauses
  sats <- S.state $ \st -> besides st (`LSet.emptyL` cap)
  go sats (P.maybe Seq.empty Seq.singleton ml)
  where
    go :: LSet.Set Int %1 -> Seq.Seq Lit -> S.State CDCLState (Ur PropResult)
    go sats (l :<| rest) = S.do
      Ur m <- S.uses watchesL $ LHM.lookup (litVar l)
      case m of
        Nothing -> go sats rest
        Just targs -> loop sats (IS.toList targs) rest
      where
        loop :: LSet.Set Int %1 -> [Int] -> Seq.Seq Lit -> S.State CDCLState (Ur PropResult)
        loop !sats [] !rest = go sats rest
        loop !sats (!i : !is) !rest = S.do
          Ur c <- S.uses clausesL $ LV.unsafeGet i
          Ur resl <- S.zoom valuationL $ propLit l c
          case resl of
            Nothing -> loop sats is rest
            Just (Conflict l) ->
              sats `lseq` S.pure (Ur (ConflictFound (toClauseId i) l))
            Just (Satisfied Nothing) -> loop (LSet.insert i sats) is rest
            Just (Satisfied (Just ((w :!: old) :!: (new :!: newIdx)))) -> S.do
              updateWatchLit i w old new newIdx
              loop (LSet.insert i sats) is rest
            Just (WatchChangedFromTo w old new newIdx) -> S.do
              updateWatchLit i w old new newIdx
              loop sats is rest
            Just (Unit l) -> S.do
              assertLit (toClauseId i) l
              loop (LSet.insert i sats) is (rest |> l)
    go sats Seq.Empty = S.do
      -- No literal given a priori. Find first literal.
      -- FIXME: Use heuristics for variable selection.
      (Ur resl, sats) <- S.state \(CDCLState steps clauses watches vals) ->
        LV.findWith
          ( \(vals, sats) i c ->
              LSet.member i sats & \case
                (Ur False, sats) ->
                  S.runState (findUnit c) vals & \(r, a) ->
                    (r, (a, sats))
                (Ur True, sats) -> (Ur Nothing, (vals, sats))
          )
          (vals, sats)
          clauses
          & \(ur, (vals, sats), clauses) ->
            ((ur, sats), CDCLState steps clauses watches vals)

      case resl of
        Nothing -> sats `lseq` S.pure (Ur NoMorePropagation)
        Just (WatchChangedFromTo w old new newIdx, i) -> S.do
          updateWatchLit i w old new newIdx
          go sats Seq.Empty
        Just (Satisfied Nothing, i) -> go (LSet.insert i sats) Seq.Empty
        Just (Satisfied (Just ((w :!: old) :!: (new :!: newIdx))), i) -> S.do
          updateWatchLit i w old new newIdx
          go (LSet.insert i sats) Seq.Empty
        Just (Conflict ml, i) ->
          sats `lseq` S.pure (Ur (ConflictFound (toClauseId i) ml))
        Just (Unit l, i) -> S.do
          assertLit (toClauseId i) l
          go (LSet.insert i sats) (Seq.singleton l)

updateWatchLit :: Int -> WatchVar -> VarId -> VarId -> Index -> S.State CDCLState ()
updateWatchLit cid w old new vid = S.do
  S.zoom clausesL $ S.modify $ LV.modify_ (watchVarL w .~ vid) cid
  S.zoom watchesL
    $ S.modify
    $ LHM.alter (fmap $ IS.delete cid) old
    PL.. LHM.alter (fmap $ IS.insert cid) new

assertLit :: ClauseId -> Lit -> S.State CDCLState ()
assertLit (Just -> antecedent) lit = S.do
  Ur (decideLevel :!: decisionStep) <- S.zoom stepsL S.do
    Ur len <- S.state LUV.size
    let curStp = len - 1
    S.state $ LUV.modify (\i -> (i + 1, fromIntegral curStp :!: i)) curStp
  valuationL
    S.%= LUA.set (fromEnum $ litVar lit) Definite {value = isPositive lit, ..}

-- | Propagate Literal.
propLit :: Lit -> Clause -> S.State Valuation (Ur (Maybe UnitResult))
propLit trueLit c@Clause {..} =
  let l = U.unsafeIndex lits watched1
   in if litVar l == litVar trueLit
        then -- Have the same variable as watched var #1

          if l == trueLit
            then S.pure $ Ur $ Just $ Satisfied Nothing -- Satisfied.
            else findNextAvailable W1 c -- False. Find next watched lit.
        else -- Otherwise it must be watched var #2

          if U.unsafeIndex lits watched2 == trueLit
            then S.pure $ Ur $ Just $ Satisfied Nothing -- Satisfied
            else findNextAvailable W2 c -- False. Find next watched lit.

findUnit ::
  Clause ->
  S.State Valuation (Ur (Maybe UnitResult))
findUnit c@Clause {..}
  | watched2 < 0 = S.do
      -- Only the first literal is active.
      let l = U.unsafeIndex lits watched1
      mres <- evalLit l
      S.pure case mres of
        Just False -> Ur $ Just (Conflict l)
        Just True -> Ur $ Just $ Satisfied Nothing
        Nothing -> Ur $ Just (Unit l)
  | otherwise = S.do
      -- The clause has more than two literals.
      let l1 = U.unsafeIndex lits watched1
          l2 = U.unsafeIndex lits watched2
      mres <- evalLit l1
      case mres of
        Just True ->
          -- satisfied; nothing to do.
          S.pure $ Ur $ Just $ Satisfied Nothing
        Just False ->
          -- Unsatisfiable literal: find next available literal for watched1
          findNextAvailable W1 c
        Nothing -> S.do
          -- Undetermined. Check for watched2
          mres' <- evalLit l2
          case mres' of
            Just True ->
              -- satisfied; nothing to do.
              S.pure (Ur (Just $ Satisfied Nothing))
            Just False ->
              -- Unsatisfiable literal: find next available literal for watched2
              findNextAvailable W2 c
            Nothing ->
              -- No literal changed.
              S.pure (Ur Nothing)

getWatchedLit :: WatchVar -> Clause -> Lit
getWatchedLit W1 Clause {..} = U.unsafeIndex lits watched1
getWatchedLit W2 Clause {..} = U.unsafeIndex lits watched2

findNextAvailable :: WatchVar -> Clause -> S.State Valuation (Ur (Maybe UnitResult))
findNextAvailable w c@Clause {..} = S.do
  let lit = getWatchedLit w c
      origVar = litVar lit
  Ur cands <- S.state \vals ->
    unsafeMapMaybeL
      vals
      (P.curry P.. unassigned watched1 watched2)
      lits

  let (mSat, mUndet) =
        L.foldOver
          (Lens.foldring U.foldr)
          ( (,)
              <$> (fmap fst <$> L.find ((== AssignedTrue) P.. P.snd))
              <*> (fmap fst <$> L.find ((== Unassigned) P.. P.snd))
          )
          cands
  case mSat of
    Just i ->
      let v' = litVar $ U.unsafeIndex lits i
       in S.pure (Ur (Just (Satisfied $ Just $ (w :!: origVar) :!: (v' :!: i))))
    Nothing -> case mUndet of
      Just i ->
        let v' = litVar $ U.unsafeIndex lits i
         in S.pure (Ur (Just $ WatchChangedFromTo w origVar v' i))
      Nothing -> S.pure (Ur (Just $ Conflict lit))

unassigned :: Index -> Index -> Valuation -> (Int, Lit) -> Maybe AssignmentState
unassigned exc1 exc2 vals (cur, l)
  | cur == exc1 || cur == exc2 = Nothing
  | otherwise =
      S.runState (evalLit l) vals & \case
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

evalLit :: Lit -> S.State Valuation (Maybe Bool)
evalLit l = S.do
  Ur m <- S.state $ LUA.unsafeGet (fromEnum $ litVar l)
  S.pure case m of
    Definite {..} ->
      Just
        $ if Lens.is _PosL l
          then value
          else not value
    Indefinite -> Nothing
