{-# LANGUAGE GHC2021 #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

-- | DPLL Algorithm, supercharged with Conflict-Driven Clause Learning (CDCL).
module Logic.Propositional.Classical.SAT.CDCL () where

import Control.Applicative
import Control.Foldl qualified as L
import Control.Lens hiding (Index, (&))
import Control.Lens qualified as Lens
import Control.Lens.Extras qualified as Lens
import Control.Monad (guard)
import Control.Monad.Trans.Maybe (MaybeT (..))
import Control.Monad.Trans.Reader (ReaderT (..))
import Control.Monad.Trans.Writer.CPS (runWriter, tell, writer)
import Control.Optics.Linear
import Data.Bifunctor.Linear qualified as BiL
import Data.Foldable (foldl', foldr', foldrM)
import Data.Function (fix)
import Data.Functor (($>))
import Data.Functor.Linear qualified as D
import Data.Generics.Labels ()
import Data.HashMap.Mutable.Linear.Extra qualified as LHM
import Data.HashSet qualified as HS
import Data.Hashable (Hashable)
import Data.Maybe (isJust)
import Data.Set.Mutable.Linear qualified as Set
import Data.Strict (Pair (..))
import Data.Unrestricted.Linear qualified as Ur
import Data.Vector.Mutable.Linear.Extra qualified as LV
import Data.Vector.Unboxed qualified as U
import GHC.Generics (Generic)
import Logic.Propositional.Classical.SAT.CDCL.Types
import Logic.Propositional.Classical.SAT.Types
import Logic.Propositional.Syntax.NormalForm.Classical.Conjunctive
import Prelude.Linear hiding (not, (&&), (/=), (<), (==), (||))
import Unsafe.Linear qualified as Unsafe
import Prelude hiding (uncurry, ($))
import Prelude qualified as P

{-
unitPropInit :: CDLLState %1 -> (CDLLState, PropResult)
unitPropInit (CDLLState steps clauses watches vals) =
  LV.findWith (uncurry findUnit) (steps, vals) clauses
    & \(m, (steps, vals), clauses) ->
      (CDLLState steps clauses watches vals, Ur.lift isJust m)
 -}

toClauseId :: Int -> ClauseId
toClauseId = fromIntegral

findUnit ::
  Valuation %1 ->
  Clause ->
  (Ur (Maybe PropResult), Valuation)
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
              findNextAvailable vals watched1 c
            (Nothing, vals) ->
              -- Undetermined. Check for watched2
              evalLit l2 vals & \case
                (Just True, vals) ->
                  -- satisfied; nothing to do.
                  (Ur (Just $ Satisfied Nothing), vals)
                (Just False, vals) ->
                  -- Unsatisfiable literal: find next available literal for watched2
                  findNextAvailable vals watched2 c
                (Nothing, vals) ->
                  -- No literal changed.
                  (Ur Nothing, vals)

findNextAvailable :: Valuation %1 -> Index -> Clause -> (Ur (Maybe PropResult), Valuation)
findNextAvailable vals origIdx Clause {..} =
  let lit = U.unsafeIndex lits origIdx
      origVar = litVar lit
   in unsafeMapMaybeL
        vals
        ( \vals i l ->
            unassigned watched1 watched2 vals (i, l)
        )
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
                   in (Ur (Just (Satisfied $ Just $ origVar :!: v')), vals)
                Nothing -> case mUndet of
                  Just i ->
                    let v' = litVar $ U.unsafeIndex lits i
                     in (Ur (Just $ WatchChangedFromTo origVar v'), vals)
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

findUVecL ::
  forall a b.
  (U.Unbox a) =>
  (b %1 -> a -> (Bool, b)) ->
  b %1 ->
  U.Vector a ->
  (Maybe a, b)
findUVecL p = go
  where
    go :: b %1 -> U.Vector a -> (Maybe a, b)
    go !b !uv
      | U.null uv = (Nothing, b)
      | otherwise =
          let a = U.unsafeHead uv
           in p b a & \case
                (True, b) -> (Just a, b)
                (False, b) -> go b (U.unsafeTail uv)

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
