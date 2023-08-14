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
{-# OPTIONS_GHC -Wno-name-shadowing #-}

-- | DPLL Algorithm, supercharged with Conflict-Driven Clause Learning (CDCL).
module Logic.Propositional.Classical.SAT.CDCL () where

import Control.Applicative
import Control.Foldl qualified as L
import Control.Lens hiding (Index, (&))
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
import Prelude.Linear hiding (not, (<), (==))
import Prelude hiding (uncurry, ($))
import Prelude qualified as P

unitPropInit :: CDLLState %1 -> (CDLLState, PropResult)
unitPropInit (CDLLState steps clauses watches vals) =
  LV.findWith (uncurry findUnit) (steps, vals) clauses
    & \(m, (steps, vals), clauses) ->
      (CDLLState steps clauses watches vals, Ur.lift isJust m)

findUnit ::
  LV.Vector Step %1 ->
  Valuation %1 ->
  Int ->
  Clause ->
  (Ur (Maybe (PropResult, Clause)), (LV.Vector Step, Valuation))
findUnit steps vals i c@Clause {..}
  | watched1 < 0 =
      (Ur $ Just $ (Conflict Nothing (fromIntegral i), c), (steps, vals))
  | watched2 < 0 =
      let l = U.unsafeIndex lits watched1
       in evalLit l vals & \case
            (Just False, vals) ->
              (Ur $ Just ((Conflict (Just l) $ fromIntegral i), c), (steps, vals))
            (Just True, vals) ->
              (Ur Nothing, (steps, vals))
            (Nothing, vals) ->
              (Ur $ Just ((Unit l (fromIntegral i)), c), (steps, vals))
  | otherwise =
      let !l1 = U.unsafeIndex lits watched1
          !l2 = U.unsafeIndex lits watched2
       in evalLit l1 vals & \case
            (Just True, vals) -> (Ur Nothing, (steps, vals))
            (Just False, vals) ->
              LHM.backpermute lits vals & \(vs, vals) ->
                case U.findIndex _ (U.indexed vals) of
                  Nothing -> (Ur (Just (Unit l2 (fromIntegral i)), c), (steps, vals))
                  Just i -> (Ur (Just (Nothing,)))
            (Nothing, vals) ->
              evalLit l2 vals & \case
                (Just True, vals) -> (Ur (Nothing, c), (steps, vals))
                (Nothing, vals) -> (Ur (Nothing, c), (steps, vals))
                (Just False, vals) ->
                  findUVecL (unassigned watched1) vals (U.indexed lits) & \case
                    (Ur Nothing, vals) ->
                      ( Ur (Just (Unit l1 (fromIntegral i)), c)
                      , (steps, vals)
                      )
                    (Ur (Just (i, _)), vals) ->
                      ( Ur (Nothing, c {watched2 = i})
                      , (steps, vals)
                      )

unassigned :: Index -> Valuation %1 -> (Int, Lit) -> (Bool, Valuation)
unassigned exclude vals (cur, l)
  | cur == exclude = (False, vals)
  | otherwise =
      evalLit l vals & \case
        (Nothing, vals) -> (True, vals)
        (Just {}, vals) -> (False, vals)

findUVecL ::
  forall a b.
  (U.Unbox a) =>
  (b %1 -> a -> (Bool, b)) ->
  b %1 ->
  U.Vector a ->
  (Ur (Maybe a), b)
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
