{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE RecordWildCards #-}

-- | Solves satisfiability problem by naïve brute-force.
module Logic.Propositional.Classical.SAT.BruteForce (Consistency (..), classifyFormula) where

import Control.Arrow ((>>>))
import qualified Control.Foldl as L
import Control.Lens (folded)
import qualified Data.FMList as FML
import Data.Function ((&))
import qualified Data.HashSet as HS
import Data.Hashable
import Data.List.NonEmpty (NonEmpty)
import qualified Data.List.NonEmpty as NE
import GHC.Generics
import Logic.Propositional.Classical.SAT.Types
import Logic.Propositional.Syntax.General

data Consistency v = Tautology | Consistent (NonEmpty (Model v)) | Inconsistent
  deriving (Show, Eq, Ord, Generic)

classifyFormula :: (Hashable v) => Formula e v -> Consistency v
classifyFormula fml =
  let models = getModels fml
      (allSat, anyMod) =
        L.fold
          ( L.premap
              ((,) <$> id <*> ((== Just True) . flip eval fml))
              $ (,)
                <$> L.all snd
                <*> L.prefilter snd (L.premap fst $ NE.nonEmpty <$> L.list)
          )
          models
   in if allSat
        then Tautology
        else maybe Inconsistent Consistent anyMod

getModels :: (Hashable v) => Formula e v -> [Model v]
getModels =
  L.fold ((,) <$> L.null <*> (HS.toList <$> L.hashSet))
    >>> \(isNullary, f) ->
      if isNullary
        then [mempty]
        else
          f
            & traverse
              ( \v ->
                  [(FML.singleton v, mempty), (mempty, FML.singleton v)]
              )
            & map
              ( L.fold do
                  positive <- L.premap fst $ L.handles folded L.hashSet
                  negative <- L.premap snd $ L.handles folded L.hashSet
                  pure Model {..}
              )
