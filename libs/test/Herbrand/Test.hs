{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE TupleSections #-}

module Herbrand.Test (
  fullFormula,
  genFormula,
  modelFor,
  Arity,
  Size,
  literal,
  cnfGen,
  projModel,
) where

import qualified Control.Foldl as L
import Control.Lens (alaf, both, (%~), _Just)
import qualified Data.FMList as FML
import qualified Data.HashSet as HS
import Data.Hashable (Hashable)
import Data.Maybe
import Data.Monoid (Ap (..))
import Logic.Propositional.Classical.SAT.BruteForce
import Logic.Propositional.Classical.SAT.Types
import Logic.Propositional.Syntax.General
import Logic.Propositional.Syntax.NormalForm.Classical.Conjunctive
import Test.Falsify.Generator
import qualified Test.Falsify.Range as R
import Test.Tasty.Falsify

type Size = Word

type Arity = Word

fullFormula ::
  -- | Number of variables
  Arity ->
  -- | Size parameter
  Size ->
  Gen (Formula Full Int)
fullFormula vars = go
  where
    baseCases =
      [ (1, pure (⊥))
      , (1, pure (⊤))
      , (vars, Atom <$> int (R.between (0, fromIntegral vars - 1)))
      ]
    go !sz
      | sz <= 1 = frequency baseCases
      | otherwise =
          frequency
            $ map
              (1,)
              [ neg <$> go (sz - 1)
              , (==>) <$> go ((sz - 1) `quot` 2) <*> go ((sz - 1) `quot` 2)
              , (/\) <$> go ((sz - 1) `quot` 2) <*> go ((sz - 1) `quot` 2)
              , (\/) <$> go ((sz - 1) `quot` 2) <*> go ((sz - 1) `quot` 2)
              ]

genFormula :: Arity -> Size -> Property (Formula Full Int, Consistency Int)
genFormula varMax szMax = do
  arity <- gen $ integral $ R.between (1, varMax)

  sz <- gen $ integral $ R.between (1, szMax)

  phi <- gen $ fullFormula arity sz
  collect "size" [size phi]
  collect "arity" [HS.size $ L.fold L.hashSet phi]
  collect
    "# of maximum occurrence"
    [ L.fold
        ( L.premap (,1 :: Int)
            $ L.fold (fromMaybe 0 <$> L.maximum)
            <$> L.foldByKeyMap L.sum
        )
        phi
    ]
  let consis = classifyFormula phi
  label
    "consistency"
    [ case consis of
        Tautology -> "Tautology"
        Consistent {} -> "Satsifiable"
        Inconsistent -> "Unsatisfiable"
    ]
  pure (phi, consis)

cnfGen :: Arity -> Size -> R.Range Size -> Gen (CNF Int)
cnfGen ar numCls numLits =
  CNF
    <$> list
      (R.between (0, numCls))
      (CNFClause <$> list numLits (literal ar))

literal :: Arity -> Gen (Literal Int)
literal a = choose (Positive <$> v) (Negative <$> v)
  where
    v = int (R.between (0, fromIntegral a - 1))

projModel :: (v -> Maybe Int) -> Model v -> Model Int
projModel proj m =
  m
    { positive = L.fold (L.premap proj $ L.handles _Just L.hashSet) $ positive m
    , negative = L.fold (L.premap proj $ L.handles _Just L.hashSet) $ negative m
    }

modelFor :: (Hashable v) => HS.HashSet v -> Gen (Model v)
modelFor =
  fmap (uncurry Model . (both %~ L.fold L.hashSet))
    . alaf
      Ap
      foldMap
      ( \v ->
          choose
            (pure (FML.singleton v, mempty))
            (pure (mempty, FML.singleton v))
      )
    . HS.toList
