{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}

module Logic.Propositional.Classical.Syntax.TestUtils (
  fullFormula,
  testProverSemantics,
  genFormula,
  testSolverSemantics,
  modelFor,
  Arity,
  Size,
  testSolverSemanticsWith,
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
import Test.Falsify.Predicate ((.$))
import qualified Test.Falsify.Predicate as P
import qualified Test.Falsify.Range as R
import Test.Tasty (TestTree, testGroup)
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

testProverSemantics ::
  Arity ->
  Size ->
  (Formula Full Int -> ProofResult (Model Int)) ->
  TestTree
testProverSemantics vs sz prove =
  testGroup
    "behaves semantically correctly"
    [ testProperty "determines provability correctly" $ do
        (phi, consis) <- genFormula vs sz
        let ans = prove phi
        case consis of
          Tautology -> assert $ P.expect Proven .$ ("answer", ans)
          _ ->
            assert
              $ P.satisfies
                ("Refuted", \case Refuted {} -> True; _ -> False)
              .$ ("answer", ans)
    , testProperty "gives a correct counterexample" $ do
        (phi, consis) <- genFormula vs sz
        let phi' = case consis of
              Tautology -> neg phi
              _ -> phi
        info $ "Refutable formula: " <> show phi'
        case prove phi' of
          Proven -> testFailed "Expected a counterexample, but got Provable"
          Refuted m -> do
            info $ "Given counterexample: " <> show m
            assert
              $ P.eq
              .$ ("expected", Just False)
              .$ ("answer", eval m phi')
    ]

testSolverSemantics ::
  Arity ->
  Size ->
  (Formula Full Int -> SatResult (Model Int)) ->
  TestTree
testSolverSemantics = testSolverSemanticsWith Just

testSolverSemanticsWith ::
  (Show v) =>
  (v -> Maybe Int) ->
  Arity ->
  Size ->
  (Formula Full Int -> SatResult (Model v)) ->
  TestTree
testSolverSemanticsWith projVar vs sz solver =
  testGroup
    "behaves sematically correctly"
    [ testProperty "Gives a correct decision" $ do
        (phi, consis) <- genFormula vs sz
        let ans = solver phi
        case consis of
          Inconsistent ->
            assert
              $ P.eq
              .$ ("expected", Unsat)
              .$ ("answer", projModel projVar <$> ans)
          _ ->
            assert
              $ P.satisfies
                ("Satisfiable", \case Satisfiable {} -> True; _ -> False)
              .$ ("answer", projModel projVar <$> ans)
    , testProperty "Gives a correct model" $ do
        (phi, consis) <- genFormula vs sz

        label
          "consistency"
          [ case consis of
              Tautology -> "Tautology"
              Consistent {} -> "Satsifiable"
              Inconsistent -> "Unsatisfiable"
          ]
        let phi' = case consis of
              Inconsistent -> neg phi
              _ -> phi
        info $ "Satsifiable Formula: " <> show phi'
        case solver phi' of
          Unsat -> testFailed "Expected Satisfiable, but got Unsat"
          Satisfiable m -> do
            info $ "Given model: " <> show m
            assert
              $ P.eq
              .$ ("expected", Just True)
              .$ ("answer", eval (projModel projVar m) phi')
    ]

cnfGen :: Arity -> Size -> Size -> Gen (CNF Int)
cnfGen ar numCls numLits =
  CNF
    <$> list
      (R.between (0, numCls))
      (CNFClause <$> list (R.between (0, numLits)) (literal ar))

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
