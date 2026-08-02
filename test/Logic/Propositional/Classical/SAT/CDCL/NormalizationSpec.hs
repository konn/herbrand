{- | Differential tests for CDCL clause normalization.

The acceptance benchmark corpus contains no duplicate clauses, no repeated
literals and no tautologies, so it cannot distinguish one deduplication from
another.  These tests are therefore the correctness gate for any change to
'prepareCDCL''s normalization, and they assert /ordered/ list equality against a
reference implementation — not set equality — because the retained order selects
each clause's watched pair and fixes both BCP order and clause identity.
-}
module Logic.Propositional.Classical.SAT.CDCL.NormalizationSpec (
  test_matchesReference,
  test_shapes,
  test_generatorCoverage,
) where

import Data.List (nub)
import Logic.Propositional.Classical.SAT.CDCL (normalizedClausesForTest)
import Logic.Propositional.Classical.SAT.CDCL.Types (Lit, VarId (..), encodeLit, fromVarId)
import Logic.Propositional.Syntax.General
import Logic.Propositional.Syntax.NormalForm.Classical.Conjunctive
import qualified Test.Falsify.Generator as F
import Test.Falsify.Predicate ((.$))
import qualified Test.Falsify.Predicate as P
import qualified Test.Falsify.Range as R
import Test.Tasty
import Test.Tasty.Falsify
import Test.Tasty.HUnit (testCase, (@?=))

{- | The reference normalization: exactly the expression the port used before
the fold swap, kept verbatim so that a test written after the change cannot
mirror the new implementation and confirm itself.
-}
reference :: CNF VarId -> Maybe (Int, Int, [[Lit]])
reference (CNF rawClauses)
  | null rawClauses = Nothing
  | any (null . clauseLits) rawClauses = Nothing
  | otherwise =
      Just
        ( maximum (map (fromVarId . literalVariable) (concatMap clauseLits rawClauses)) + 1
        , length normalized
        , normalized
        )
  where
    normalized = nub (map (nub . map encodeLit . clauseLits) rawClauses)

literalVariable :: Literal VarId -> VarId
literalVariable (Positive variable) = variable
literalVariable (Negative variable) = variable

-- | A small arity makes duplicate clauses and post-inner-nub collisions common.
literalGen :: Word -> Gen (Literal VarId)
literalGen arity =
  F.choose
    (Positive . VarId <$> variable)
    (Negative . VarId <$> variable)
  where
    variable = fromIntegral <$> F.int (R.between (0, fromIntegral arity - 1))

clauseGen :: Word -> Gen (CNFClause VarId)
clauseGen arity =
  CNFClause <$> F.list (R.between (1, 4)) (literalGen arity)

{- | Generates CNFs biased toward the shapes that discriminate one nub from
another: interleaved duplicate clauses, repeated literals after a first
occurrence, tautologies, and permuted duplicates.
-}
normalizationGen :: Gen (CNF VarId)
normalizationGen = do
  arity <- fromIntegral <$> F.int (R.between (1, 3))
  base <- F.list (R.between (1, 6)) (clauseGen arity)
  extras <- traverse (injections arity) base
  pure (CNF (interleave base (concat extras)))

-- | Zip two lists so duplicates land interleaved rather than adjacent.
interleave :: [a] -> [a] -> [a]
interleave [] ys = ys
interleave xs [] = xs
interleave (x : xs) (y : ys) = x : y : interleave xs ys

{- | The duplicate is emitted unconditionally, so every generated CNF contains
at least one duplicate clause and 'test_generatorCoverage' holds by
construction rather than by luck. Making it conditional left the coverage
assertion true only most of the time -- falsify found
@[[0],[0, -0]]@, a CNF with no duplicate clause and no repeated literal, on
which the differential assertion is vacuous because normalization is the
identity. The remaining injections stay random so the other shapes vary.
-}
injections :: Word -> CNFClause VarId -> Gen [CNFClause VarId]
injections arity clause@(CNFClause lits) = do
  repeated <- F.bool False
  tautology <- F.bool False
  permuted <- F.bool False
  extra <- literalGen arity
  pure $
    concat
      [ [clause]
      , -- A repeated literal appended *after* its own existing occurrence.
        -- Prepending would leave first-occurrence order unchanged and so would
        -- not discriminate first- from last-occurrence retention.
        case reverse lits of
          final : _ | repeated -> [CNFClause (lits <> [final])]
          _ -> []
      , case lits of
          leading : _ | tautology -> [CNFClause (lits <> [negateLiteral leading])]
          _ -> []
      , [CNFClause (reverse lits) | permuted]
      , [CNFClause (lits <> [extra])]
      ]

negateLiteral :: Literal VarId -> Literal VarId
negateLiteral (Positive variable) = Negative variable
negateLiteral (Negative variable) = Positive variable

test_matchesReference :: TestTree
test_matchesReference =
  testProperty "normalization matches the reference, as an ordered list" $ do
    cnf@(CNF cls) <- gen normalizationGen
    let encoded = map (map encodeLit . clauseLits) cls
    collect "# of clauses" [length cls]
    collect "has duplicate clauses" [length (nub encoded) /= length encoded]
    collect
      "has a clause with repeated literals"
      [any (\c -> length (nub c) /= length c) encoded]
    assert $
      P.eq
        .$ ("reference", reference cnf)
        .$ ("normalizedClausesForTest", normalizedClausesForTest cnf)

{- | The property above reports its shape census with 'collect', which cannot
fail a test — and the suite runs with @--hide-successes@, so on a green run the
census is not even printed. That would let the property pass having never
generated a duplicate, which is precisely the blindness this module exists to
remove. Assert the census instead of reporting it.
-}
test_generatorCoverage :: TestTree
test_generatorCoverage =
  testProperty "the generator actually produces the shapes it claims" $ do
    cnf@(CNF cls) <- gen normalizationGen
    let encoded = map (map encodeLit . clauseLits) cls
        duplicateClauses = length (nub encoded) /= length encoded
        repeatedLiterals = any (\c -> length (nub c) /= length c) encoded
    collect "shape" [(duplicateClauses, repeatedLiterals)]
    -- Every generated CNF must exercise at least one of the two dedup paths;
    -- otherwise `normalizedClausesForTest` is the identity and the differential
    -- assertion in `test_matchesReference` proves nothing about deduplication.
    assert $
      P.satisfies
        ("exercises deduplication", id)
        .$ ("duplicateClauses || repeatedLiterals", duplicateClauses || repeatedLiterals)
    assert $
      P.eq
        .$ ("reference", reference cnf)
        .$ ("normalizedClausesForTest", normalizedClausesForTest cnf)

-- | One deterministic case per discriminating shape.
test_shapes :: TestTree
test_shapes =
  testGroup
    "normalization shapes"
    [ testCase "keeps first occurrence when duplicates are interleaved" $
        clausesOf [[p 0], [p 1], [p 0], [p 2]] @?= Just [[l 0], [l 1], [l 2]]
    , testCase "keeps a repeated literal's first position" $
        clausesOf [[p 0, p 1, p 0]] @?= Just [[l 0, l 1]]
    , testCase "keeps tautologies" $
        clausesOf [[p 0, n 0]] @?= Just [[l 0, ln 0]]
    , testCase "does not deduplicate permuted duplicates" $
        clausesOf [[p 0, p 1], [p 1, p 0]] @?= Just [[l 0, l 1], [l 1, l 0]]
    , testCase "deduplicates clauses that collide only after inner nub" $
        clausesOf [[p 0, p 1, p 1], [p 0, p 0, p 1]] @?= Just [[l 0, l 1]]
    , testCase "preserves unit clauses" $
        clausesOf [[p 0], [p 1]] @?= Just [[l 0], [l 1]]
    , testCase "short-circuits on an empty formula" $
        normalizedClausesForTest (CNF []) @?= Nothing
    , testCase "short-circuits on an empty clause" $
        normalizedClausesForTest (CNF [CNFClause []]) @?= Nothing
    , testCase "variable count comes from the raw clauses" $
        varsOf [[p 0], [p 0], [p 5]] @?= Just 6
    ]
  where
    p = Positive . VarId
    n = Negative . VarId
    l = encodeLit . Positive . VarId
    ln = encodeLit . Negative . VarId
    prepared = normalizedClausesForTest . CNF . map CNFClause
    clausesOf cls = (\(_, _, normalized) -> normalized) <$> prepared cls
    varsOf cls = (\(vars, _, _) -> vars) <$> prepared cls
