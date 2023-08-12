module Logic.Propositional.Classical.SAT.DPLLSpec (test_solve) where

import Logic.Propositional.Classical.SAT.DPLL
import Logic.Propositional.Classical.Syntax.TestUtils
import Logic.Propositional.Syntax.NormalForm.Classical.Conjunctive
import Test.Tasty

test_solve :: TestTree
test_solve =
  testGroup
    "solve"
    [ testGroup
        "solve . fromWithFree . fromFormulaFast"
        [ testSolverSemanticsWith projVar 10 128
            $ solve
            . fmap fromWithFree
            . fromFormulaFast
        ]
    ]

projVar :: Int -> Maybe Int
projVar i
  | even i = Just $ i `quot` 2
  | otherwise = Nothing

fromWithFree :: WithFresh Int -> Int
fromWithFree (Var i) = 2 * i
fromWithFree (Fresh i) = 2 * fromIntegral i + 1
