{-# LANGUAGE GHC2021 #-}

module Workloads (
  learnedInsertionCNF,
  propagationCNF,
) where

import Logic.Propositional.Classical.SAT.CDCL.Types (VarId)
import Logic.Propositional.Syntax.General (Literal (..))
import Logic.Propositional.Syntax.NormalForm.Classical.Conjunctive (
  CNF (..),
  CNFClause (..),
 )

propagationCNF :: CNF VarId
propagationCNF =
  CNF $
    CNFClause [Positive 0]
      : [ CNFClause [Negative variable, Positive (variable + 1)]
        | variable <- [0 .. 4094]
        ]
        <> [CNFClause [Negative 4095]]

learnedInsertionCNF :: CNF VarId
learnedInsertionCNF =
  CNF $
    [ CNFClause
        [Positive $ fromIntegral (pigeon * holes + hole) | hole <- [0 .. holes - 1]]
    | pigeon <- [0 .. pigeons - 1]
    ]
      <> [ CNFClause
             [ Negative $ fromIntegral (first * holes + hole)
             , Negative $ fromIntegral (second * holes + hole)
             ]
         | hole <- [0 .. holes - 1]
         , first <- [0 .. pigeons - 1]
         , second <- [first + 1 .. pigeons - 1]
         ]
  where
    pigeons, holes :: Int
    pigeons = 7
    holes = 6
