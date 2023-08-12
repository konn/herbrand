{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE TupleSections #-}

module Logic.Propositional.Classical.Syntax.TestUtils (
  fullFormula,
) where

import Logic.Propositional.Syntax.General
import Test.Falsify.Generator
import qualified Test.Falsify.Range as R

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
      [ (1, pure $ Bot NoExtField)
      , (1, pure $ Top NoExtField)
      , (vars, Atom <$> int (R.between (0, fromIntegral vars - 1)))
      ]
    go !sz
      | sz <= 0 = frequency baseCases
      | otherwise =
          frequency $
            map
              (1,)
              [ Not NoExtField <$> go (sz - 1)
              , Impl NoExtField <$> go (sz `quot` 2) <*> go (sz `quot` 2)
              , (:/\) <$> go (sz `quot` 2) <*> go (sz `quot` 2)
              , (:\/) <$> go (sz `quot` 2) <*> go (sz `quot` 2)
              ]
