{-# LANGUAGE GHC2021 #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Conjunctive normal forms in classical propositional logic.
module Logic.Propositional.Syntax.NormalForm.Classical.Conjunctive (
  CNF (..),
  CNFClause (..),
  Literal (..),
  forceSpineCNF,
  toFormula,
  fromFormulaOrd,
  fromFormulaNaive,
) where

import Control.Arrow ((>>>))
import Control.DeepSeq (NFData)
import Control.Foldl qualified as L
import Control.Lens
import Control.Parallel.Strategies (evalList, rseq, using)
import Data.Coerce (coerce)
import Data.FMList qualified as FML
import Data.Foldable1 as F1
import Data.Functor.Foldable (cata)
import Data.List.NonEmpty qualified as NE
import Data.Set qualified as Set
import GHC.Exts (IsList)
import GHC.Generics (Generic, Generic1)
import Logic.Propositional.Syntax.General
import Logic.Propositional.Syntax.Transformation.Claassical (deMorgan)
import Prelude hiding (foldl1)

-- | Propositional formula in Conjunction Normal Form (__CNF__) with atomic formula @a@.
newtype CNF a = CNF {cnfClauses :: [CNFClause a]}
  deriving (Show, Eq, Ord, Generic, Generic1, Functor, Foldable, Traversable)
  deriving anyclass (Wrapped, NFData)
  deriving newtype (IsList)

-- | Each conjunctive clause in CNF formulae, i.e. disjunction of literals.
newtype CNFClause a = CNFClause {clauseLits :: [Literal a]}
  deriving (Show, Eq, Ord, Generic, Generic1, Functor, Foldable, Traversable)
  deriving anyclass (Wrapped, NFData)
  deriving newtype (IsList)

forceSpineCNF :: forall a. CNF a -> CNF a
forceSpineCNF = flip using $ coerce $ evalList $ evalList $ rseq @(Literal a)

fromFormulaOrd :: (Ord a, XTop x ~ XBot x) => Formula x a -> CNF a
fromFormulaOrd =
  CNF . fmap (CNFClause . Set.toList) . L.fold L.nub . do
    deMorgan >>> cata \case
      AtomF a -> pure $ Set.singleton a
      TopF {} -> mempty
      BotF {} -> pure mempty
      NotF c _ -> noExtCon c
      ImplF c _ _ -> noExtCon c
      l ::/\ r -> l <> r
      ls ::\/ rs ->
        -- Use distributive laws
        foldMap
          (foldMap (fmap FML.singleton . (<>)) rs)
          ls

fromFormulaNaive :: (XTop x ~ XBot x) => Formula x a -> CNF a
fromFormulaNaive =
  CNF . FML.toList . fmap (CNFClause . FML.toList) . do
    deMorgan >>> cata \case
      AtomF a -> FML.singleton $ FML.singleton a
      TopF {} -> mempty
      BotF {} -> FML.singleton mempty
      NotF c _ -> noExtCon c
      ImplF c _ _ -> noExtCon c
      l ::/\ r -> l <> r
      ls ::\/ rs ->
        -- Use distributive laws
        foldMap
          ( \l ->
              foldMap
                ( \r ->
                    FML.singleton $ l <> r
                )
                rs
          )
          ls

{-
>>> summands $ Not (Atom "a")
[Not "a"]
-}

{- Top' -> DL.singleton Top
Bot' -> DL.singleton Bot
Atom' a -> DL.singleton (Atom a) -}

{- |
Embeds CNF back into general formula.
Note that this does not do any semantic transformation except for
mapping empty CNF and empty clause to ⊤ and ⊥.
-}
toFormula ::
  (XBot x ~ NoExtField, XTop x ~ NoExtField) =>
  CNF a ->
  Formula x (Literal a)
toFormula =
  maybe
    (⊤)
    ( foldl1 (/\)
        . fmap
          ( maybe
              (⊥)
              (foldl1 (\/) . fmap Atom)
              . NE.nonEmpty
              . clauseLits
          )
    )
    . NE.nonEmpty
    . cnfClauses
