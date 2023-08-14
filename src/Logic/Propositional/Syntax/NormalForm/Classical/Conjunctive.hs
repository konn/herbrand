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
  fromFormulaFast,
  fromFormulaOrd,
  fromFormulaNaive,
  WithFresh (..),
) where

import Control.Arrow ((>>>))
import Control.DeepSeq (NFData)
import Control.Lens
import Control.Monad.Trans.RWS.CPS (RWST, evalRWS, get, modify, tell)
import Control.Parallel.Strategies (evalList, rseq, using)
import Data.Coerce (coerce)
import Data.FMList qualified as FML
import Data.Foldable1 as F1
import Data.Functor.Foldable (cata)
import Data.Functor.Foldable qualified as R
import Data.Hashable (Hashable)
import Data.List.NonEmpty qualified as NE
import GHC.Exts (IsList)
import GHC.Generics (Generic, Generic1)
import Logic.Propositional.Syntax.General
import Logic.Propositional.Syntax.Transformation.Claassical (deMorgan)
import Prelude hiding (foldl1)

-- | Propositional formula in Conjunction Normal Form (__CNF__) with atomic formula @a@.
newtype CNF a = CNF {cnfClauses :: [CNFClause a]}
  deriving (Show, Eq, Ord, Generic, Generic1, Functor, Foldable, Traversable)
  deriving anyclass (Wrapped, NFData, Hashable)
  deriving newtype (IsList)

-- | Each conjunctive clause in CNF formulae, i.e. disjunction of literals.
newtype CNFClause a = CNFClause {clauseLits :: [Literal a]}
  deriving (Show, Eq, Ord, Generic, Generic1, Functor, Foldable, Traversable)
  deriving anyclass (Wrapped, NFData, Hashable)
  deriving newtype (IsList)

data WithFresh a
  = Var !a
  | Fresh {-# UNPACK #-} !Word
  deriving (Show, Eq, Ord, Generic, Generic1, Functor, Foldable, Traversable)
  deriving anyclass (Hashable, NFData)

forceSpineCNF :: forall a. CNF a -> CNF a
forceSpineCNF = flip using $ coerce $ evalList $ evalList $ rseq @(Literal a)

fromFormulaFast :: Formula x a -> CNF (WithFresh a)
fromFormulaFast =
  CNF
    . coerce
    . uncurry ((:) . pure)
    . fmap (FML.toList . fmap FML.toList)
    . (\f -> evalRWS f () 0)
    . R.cata \case
      AtomF a -> pure $ Positive (Var a)
      TopF _ -> do
        e <- newFresh
        tell $ FML.singleton $ FML.singleton e
        pure e
      BotF _ -> do
        e <- newFresh
        tell $ FML.singleton $ FML.singleton $ negLit e
        pure e
      NotF _ aSt -> do
        e <- aSt
        e' <- newFresh
        tell
          $ FML.fromList
            [ FML.fromList [e, e']
            , FML.fromList [negLit e, negLit e']
            ]
        pure e'
      ImplF _ l r -> do
        e1 <- l
        e2 <- r
        e' <- newFresh
        tell
          $ FML.fromList
            [ FML.fromList [negLit e', negLit e1, e2]
            , FML.fromList [e', e1]
            , FML.fromList [e', negLit e2]
            ]
        pure e'
      l :/\$ r -> do
        e1 <- l
        e2 <- r
        e' <- newFresh
        tell
          $ FML.fromList
            [ FML.fromList [negLit e', e1]
            , FML.fromList [negLit e', e2]
            , FML.fromList [e', negLit e1, negLit e2]
            ]
        pure e'
      l :\/$ r -> do
        e1 <- l
        e2 <- r
        e' <- newFresh
        tell
          $ FML.fromList
            [ FML.fromList [negLit e', e1, e2]
            , FML.fromList [e', negLit e1]
            , FML.fromList [e', negLit e2]
            ]
        pure e'

newFresh :: (Monad m) => RWST () w Word m (Literal (WithFresh a))
newFresh = Positive . Fresh <$> get <* modify (+ 1)

fromFormulaOrd :: (XTop x ~ XBot x) => Formula x a -> CNF a
fromFormulaOrd =
  CNF . FML.toList . fmap (CNFClause . FML.toList) . do
    deMorgan >>> cata \case
      AtomF a -> FML.singleton $ FML.singleton a
      TopF {} -> mempty
      BotF {} -> pure mempty
      l :/\$ r -> l <> r
      ls :\/$ rs ->
        -- Use distributive laws
        foldMap
          (foldMap (fmap pure . (<>)) rs)
          ls

fromFormulaNaive :: (XTop x ~ XBot x) => Formula x a -> CNF a
fromFormulaNaive =
  CNF . FML.toList . fmap (CNFClause . FML.toList) . do
    deMorgan >>> cata \case
      AtomF a -> FML.singleton $ FML.singleton a
      TopF {} -> mempty
      BotF {} -> FML.singleton mempty
      l :/\$ r -> l <> r
      ls :\/$ rs ->
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
  (XBot x ~ NoExtField, XTop x ~ NoExtField, XNot x ~ NoExtField) =>
  CNF a ->
  Formula x a
toFormula =
  maybe
    (⊤)
    ( foldl1 (/\)
        . fmap
          ( maybe
              (⊥)
              ( foldl1 (\/) . fmap \case
                  Positive a -> Atom a
                  Negative a -> neg $ Atom a
              )
              . NE.nonEmpty
              . clauseLits
          )
    )
    . NE.nonEmpty
    . cnfClauses
