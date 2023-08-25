{-# LANGUAGE GHC2021 #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Conjunctive normal forms in classical propositional logic.
module Logic.Propositional.Syntax.NormalForm.Classical.Conjunctive (
  CNF (..),
  CNFClause (..),
  Literal (..),
  forceSpineCNF,
  toFormula,
  fromFormulaFast,
  fromFormulaNaive,
  WithFresh (..),
) where

import Control.Arrow ((>>>))
import Control.DeepSeq (NFData)
import Control.Lens
import Control.Monad.Trans.RWS.CPS (RWST, evalRWS, state, tell)
import Control.Parallel.Strategies (evalList, rseq, using)
import Data.Coerce (coerce)
import Data.FMList qualified as FML
import Data.Foldable1 as F1
import Data.Functor.Foldable (cata)
import Data.Functor.Foldable qualified as R
import Data.Functor.Linear qualified as Lin
import Data.Hashable (Hashable)
import Data.List.NonEmpty qualified as NE
import Data.Monoid (Endo (..))
import Data.Semigroup.Foldable (intercalateMap1)
import Data.Unrestricted.Linear (Consumable)
import GHC.Exts (IsList)
import GHC.Generics (Generic, Generic1)
import Generics.Linear qualified as L
import Generics.Linear.TH qualified as L
import Logic.Propositional.Syntax.General
import Logic.Propositional.Syntax.Transformation.Claassical (deMorgan)
import Prelude.Linear (Dupable, Movable)
import Prelude.Linear.Generically qualified as Lin
import Prelude hiding (foldl1)

-- | Propositional formula in Conjunction Normal Form (__CNF__) with atomic formula @a@.
newtype CNF a = CNF {cnfClauses :: [CNFClause a]}
  deriving (Eq, Ord, Generic, Generic1, Functor, Foldable, Traversable)
  deriving anyclass (Wrapped, NFData, Hashable)
  deriving newtype (IsList)

instance (Show a) => Show (CNF a) where
  showsPrec _ (CNF cs) = shows cs

-- | Each conjunctive clause in CNF formulae, i.e. disjunction of literals.
newtype CNFClause a = CNFClause {clauseLits :: [Literal a]}
  deriving (Eq, Ord, Generic, Generic1, Functor, Foldable, Traversable)
  deriving anyclass (Wrapped, NFData, Hashable)
  deriving newtype (IsList)

instance (Show a) => Show (CNFClause a) where
  showsPrec _ (CNFClause []) = showString "[]"
  showsPrec _ (CNFClause (c : cs)) =
    showChar '[' . appEndo (intercalateMap1 (Endo $ showString ", ") (Endo . showsLit) $ c NE.:| cs) . showChar ']'
    where
      showsLit (Positive a) = shows a
      showsLit (Negative a) = showChar '-' . shows a

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
    . fmap (([Positive (Fresh 0)] :) . FML.toList . fmap FML.toList)
    . (\f -> evalRWS f () 1)
    . R.cata \case
      AtomF a -> pure $ Positive (Var a)
      TopF _ -> do
        pure $ Positive (Fresh 0)
      BotF _ -> do
        pure $ Negative (Fresh 0)
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
newFresh = Positive . Fresh <$> state ((,) <$> id <*> (+ 1))

fromFormulaNaive :: (XTop x ~ XBot x) => Formula x a -> CNF a
fromFormulaNaive =
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

L.deriveGenericAnd1 ''CNFClause
L.deriveGenericAnd1 ''CNF

deriving via Lin.Generically1 CNFClause instance Lin.Functor CNFClause

instance Lin.Traversable CNFClause where
  traverse = Lin.genericTraverse

deriving newtype instance
  (Consumable a) => Consumable (CNFClause a)

deriving newtype instance
  (Dupable a) => Dupable (CNFClause a)

deriving newtype instance
  (Movable a) => Movable (CNFClause a)

deriving via Lin.Generically1 CNF instance Lin.Functor CNF

instance Lin.Traversable CNF where
  traverse = Lin.genericTraverse

deriving via
  L.Generically (CNF a)
  instance
    (Consumable a) => Consumable (CNF a)

deriving via
  L.Generically (CNF a)
  instance
    (Dupable a) => Dupable (CNF a)

deriving via
  L.Generically (CNF a)
  instance
    (Movable a) => Movable (CNF a)
