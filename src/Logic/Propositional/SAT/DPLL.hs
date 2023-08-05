{-# LANGUAGE GHC2021 #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}

module Logic.Propositional.SAT.DPLL (
  CNF (..),
  CNFClause (..),
  Literal (..),
  neg,
  Model (..),
  oneLiteralRule,
  affirmativeNegative,
  solve,
) where

import Control.Applicative
import Control.DeepSeq
import Control.Foldl qualified as L
import Control.Lens
import Control.Monad (guard)
import Control.Monad.Trans.Maybe (MaybeT (..))
import Control.Monad.Trans.Reader (ReaderT (..))
import Control.Monad.Trans.Writer.CPS (runWriter, tell, writer)
import Data.Foldable (foldl', foldr', foldrM)
import Data.Function (fix)
import Data.Functor (($>))
import Data.Generics.Labels ()
import Data.HashSet (HashSet)
import Data.HashSet qualified as HS
import Data.Hashable (Hashable)
import Data.Strict (Pair (..))
import GHC.Generics (Generic, Generic1, Generically (..))
import Logic.Propositional.Syntax.NormalForm.Classical.Conjunctive

data Result a = Sat a | Unsat
  deriving (Show, Eq, Ord, Generic, Generic1, Functor, Foldable, Traversable)
  deriving anyclass (Hashable, NFData)

data Model a = Model {positive :: HashSet a, negative :: HashSet a}
  deriving (Show, Eq, Ord, Generic)
  deriving (Semigroup, Monoid) via Generically (Model a)

solve :: (Hashable a) => CNF a -> Result (Model a)
solve =
  uncurry ($>) . runWriter . fix \self fml -> do
    fml' <-
      fixedPointM
        ( runMaybeT
            . runReaderT
              ( ReaderT (MaybeT . writer . oneLiteralRule)
                  <|> ReaderT (MaybeT . writer . affirmativeNegative)
              )
        )
        fml
    {-
      Criteria:

        1. If the CNF doesn't have any clause, it is a tautology;
        2. If any of the clauses is empty, it is false;
        3. Otherwise, we choose an arbitrary atomic formula and do a case-analysis on it.

      We use beautiful folding to check those conditions in a one-shot.
    -}
    let (isFalse :!: mv) =
          L.fold
            ( (:!:)
                <$> L.any (null . clauseLits)
                <*> L.handles folded L.head
            )
            $ cnfClauses fml'
    case mv of
      _ | isFalse -> pure Unsat
      Nothing -> pure $ Sat ()
      Just v -> do
        let posCl = runWriter (self $ assert (Positive v) fml')
        case posCl of
          (Sat (), model) -> Sat <$> tell model
          (Unsat, _) -> self $ assert (Negative v) fml'

assert :: Literal a -> CNF a -> CNF a
assert l (CNF cs) = CNF $ CNFClause [l] : cs

fixedPointM :: (Monad m) => (a -> m (Maybe a)) -> a -> m a
fixedPointM f = fix $ \self x -> do
  maybe (pure x) self =<< f x

neg :: Literal a -> Literal a
neg (Positive a) = Negative a
neg (Negative a) = Positive a

data StrictFst a b = StrictFst !a b
  deriving (Show, Eq, Ord, Generic)

unLit :: Literal a -> a
unLit (Positive a) = a
unLit (Negative a) = a

-- | 1-Literal Rule (Unit Propagation)
oneLiteralRule :: (Hashable a) => CNF a -> (Maybe (CNF a), Model a)
oneLiteralRule (CNF cls0) =
  {-
    NOTE: We must pay attention to where to use foldr' and foldl'.
    In the construction of 'oneLit0' we use foldl' add (:), which makes
    'oneLit0' reversed (compared to occurrence in cls0).

    As we want to process first 1-literals first, we must use foldr for
    consumption; i.e in the following operations:

    1. filtering/trasforming existing clauses (i.e. generating cls')
    2. picking of appropriate literal in model generation.
  -}
  let (oneLit0, cls') =
        foldl'
          ( \(ml, rst) ls ->
              let ml' = maybe ml (: ml) do
                    [l] <- pure $ clauseLits ls
                    pure l
               in (ml', maybe id (:) (foldrM prune ls oneLit0) rst)
          )
          ([], [])
          cls0
      prune !l (CNFClause lits) = do
        guard $ l `notElem` HS.fromList lits
        pure $ CNFClause $ filter (/= neg l) lits

      ((positive :!: negative) :!: _) =
        foldr'
          ( \ !l ((accP :!: accN) :!: occ) ->
              ( case l of
                  _ | unLit l `HS.member` occ -> (accP :!: accN) :!: occ
                  Positive a -> (HS.insert a accP :!: accN) :!: HS.insert a occ
                  Negative a -> (accP :!: HS.insert a accN) :!: HS.insert a occ
              )
          )
          mempty
          oneLit0
   in (forceSpineCNF (CNF cls') <$ guard (not $ null oneLit0), Model {..})

{- |
Affirmative-Negative Rule (Pure Literal Rule):
if a literal occurs only postiviely or only negatively, we can set it to 'True' ('False', resp.).
-}
affirmativeNegative :: (Hashable a) => CNF a -> (Maybe (CNF a), Model a)
affirmativeNegative (CNF cls0) =
  let (StrictFst (poss :!: negs) rs) =
        foldr'
          ( \cls (StrictFst posNegs ans) ->
              StrictFst (posNegs <> extractPosNeg cls) $
                if HS.null $ HS.intersection pureLits $ HS.fromList $ clauseLits cls
                  then cls : ans
                  else ans
          )
          (StrictFst (HS.empty :!: HS.empty) [])
          cls0
      extractPosNeg =
        L.fold
          ( L.premap (\case Positive l -> Left l; Negative l -> Right l) $
              (:!:) <$> L.handles _Left L.hashSet <*> L.handles _Right L.hashSet
          )
          . clauseLits
      positive = poss `HS.difference` negs
      negative = negs `HS.difference` poss
      pureLits = HS.map Positive positive `HS.union` HS.map Negative negative
   in (forceSpineCNF (CNF rs) <$ guard (not $ HS.null pureLits), Model {..})
