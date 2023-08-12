{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Solves satisfiability with semantic Tabelaux
module Logic.Propositional.Classical.SAT.Tableaux (
  prove,
  solve,
  ProofResult (..),
) where

import Control.Applicative
import Control.Arrow ((>>>))
import qualified Control.Foldl as L
import Control.Lens (preview, (%~), (.~), (^.), _Just)
import Control.Monad (guard)
import Data.Function ((&))
import Data.Generics.Labels ()
import Data.HashSet (HashSet)
import qualified Data.HashSet as HS
import Data.Hashable
import GHC.Generics (Generic)
import Logic.Propositional.Classical.SAT.Types
import Logic.Propositional.Syntax.General

data Branch e v = Branch
  { model :: !(HashSet (Literal v))
  , branch :: ![Literal (Formula e v)]
  , stack :: ![Literal (Formula e v)]
  }
  deriving (Show, Generic)

closedWith ::
  ( Hashable v
  , Hashable (XTop e)
  , Hashable (XBot e)
  , Hashable (XNot e)
  , Hashable (XImpl e)
  ) =>
  Branch e v ->
  Literal (Formula e v) ->
  Bool
closedWith _ (Negative Top {}) = True
closedWith _ (Positive Bot {}) = True
closedWith Branch {..} (Positive (Atom a)) = Negative a `HS.member` model
closedWith Branch {..} (Negative (Atom a)) = Positive a `HS.member` model
closedWith Branch {..} fml = negLit fml `elem` branch || negLit fml `elem` stack

solve ::
  ( Hashable v
  , Hashable (XTop e)
  , Hashable (XBot e)
  , Hashable (XNot e)
  , Hashable (XImpl e)
  ) =>
  Formula e v ->
  SatResult (Model v)
solve =
  toLit >>> negLit >>> proveLit >>> \case
    Proven -> Unsat
    Refuted m -> Satisfiable m

-- | Trying to Prove formula by semantic tabelaux
prove ::
  forall e v.
  ( Hashable v
  , Hashable (XTop e)
  , Hashable (XBot e)
  , Hashable (XNot e)
  , Hashable (XImpl e)
  ) =>
  Formula e v ->
  ProofResult (Model v)
prove = proveLit . toLit

proveLit ::
  forall e v.
  ( Hashable v
  , Hashable (XTop e)
  , Hashable (XBot e)
  , Hashable (XNot e)
  , Hashable (XImpl e)
  ) =>
  Literal (Formula e v) ->
  ProofResult (Model v)
proveLit =
  maybe Proven (Refuted . toModel)
    . go
    . Branch mempty mempty
    . pure
    . negLit
  where
    go !branch = case branch ^. #stack of
      [] -> pure $ branch ^. #model
      (e : s') -> do
        guard $ not $ branch `closedWith` e
        let b' =
              branch
                & #branch %~ (e :)
                & #stack .~ s'
        case e of
          Positive Top {} -> go b'
          Positive Bot {} -> Nothing
          Positive (Atom a) -> go $ b' & #model %~ HS.insert (Positive a)
          Positive (Impl _ l r) ->
            go (b' & #stack %~ (Negative l :))
              <|> go (b' & #stack %~ (Positive r :))
          Positive (l :/\ r) ->
            go (b' & #stack %~ (Positive l :) . (Positive r :))
          Positive (l :\/ r) ->
            go (b' & #stack %~ (Positive l :)) <|> go (b' & #stack %~ (Positive r :))
          Positive (Not _ phi) ->
            go $ branch & #stack .~ (Negative phi : s')
          Negative Top {} -> Nothing
          Negative Bot {} -> go b'
          Negative (Atom a) -> go $ b' & #model %~ HS.insert (Negative a)
          Negative (Not _ phi) ->
            go $ b' & #stack %~ (Positive phi :)
          Negative (Impl _ l r) ->
            go (b' & #stack %~ (Positive l :) . (Negative r :))
          Negative (l :\/ r) ->
            go (b' & #stack %~ (Negative l :) . (Negative r :))
          Negative (l :/\ r) ->
            go (b' & #stack %~ (Negative l :))
              <|> go (b' & #stack %~ (Negative r :))

toModel :: (Hashable v) => HashSet (Literal v) -> Model v
toModel =
  L.fold
    ( do
        positive <- L.premap (preview #_Positive) $ L.handles _Just L.hashSet
        negative <- L.premap (preview #_Negative) $ L.handles _Just L.hashSet
        pure Model {..}
    )
