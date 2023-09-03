{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -funbox-strict-fields #-}

module Parse (decodeBenchs, Benchs) where

import Control.Lens hiding ((<.>))
import Control.Monad ((<=<))
import qualified Data.Bifunctor as Bi
import qualified Data.ByteString.Lazy as LBS
import Data.Coerce (coerce)
import qualified Data.Csv as Csv
import Data.Foldable (foldMap')
import Data.Generics.Labels ()
import qualified Data.Map.Strict as Map
import Data.Semigroup (First (..))
import qualified Data.Text as T
import qualified Data.Trie.Map as Trie
import qualified Data.Trie.Map.Internal as Trie
import qualified Data.Vector as V
import Data.Vector.Internal.Check
import Types
import UnliftIO (throwString)

type Benchs = Map.Map [T.Text] (Map.Map T.Text BenchCase)

decodeBenchs :: (HasCallStack) => FilePath -> IO Benchs
decodeBenchs = fmap toBenchTree . readBenchCsv

toBenchTree :: V.Vector BenchCase -> Benchs
toBenchTree =
  coerce
    . Map.filter (not . Map.null)
    . flatKeys
    . stripCommonPrefices
    . foldMap' (Trie.singleton <$> T.splitOn "." . fullName <*> First)

readBenchCsv :: (HasCallStack) => FilePath -> IO (V.Vector BenchCase)
readBenchCsv = either throwString (pure . snd) . Csv.decodeByName <=< LBS.readFile

stripCommonPrefices :: Trie.TMap T.Text a -> Trie.TMap T.Text a
stripCommonPrefices = go
  where
    go tr@(Trie.TMap (Trie.Node Nothing dic)) =
      if Map.size dic == 1 then go $ snd $ Map.findMin dic else tr
    go tr@(Trie.TMap (Trie.Node Just {} _)) = tr

flatKeys :: (Semigroup a) => Trie.TMap T.Text a -> Map.Map [T.Text] (Map.Map T.Text a)
flatKeys = go . Trie.getNode
  where
    go tr@(Trie.Node _ chs)
      | any ((== 1) . Trie.count) chs =
          Map.singleton [] $ Map.fromListWith (<>) $ map (Bi.first $ T.intercalate ".") $ Trie.toList $ Trie.TMap tr
      | otherwise =
          ifoldMapBy
            (Map.unionWith (<>))
            Map.empty
            (Map.mapKeysMonotonic . (:))
            (go . Trie.getNode <$> chs)
