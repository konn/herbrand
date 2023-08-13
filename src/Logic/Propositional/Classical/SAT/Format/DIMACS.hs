{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Logic.Propositional.Classical.SAT.Format.DIMACS (
  -- * Basic Types
  DIMACS (..),
  ToDIMACS (..),
  Preamble (..),
  Problem (..),
  CNFSetting (..),
  SATSetting (..),

  -- * Formatters
  formatDIMACS,

  -- * Parsers
  parseDIMACS,
  parseDIMACSLazy,

  -- ** Parsers
  dimacsP,
  preambleP,
  problemP,

  -- ** CNF
  cnfBodyP,
  clauseP,

  -- ** SAT
  formulaP,

  -- ** Helper parsers
  litP,
  varP,
) where

import Control.Applicative
import Control.Arrow ((>>>))
import Control.DeepSeq (NFData)
import qualified Control.Foldl as L
import Control.Lens (Prism', (^?))
import Control.Monad (replicateM, when)
import Control.Monad.Trans.State.Strict (evalState, get, put)
import Data.Attoparsec.ByteString.Char8 (Parser)
import qualified Data.Attoparsec.ByteString.Char8 as Atto
import qualified Data.Attoparsec.ByteString.Lazy as AttoL
import qualified Data.Attoparsec.Combinator as Atto
import qualified Data.ByteString.Builder as BB
import qualified Data.ByteString.Char8 as BS8
import qualified Data.ByteString.Lazy.Char8 as LBS8
import Data.FMList (FMList)
import qualified Data.FMList as FML
import Data.Foldable1 (foldl1')
import Data.Functor.Foldable
import Data.Functor.Foldable.TH
import Data.Hashable (Hashable)
import qualified Data.List.NonEmpty as NE
import GHC.Generics
import Logic.Propositional.Syntax.General
import Logic.Propositional.Syntax.NormalForm.Classical.Conjunctive

data Preamble = Preamble
  { comment :: {-# UNPACK #-} !BS8.ByteString
  , problem :: {-# UNPACK #-} !Problem
  }
  deriving (Show, Eq, Ord, Generic)
  deriving anyclass (NFData, Hashable)

data Problem
  = CNFProblem {-# UNPACK #-} !CNFSetting
  | SATProblem {-# UNPACK #-} !SATSetting
  deriving (Show, Eq, Ord, Generic)
  deriving anyclass (NFData, Hashable)

data CNFSetting = CNFSetting
  { variables :: {-# UNPACK #-} !Word
  , clauses :: {-# UNPACK #-} !Word
  }
  deriving (Show, Eq, Ord, Generic)
  deriving anyclass (NFData, Hashable)

newtype SATSetting = SATSetting {variables :: Word}
  deriving (Show, Eq, Ord, Generic)
  deriving anyclass (NFData, Hashable)

data DIMACS
  = DIMACS_CNF
      {-# UNPACK #-} !BS8.ByteString
      {-# UNPACK #-} !CNFSetting
      {-# UNPACK #-} !(CNF Word)
  | DIMACS_SAT
      {-# UNPACK #-} !BS8.ByteString
      {-# UNPACK #-} !SATSetting
      {-# UNPACK #-} !(Formula Full Word)
  deriving (Show, Eq, Ord, Generic)
  deriving anyclass (NFData, Hashable)

data FactoredFormula
  = Disj (FMList FactoredFormula)
  | Conj (FMList FactoredFormula)
  | Neg FactoredFormula
  | Plain (Literal Word)
  deriving (Generic)

makeBaseFunctor ''FactoredFormula

class ToDIMACS a where
  toDIMACS :: a -> DIMACS

instance ToDIMACS DIMACS where
  toDIMACS = id

instance ToDIMACS (Formula Full Word) where
  toDIMACS f =
    let mminMax = uncurry (liftA2 (,)) $ L.fold ((,) <$> L.minimum <*> L.maximum) f
     in case mminMax of
          Nothing -> DIMACS_SAT "Herbrand: no variables" SATSetting {variables = 0} f
          Just (!mn, !mx) ->
            let (variables, shift)
                  | mn > 0 = (mx, mn)
                  | otherwise =
                      ( fromIntegral $ abs @Int (fromIntegral mn - 1)
                      , shift + mx
                      )
             in DIMACS_SAT "Herbrand" SATSetting {..} $ (+ shift) <$> f

instance ToDIMACS (CNF Word) where
  toDIMACS f =
    let mminMax = uncurry (liftA2 (,)) $ L.fold ((,) <$> L.minimum <*> L.maximum) f
        clauses = L.fold L.genericLength $ cnfClauses f
     in case mminMax of
          Nothing -> DIMACS_CNF "Herbrand: no variables" CNFSetting {variables = 0, ..} f
          Just (!mn, !mx) ->
            let (variables, shift)
                  | mn > 0 = (mx, mn)
                  | otherwise =
                      ( fromIntegral $ abs @Int (fromIntegral mn - 1)
                      , shift + mx
                      )
             in DIMACS_CNF "Herbrand" CNFSetting {..} $ (+ shift) <$> f

formatDIMACS :: DIMACS -> BB.Builder
formatDIMACS (DIMACS_CNF cmt CNFSetting {..} (CNF cls)) =
  formatComment cmt
    <> ("p " <> BB.wordDec variables <> " " <> BB.wordDec clauses <> "\n")
    <> foldMap
      ( \(CNFClause lits) ->
          foldMap
            ( \case
                Positive w -> BB.wordDec w <> " "
                Negative w -> "-" <> BB.wordDec w <> " "
            )
            lits
            <> "0\n"
      )
      cls
formatDIMACS (DIMACS_SAT cmt SATSetting {..} fml) =
  formatComment cmt
    <> ("p " <> BB.wordDec variables <> "\n")
    <> refold formatFactored factorFormula fml
    <> "\n"

formatFactored :: FactoredFormulaF BB.Builder -> BB.Builder
formatFactored = \case
  PlainF (Positive w) -> BB.wordDec w
  PlainF (Negative w) -> BB.char8 '-' <> BB.wordDec w
  NegF i -> "-(" <> i <> ")"
  ConjF ns -> "*(" <> seps ns <> ")"
  DisjF ns -> "+(" <> seps ns <> ")"

seps :: FMList BB.Builder -> BB.Builder
seps =
  flip evalState True . FML.foldMapA \w -> do
    !isHead <- get
    if isHead then w <$ put False else pure $ " " <> w

factorFormula :: (XNot n ~ NoExtField) => Formula n Word -> FactoredFormulaF (Formula n Word)
factorFormula = \case
  Atom l -> PlainF (Positive l)
  Not _ (Atom l) -> PlainF (Negative l)
  Not _ l -> NegF l
  Bot {} -> DisjF mempty
  Top {} -> ConjF mempty
  Impl _ l r -> DisjF $ Not NoExtField l `FML.cons` factor (.:\/) r
  l :/\ r -> ConjF $ factor (.:/\) l <> factor (.:/\) r
  l :\/ r -> DisjF $ factor (.:\/) l <> factor (.:\/) r

factor ::
  (forall x. Prism' (FormulaF n e x) (x, x)) ->
  Formula n e ->
  FMList (Formula n e)
factor p = para $ \e -> case e ^? p of
  Nothing -> FML.singleton $ embed $ fst <$> e
  Just ((_, l), (_, r)) -> l <> r

formatComment :: BS8.ByteString -> BB.Builder
formatComment =
  BS8.lines
    >>> foldMap ((<> BB.char8 '\n') . ("c " <>) . BB.byteString)

parseDIMACS :: BS8.ByteString -> Either String DIMACS
parseDIMACS = Atto.parseOnly (Atto.skipSpace *> dimacsP)

parseDIMACSLazy :: LBS8.ByteString -> Either String DIMACS
parseDIMACSLazy = AttoL.parseOnly (Atto.skipSpace *> dimacsP)

dimacsP :: Parser DIMACS
dimacsP = do
  Preamble {..} <- preambleP
  case problem of
    SATProblem sat -> DIMACS_SAT comment sat <$> formulaP sat
    CNFProblem cnf -> DIMACS_CNF comment cnf <$> cnfBodyP cnf

parens :: Parser a -> Parser a
parens p = symbol "(" *> p <* ")"

formulaP :: SATSetting -> Parser (Formula Full Word)
formulaP SATSetting {..} = go
  where
    go =
      (Atom <$> varP variables)
        <|> (Not NoExtField <$ symbol "-" <*> go)
        <|> (ands <$ symbol "*" <*> parens (many go))
        <|> (ors <$ symbol "+" <*> parens (many go))
        <|> parens go

ands :: [Formula Full Word] -> Formula Full Word
ands = maybe (Top NoExtField) (foldl1' (:/\)) . NE.nonEmpty

ors :: [Formula Full Word] -> Formula Full Word
ors = maybe (Bot NoExtField) (foldl1' (:\/)) . NE.nonEmpty

preambleP :: Parser Preamble
preambleP =
  Preamble . BS8.unlines <$> many commentP <*> problemP

commentP :: Parser BS8.ByteString
commentP =
  Atto.char 'c'
    *> many (Atto.satisfy (\c -> c == ' ' || c == '\t'))
    *> Atto.takeWhile (/= '\n')
    <* Atto.char '\n'

lexeme :: Parser a -> Parser a
lexeme p = p <* Atto.skipSpace

symbol :: BS8.ByteString -> Parser BS8.ByteString
symbol = lexeme . Atto.string

number :: Parser Word
number = lexeme Atto.decimal

litP :: Word -> Parser (Literal Word)
litP vs = Negative <$ symbol "-" <*> varP vs <|> Positive <$> varP vs

cnfBodyP :: CNFSetting -> Parser (CNF Word)
cnfBodyP sett@CNFSetting {..} =
  CNF <$> replicateM (fromIntegral clauses) (clauseP sett)

varP :: Word -> Parser Word
varP i = do
  n <- number
  when (n < 1)
    $ fail ("Variable out of bound: " <> show n <> " < 1")
  when (i < n) $ fail ("Variable out of bound: " <> show n <> " > " <> show i)
  pure n

clauseP :: CNFSetting -> Parser (CNFClause Word)
clauseP CNFSetting {..} = CNFClause <$> many (litP variables) <* terminate

terminate :: Parser ()
terminate =
  lexeme (Atto.endOfInput <|> Atto.char '0' *> notFollowedBy "digit" Atto.digit)

notFollowedBy :: (Show a) => String -> Parser a -> Parser ()
notFollowedBy cls p =
  Atto.lookAhead
    $ optional p
    >>= maybe (pure ()) (\a -> fail $ "Unexpected " <> cls <> ": " <> show a)

problemP :: Parser Problem
problemP = symbol "p" *> bodyP
  where
    bodyP = CNFProblem <$> cnfSettingP <|> SATProblem <$> satSetingP

satSetingP :: Parser SATSetting
satSetingP = SATSetting <$ symbol "sat" <*> number

cnfSettingP :: Parser CNFSetting
cnfSettingP = CNFSetting <$ symbol "cnf" <*> number <*> number
