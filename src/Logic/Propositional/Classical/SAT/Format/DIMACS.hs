{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

module Logic.Propositional.Classical.SAT.Format.DIMACS (
  -- * Basic Types
  DIMACS (..),
  Preamble (..),
  Problem (..),
  CNFSetting (..),
  SATSetting (..),

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
import Control.DeepSeq (NFData)
import Control.Monad (replicateM, when)
import Data.Attoparsec.ByteString.Char8 (Parser)
import qualified Data.Attoparsec.ByteString.Char8 as Atto
import qualified Data.Attoparsec.ByteString.Lazy as AttoL
import qualified Data.Attoparsec.Combinator as Atto
import qualified Data.ByteString.Char8 as BS8
import qualified Data.ByteString.Lazy.Char8 as LBS8
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
ands = maybe (Top NoExtField) (foldr1 (:/\)) . NE.nonEmpty

ors :: [Formula Full Word] -> Formula Full Word
ors = maybe (Bot NoExtField) (foldr1 (:\/)) . NE.nonEmpty

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
