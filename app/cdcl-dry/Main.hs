{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE RecordWildCards #-}
{-# OPTIONS_GHC -finfo-table-map -fdistinct-constructor-tables #-}

module Main (main) where

import Control.Applicative ((<**>))
import Control.DeepSeq (force)
import Control.Exception (evaluate)
import Control.Lens
import Control.Monad (void)
import qualified Data.ByteString.Lazy as LBS
import Logic.Propositional.Classical.SAT.CDCL
import Logic.Propositional.Classical.SAT.Format.DIMACS (parseCNFLazy)
import qualified Options.Applicative as Opt

newtype Opt = Opt {input :: FilePath}

optP :: Opt.ParserInfo Opt
optP = Opt.info (p <**> Opt.helper) $ Opt.progDesc "Solves SAT problem on CNF formula by CDCL"
  where
    p = Opt <$> Opt.strOption (Opt.long "input" <> Opt.short 'i' <> Opt.metavar "PATH" <> Opt.help "The path to the input CNF file.")

cnf0, cnf1 :: CNF VarId
cnf0 = [[Positive 1, Negative 0, Positive 1, Positive 1, Positive 1]]
cnf1 =
  [ [Positive 1, Negative 0, Positive 1, Positive 1, Positive 1]
  , [Positive 0, Positive 0, Positive 0, Positive 0, Positive 1]
  ]

main :: IO ()
main = do
  -- Opt {..} <- Opt.execParser optP
  !cnf <- evaluate $ force cnf1
  putStrLn "CNF evaluated. Solving..."

  print $ solveVarId cnf
