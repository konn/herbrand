{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE RecordWildCards #-}
{-# OPTIONS_GHC -finfo-table-map -fdistinct-constructor-tables #-}

module Main (main) where

import Control.Applicative ((<**>))
import Control.DeepSeq (force)
import Control.Exception (evaluate)
import Control.Lens
import qualified Data.ByteString.Lazy as LBS
import Logic.Propositional.Classical.SAT.CDCL
import Logic.Propositional.Classical.SAT.Format.DIMACS (parseCNFLazy)
import qualified Options.Applicative as Opt

data Opt = Opt {input :: FilePath, detail :: Bool}

optP :: Opt.ParserInfo Opt
optP = Opt.info (p <**> Opt.helper) $ Opt.progDesc "Solves SAT problem on CNF formula by CDCL"
  where
    p = do
      input <- Opt.strOption (Opt.long "input" <> Opt.short 'i' <> Opt.metavar "PATH" <> Opt.help "The path to the input CNF file.")
      detail <- Opt.switch $ Opt.long "detail" <> Opt.short 'D' <> Opt.help "Shows solution"
      pure Opt {..}

cnf0, cnf1 :: CNF VarId
cnf0 = [[Positive 1, Negative 0, Positive 1, Positive 1, Positive 1]]
cnf1 =
  [ [Positive 1, Negative 0, Positive 1, Positive 1, Positive 1]
  , [Positive 0, Positive 0, Positive 0, Positive 0, Positive 1]
  ]

main :: IO ()
main = do
  Opt {..} <- Opt.execParser optP
  !cnf <- either error (evaluate . force . view _3) . parseCNFLazy =<< LBS.readFile input
  putStrLn "CNF evaluated. Solving..."

  resl <- evaluate $ force $ solve cnf
  if detail
    then print resl
    else print $ () <$ resl
