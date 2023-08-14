{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE NoFieldSelectors #-}
{-# OPTIONS_GHC -Wno-partial-fields #-}

module Main (main) where

import Control.Applicative ((<**>))
import Control.Lens ((^.))
import Control.Monad
import qualified Data.Aeson as A
import qualified Data.ByteString.Builder as BB
import Data.Function (fix)
import Data.Maybe (fromMaybe)
import GHC.Generics (Generic)
import Herbrand.Test
import Logic.Propositional.Classical.SAT.Format.DIMACS
import qualified Options.Applicative as Opt
import System.Directory
import System.FilePath
import Test.Falsify.Interactive (sample)
import Test.Falsify.Range (withOrigin)

data FormulaType
  = Formula
      { variables :: {-# UNPACK #-} !Word
      , size :: {-# UNPACK #-} !Word
      }
  | CNF
      { variables :: {-# UNPACK #-} !Word
      , clauses :: {-# UNPACK #-} !Word
      , maxClauseSize :: {-# UNPACK #-} !Word
      , minClauseSize :: !(Maybe Word)
      }
  deriving (Show, Eq, Ord, Generic)

data Options = Options
  { output :: !FilePath
  , name :: !(Maybe String)
  , formula :: !FormulaType
  , count :: !Word
  }
  deriving (Show, Eq, Ord, Generic)

optsP :: Opt.ParserInfo Options
optsP = Opt.info (p <**> Opt.helper) $ Opt.progDesc "Generate formula(e) of specified size in (extended) DIMACS SAT format"
  where
    p = do
      output <-
        Opt.strOption
          $ Opt.long "output"
          <> Opt.short 'o'
          <> Opt.metavar "OUT_DIR"
          <> Opt.help "Output dir"
      name <-
        Opt.optional
          $ Opt.strOption
          $ Opt.long "name"
          <> Opt.short 'N'
          <> Opt.metavar "NAME"
          <> Opt.showDefault
          <> Opt.help "Base name of output value. Each formula will be saved as `<OUT_DIR>/<NAME>-%i.sat`, where `%i` is 0-origin number. If omitted, saved as `<OUT_DIR>/%i.sat`."
      count <-
        Opt.option Opt.auto
          $ Opt.long "count"
          <> Opt.short 'n'
          <> Opt.value 1
          <> Opt.metavar "NUM"
          <> Opt.showDefault
          <> Opt.help "Number of examples to generate"
      formula <- Opt.subparser typeP
      pure Options {..}
    typeP =
      Opt.command "cnf" (Opt.info cnfP $ Opt.progDesc "Generates formula in CNF.")
        <> Opt.command "formula" (Opt.info fmlP $ Opt.progDesc "Generates formula in CNF.")
    varsP =
      Opt.option Opt.auto
        $ Opt.metavar "NUM_VARS"
        <> Opt.long "vars"
        <> Opt.short 'v'
        <> Opt.help "Number of variables (Arity)"
    cnfP = do
      variables <- varsP
      clauses <-
        Opt.option Opt.auto
          $ Opt.metavar "NUM_CLAUSES"
          <> Opt.long "size"
          <> Opt.short 's'
          <> Opt.help "Number of clauses"
      maxClauseSize <-
        Opt.option Opt.auto
          $ Opt.metavar "MAX_CLAUSES"
          <> Opt.long "max-clause"
          <> Opt.short 'C'
          <> Opt.help "Maximum size of clause"
      minClauseSize <-
        Opt.optional
          $ Opt.option Opt.auto
          $ Opt.metavar "MIN_CLAUSES"
          <> Opt.long "min-clause"
          <> Opt.short 'c'
          <> Opt.help "Minimum size of clause (default: MAX_CLAUSES / 2)"
      pure CNF {..}
    fmlP = do
      variables <- varsP
      size <-
        Opt.option Opt.auto
          $ Opt.metavar "SIZE"
          <> Opt.long "size"
          <> Opt.short 's'
          <> Opt.help "Size of a formula, i.e. # of connectives and atoms"
      pure Formula {..}

main :: IO ()
main = do
  Options {..} <- Opt.customExecParser (Opt.prefs Opt.subparserInline) optsP
  createDirectoryIfMissing True output
  ($ 0) $ fix $ \ !self !i -> unless (i > count) $ do
    dimacs <- sample
      $ case formula of
        Formula {..} -> toDIMACS <$> fullFormula variables size
        CNF {..} ->
          let !lb = fromMaybe 0 minClauseSize
              !ub = maxClauseSize
              clsSize = ((lb, ub) `withOrigin` ((lb + ub) `quot` 2))
           in toDIMACS <$> cnfGen variables clauses clsSize
    let (stat, ext) =
          case formula of
            Formula {} -> (show $ A.decode @SATStatistics $ dimacs ^. commentL, "sat")
            CNF {} -> (show $ A.decode @CNFStatistics $ dimacs ^. commentL, "cnf")
        dest = output </> maybe "" (<> "-") name <> show i <.> ext
    BB.writeFile dest $ formatDIMACS dimacs
    putStrLn $ "Written: " <> dest <> " (" <> stat <> ")"
    self $ i + 1
  pure ()
