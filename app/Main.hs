{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

module Main (main) where

import Control.Monad
import DataTypes
import GCLParser.GCLDatatype
import GCLParser.Parser
import Mermaid
import Options.Applicative as Opt
import Verifier

data Options = Options
  { gclFile :: FilePath,
    k :: Int,
    prunePercentage :: Maybe Double,
    showTree :: Bool
  }
  deriving (Show)

opts :: Parser Options
opts =
  Options
    <$> strArgument
      ( metavar "FILE"
          <> help "The GCL file to process"
          <> completer (bashCompleter "file")
      )
    <*> option
      auto
      ( short 'k'
          <> metavar "NUM"
          <> help "The maximum program execution depth"
          <> value 10
          <> showDefault
      )
    <*> option
      auto
      ( short 'p'
          <> metavar "NUM"
          <> help "The max depth percentage on which pruning is applied (0.0-1.0)"
          <> value Nothing
          <> showDefault
      )
    <*> switch
      ( long "show-tree"
          <> help "Show the symbolic execution tree"
          <> showDefault
      )

main :: IO ()
main = do
  let optsParser = info (opts <**> helper) (fullDesc <> progDesc "Bounded Model Checking for GCL Programs")
  Options {..} <- execParser optsParser
  parseGCLfile gclFile >>= \case
    Left err -> putStrLn $ "Error parsing GCL file: " ++ err
    Right program -> do
      let programStmt = stmt program
      putStrLn "\nOriginal Statement:"
      print programStmt

      putStrLn "\nAnalyzing Program with Bounded Model Checking:"
      AnalysisResult {..} <- analyzeProgram (VerifierOptions {verbose = False, maxDepth = k, prunePercentage = prunePercentage}) program

      if isValidResult
        then putStrLn "\nThe program is VALID within the given bounds."
        else putStrLn "\nThe program is INVALID within the given bounds."

      when showTree $ putStrLn $ showMermaid program symbolicTree