{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

module Main (main) where

import DataTypes
import GCLParser.GCLDatatype
import GCLParser.Parser
import Mermaid
import Options.Applicative as Opt
import Verifier (analyzeProgram)
import Control.Monad

data Options = Options
  { gclFile :: FilePath,
    k :: Int,
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
      AnalysisResult {..} <- analyzeProgram (VerifierOptions {verbose = False, maxDepth = k}) program

      if isValidResult
        then putStrLn "\nThe program is VALID within the given bounds."
        else putStrLn "\nThe program is INVALID within the given bounds."

      when showTree $ putStrLn $ showMermaid program symbolicTree