{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

module Main (main) where

import DataTypes
import GCLParser.GCLDatatype
import GCLParser.Parser
import Mermaid
import Options.Applicative as Opt
import Verifier ( analyzeProgram )

data Options = Options
  { gclFile :: FilePath,
    n :: Int
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
      ( short 'n'
          <> metavar "NUM"
          <> help "The maximum program execution depth"
          <> value 10
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
      analysisResult <- analyzeProgram (VerifierOptions {verbose = False, maxDepth = n}) program

      case analysisResult of
        ValidResult tree -> do
          putStrLn "\nSymbolic Execution Tree in Mermaid format:"
          let diagramStr = showMermaid program tree
          putStrLn diagramStr
        InvalidResult tree -> do
          putStrLn "\nSymbolic Execution Tree (with Invalid Paths) in Mermaid format:"
          let diagramStr = showMermaid program tree
          putStrLn diagramStr