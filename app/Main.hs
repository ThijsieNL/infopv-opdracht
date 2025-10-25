{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}
module Main (main) where

import Options.Applicative as Opt
import GCLParser.Parser
import Verifier
import GCLParser.GCLDatatype
import DataTypes
import Mermaid

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
      putStrLn "Parsed GCL Program:"
      print program

      let programStmt = stmt program
      putStrLn "\nOriginal Statement:"
      print programStmt

      putStrLn "\nAnalyzing Program with Bounded Model Checking:"
      analysisResult <- analyzeProgram n programStmt

      case analysisResult of
        ValidResult tree -> do
          putStrLn "\nSymbolic Execution Tree in Mermaid format:"
          let diagramStr = showMermaid programStmt tree
          putStrLn diagramStr

      -- putStrLn "\nDetailed Analysis of WLP Formula with Z3:"
      -- let programTree = createSymbolicTree n programStmt
      -- let diagramStr = showMermaid programTree
      -- putStrLn diagramStr

      -- putStrLn "\nPruned Symbolic Execution Tree in Mermaid format:"
      -- prunedTree <- evalZ3 $ pruneSymbolicTree programTree
      -- let prunedDiagramStr = showMermaid prunedTree
      -- putStrLn prunedDiagramStr

      {-
      TODO: turn the last assert to assert implies the symbolic state, If that holds, then the path is valid, we skip the WLP calculation.
      Check invalid paths, and track those that lead to assertion failures.
      -}