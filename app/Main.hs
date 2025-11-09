module Main (main) where

import Control.Monad
import DataTypes
import GCLParser.GCLDatatype
import GCLParser.Parser
import Mermaid
import Options.Applicative as Opt
import System.CPUTime (getCPUTime)
import Verifier

data Options = Options
  { gclFile :: FilePath,
    k :: Int,
    prunePercentage :: Double,
    simplify :: Bool,
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
          <> value 1.0
          <> showDefault
      )
    <*> option
      auto
      ( short 's'
          <> long "simplify"
          <> help "Simplify expressions during symbolic execution"
          <> value True
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
      putStrLn "Original Statement:"
      print programStmt

      putStrLn $ "Analyzing " ++ name program ++ " with max depth " ++ show k ++ " and max depth prune percentage " ++ show prunePercentage ++ "..."

      start <- getCPUTime
      AnalysisResult {..} <- analyzeProgram (VerifierOptions {maxDepth = k, prunePercentage = prunePercentage, simplifyExpr = simplify}) program
      end <- getCPUTime
      let diff = fromIntegral (end - start) / (10 ^ 9) -- milliseconds
      if isValidResult
        then putStrLn "The program is VALID within the given bounds."
        else putStrLn "The program is INVALID within the given bounds."

      putStrLn $ "Total Z3 Invocations: " ++ show z3Invocations
      putStrLn $ "Total Formula Size: " ++ show formulaSize
      putStrLn $ "Total Paths: " ++ show totalPaths
      putStrLn $ "Unfeasible Paths: " ++ show unfeasiblePaths
      putStrLn $ "Total Execution Time: " ++ show diff ++ "ms"

      when showTree $ putStrLn $ showMermaid program symbolicTree