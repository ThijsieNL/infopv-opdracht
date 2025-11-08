module Main (main) where

import Control.Exception
import Criterion.Main
import Criterion.Main.Options (parseWith)
import DataTypes
import GCLParser.GCLDatatype
import GCLParser.Parser
import Options.Applicative
import System.Environment
import Verifier
import Criterion.Types (Config(csvFile))

-- | Command-line options for the benchmark runner
data Options = Options
  { gclFile :: FilePath,
    depths :: [Int],
    prune :: [Double],
    csv :: Maybe FilePath
  }

-- | Parser for command-line options
optsParser :: Parser Options
optsParser =
  Options
    <$> strArgument
      ( metavar "FILE"
          <> help "The GCL file to benchmark"
          <> completer (bashCompleter "file")
      )
    <*> many
      ( option
          auto
          ( short 'k'
              <> long "depth"
              <> metavar "NUM"
              <> help "The maximum program execution depth to benchmark (repeatable)"
          )
      )
    <*> many
      ( option
          auto
          ( short 'p'
              <> long "prune"
              <> metavar "NUM"
              <> help "The prune percentage for analysis (0.0-1.0, repeatable)"
          )
      )
    <*> optional
      ( strOption
          ( long "csv"
              <> metavar "FILE"
              <> help "Output results in CSV format"
              <> completer (bashCompleter "file")
          )
      )

optsInfo :: ParserInfo Options
optsInfo = info (optsParser <**> helper) (fullDesc <> progDesc "Benchmarking Bounded Model Checking for GCL Programs")

-- Our benchmark harness.
main :: IO ()
main = do
  putStrLn "GCL Verifier Benchmarking Tool"
  Options {..} <- execParser optsInfo

  putStrLn $ "Parsing file: " ++ gclFile
  parseGCLfile gclFile >>= \case
    Left err -> putStrLn $ "Error parsing GCL file: " ++ err
    Right program -> do
      prog <- evaluate program

      let depthList = if null depths then [10, 20, 50] else depths
          pruneList = if null prune then [0.0, 0.5, 1.0] else prune
          benchmarks =
            [ bgroup
                ("Benchmarking " ++ name prog)
                [ bench (label d p) $
                    whnfIO (analyzeProgram VerifierOptions {maxDepth = d, prunePercentage = p} prog)
                  | d <- depthList,
                    p <- pruneList
                ]
            ]
      let conf = defaultConfig { csvFile = csv }
      putStrLn $ "Benchmarking with depths: " ++ show depthList ++ " and prune percentages: " ++ show pruneList
      withArgs [] $ defaultMainWith conf benchmarks
  where
    label d p = "depth=" ++ show d ++ " prune=" ++ show p