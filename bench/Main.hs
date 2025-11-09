module Main (main) where

import Control.Exception
import Criterion.Main
import Criterion.Main.Options (parseWith)
import Criterion.Types (Config (csvFile, reportFile))
import DataTypes
import GCLParser.GCLDatatype
import GCLParser.Parser
import Options.Applicative
import System.Environment
import Verifier

-- | Command-line options for the benchmark runner
data Options = Options
  { gclFile :: FilePath,
    depths :: [Int],
    prune :: [Double],
    simplify :: Maybe Bool,
    csv :: Maybe FilePath,
    html :: Maybe FilePath
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
      ( option
          auto
          ( short 's'
              <> long "simplify"
              <> metavar "BOOL"
              <> help "Whether to simplify expressions during symbolic execution"
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
    <*> optional
      ( strOption
          ( long "html"
              <> metavar "FILE"
              <> help "Output results in HTML format"
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
          simplifyList = case simplify of
            Just b -> [b]
            Nothing -> [True, False]
          label d p s = "depth=" ++ show d ++ " prune=" ++ show p ++ " simplify=" ++ show s
          benchmarks =
            [ bgroup
                (name prog)
                [ bench (label d p s) $
                    whnfIO (analyzeProgram VerifierOptions {maxDepth = d, prunePercentage = p, simplifyExpr = s} prog)
                  | d <- depthList,
                    p <- pruneList,
                    s <- simplifyList
                ]
            ]
      let conf = defaultConfig {csvFile = csv, reportFile = html}
      putStrLn $ "Benchmarking with depths: " ++ show depthList ++ " and prune percentages: " ++ show pruneList
      withArgs [] $ defaultMainWith conf benchmarks
  where
    label d p s = "depth=" ++ show d ++ " prune=" ++ show p ++ " simplify=" ++ show s