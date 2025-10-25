{-# LANGUAGE LambdaCase #-}
module Main where

import Options.Applicative as Opt
import GCLParser.Parser
import Verifier (x)

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
  options <- execParser optsParser

  parseGCLfile (gclFile options) >>= \case
    Left err -> putStrLn $ "Error parsing GCL file: " ++ err
    Right file -> do
      print file
      putStrLn "Welcome to the GCL Verifier!"