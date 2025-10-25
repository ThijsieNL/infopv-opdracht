{-# LANGUAGE RecordWildCards #-}

module MainOld where

import Algebra
import Control.Monad.IO.Class
import GCLParser.GCLDatatype
import GCLParser.Parser (parseGCLfile)
import Options.Applicative hiding (str)
import Z3.Monad hiding (substitute)
import WLP
import Tree ( showMermaid, createSymbolicTree, pruneSymbolicTree )
import Data.ByteString.Base64.URL (encode)
import qualified Data.ByteString.Char8 as B
import Z3Utils (exprToZ3)

data Options = Options
  { gclFile :: FilePath,
    k :: Int,
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
      ( short 'k'
          <> metavar "NUM"
          <> help "The fixed point bound"
          <> value 3
          <> showDefault
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
main = processGCLFile =<< execParser optsParser
  where
    optsParser = info (opts <**> helper) (fullDesc <> progDesc "Bounded Model Checking for GCL Programs")

processGCLFile :: Options -> IO ()
processGCLFile Options {..} = do
  parseGCLfile gclFile >>= \case
    Left err -> putStrLn $ "Error parsing GCL file: " ++ err
    Right program -> do
      putStrLn "Parsed GCL Program:"
      print program

      let programStmt = stmt program
      putStrLn "\nOriginal Statement:"
      print programStmt


      let wlpFormula = reduceExpr $ stmtToWlp k programStmt (LitB True)
      putStrLn "\nWLP Formula:"
      print wlpFormula

      evalZ3 $ do
        ast <- exprToZ3 wlpFormula
        str <- astToString ast
        liftIO $ putStrLn ("\nZ3 AST String Representation:\n" ++ str)

      putStrLn "\nAnalyzing WLP Formula with Z3:"
      validateExpr wlpFormula >>= \case
        True -> putStrLn "The WLP formula is valid."
        False -> putStrLn "The WLP formula is not valid."

      -- let filteredStmt = transformAsserts programStmt
      -- putStrLn "\nFiltered Statement (without asserts):"
      -- print filteredStmt

      putStrLn "\nDetailed Analysis of WLP Formula with Z3:"
      let programTree = createSymbolicTree n k programStmt
      let diagramStr = showMermaid programTree
      putStrLn diagramStr


      putStrLn "\nPruned Symbolic Execution Tree in Mermaid format:"
      prunedTree <- evalZ3 $ pruneSymbolicTree programTree
      let prunedDiagramStr = showMermaid prunedTree
      putStrLn prunedDiagramStr

      {-
      TODO: turn the last assert to assert implies the symbolic state, If that holds, then the path is valid, we skip the WLP calculation.
      Check invalid paths, and track those that lead to assertion failures.
      -}


      let encoded = encode (B.pack diagramStr)
      let url = "https://mermaid.ink/img/" ++ B.unpack encoded
      putStrLn url

validateExpr :: Expr -> IO Bool
validateExpr expr = evalZ3 $ do
  z3expr <- exprToZ3 $ OpNeg expr
  assert z3expr
  res <- check
  case res of
    Sat -> return False
    Unsat -> return True
    Undef -> error "Z3 returned UNKNOWN"

analyzeExpr :: Expr -> IO ()
analyzeExpr expr = evalZ3 $ do
  z3expr <- exprToZ3 expr
  assert z3expr
  res <- check
  case res of
    Sat -> do
      (_, mModel) <- getModel
      case mModel of
        Just mdl -> do
          str <- modelToString mdl
          liftIO $ putStrLn ("SAT\n" ++ str)
        Nothing -> liftIO $ putStrLn "SAT\nNo model available."
    Unsat -> liftIO $ putStrLn "UNSAT"
    Undef -> liftIO $ putStrLn "UNKNOWN"

-- Filter out any assert statements from the program and convert assumes to asserts
transformAsserts :: Stmt -> Stmt
transformAsserts =
  foldStmt
    defaultStmtAlgebra
      { onAssert = const Skip,
        onAssume = Assert
      }
