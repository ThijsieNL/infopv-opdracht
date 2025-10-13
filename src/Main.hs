{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

module Main where

import Algebra
import Control.Monad.IO.Class
import GCLParser.GCLDatatype
import GCLParser.Parser (parseGCLfile)
import Options.Applicative hiding (str)
import Z3.Monad hiding (substitute)
import WLP
import Tree (symbolicExecute, SymNode (SymNode), showMermaid, createInitialState)
import Data.ByteString.Base64.URL (encode)
import qualified Data.ByteString.Char8 as B

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
      let initialState = createInitialState programStmt
      let programTree = symbolicExecute n k (SymNode programStmt (initialState, LitB True) 0 [])
      let diagramStr = showMermaid programTree initialState
      putStrLn diagramStr
      print programTree

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

exprToZ3 :: Expr -> Z3 AST
exprToZ3 = foldExpr exprToZ3Algebra

exprToZ3Algebra :: ExprAlgebra (Z3 AST)
exprToZ3Algebra =
  ExprAlgebra
    { onVar = \v -> do
        sym <- mkStringSymbol v
        mkIntVar sym,
      onLitI = mkInteger . toInteger,
      onLitB = mkBool,
      onLitNull = mkInteger 0, -- Represent null as 0 for simplicity
      onOpNeg = (>>= mkNot),
      onBinopExpr = \x e1 e2 -> do
        ast1 <- e1
        ast2 <- e2
        case x of
          And -> mkAnd [ast1, ast2]
          Or -> mkOr [ast1, ast2]
          Implication -> mkImplies ast1 ast2
          LessThan -> mkLt ast1 ast2
          LessThanEqual -> mkLe ast1 ast2
          GreaterThan -> mkGt ast1 ast2
          GreaterThanEqual -> mkGe ast1 ast2
          Equal -> mkEq ast1 ast2
          Minus -> mkSub [ast1, ast2]
          Plus -> mkAdd [ast1, ast2]
          Multiply -> mkMul [ast1, ast2]
          Divide -> mkDiv ast1 ast2
          Alias -> error "Alias operation not supported in Z3 translation",
      onParens = id,
      onArrayElem = undefined,
      onForall = undefined,
      onExists = undefined,
      onSizeOf = undefined,
      onRepBy = undefined,
      onCond = undefined,
      onNewStore = undefined,
      onDereference = undefined
    }