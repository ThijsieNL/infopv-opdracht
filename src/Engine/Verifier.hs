module Verifier (analyzeProgram) where

import Control.Monad.IO.Class
import GCLParser.GCLDatatype
import Tree
import WLP
import Z3.Monad hiding (substitute)
import Z3Utils
import DataTypes
import SymbolicExecution ( createSymbolicTree, createInitialState )

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


analyzeProgram :: Int -> Stmt -> IO AnalysisResult
analyzeProgram n stmt = do
    let tree = createSymbolicTree n stmt
    let initialState = createInitialState stmt
    print initialState
    return $ ValidResult tree