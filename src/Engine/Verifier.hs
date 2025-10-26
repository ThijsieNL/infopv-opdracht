module Verifier (analyzeProgram) where

import Control.Monad.IO.Class
import GCLParser.GCLDatatype
import WLP
import Z3.Monad hiding (substitute)
import Z3Utils
import DataTypes
import SymbolicExecution ( createSymbolicTree, createInitialState, isTreeInvalid )

analyzeProgram :: Int -> Stmt -> IO AnalysisResult
analyzeProgram n stmt = do
    tree <- createSymbolicTree n stmt
    return $ if isTreeInvalid tree
      then InvalidResult tree
      else ValidResult tree 