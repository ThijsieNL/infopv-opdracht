module Verifier (analyzeProgramOld, analyzeProgram) where

import Control.Monad.IO.Class
import GCLParser.GCLDatatype
import WLP
import Z3.Monad hiding (substitute)
import Z3Utils
import DataTypes
import SymbolicExecution ( createSymbolicTree, createInitialState, isTreeInvalid, symbolicExecution)
import Control.Monad.Reader (ReaderT(runReaderT))

analyzeProgramOld :: Int -> Stmt -> IO AnalysisResult
analyzeProgramOld n stmt = do
    tree <- createSymbolicTree n stmt
    return $ if isTreeInvalid tree
      then InvalidResult tree
      else ValidResult tree

analyzeProgram :: VerifierOptions -> Program -> IO AnalysisResult
analyzeProgram opts program = do
    let initialNode = NodeData
          { nodeDepth = 1
          , nodeStmt = stmt program
          , nodeState = (createSymEnv program, LitB True)
          , nodeValidity = Valid
          }

    tree <- evalZ3 $ runReaderT (symbolicExecution initialNode) opts

    let reducedTree = pruneSkipBranches tree

    return $ if isTreeInvalid reducedTree
      then InvalidResult reducedTree
      else ValidResult reducedTree
    
-- | Prune the skip placeholder nodes from the symbolic execution tree 
pruneSkipBranches :: SymbolicTree -> SymbolicTree
pruneSkipBranches (Branch nd l r) = Branch nd (pruneSkipBranches l) (pruneSkipBranches r)
pruneSkipBranches (Sequence nd br@(Branch _ l r)) = Branch nd (pruneSkipBranches l) (pruneSkipBranches r)
pruneSkipBranches (Sequence nd st) = Sequence nd (pruneSkipBranches st)
pruneSkipBranches leaf = leaf