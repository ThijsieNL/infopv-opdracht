module Verifier (analyzeProgram) where

import GCLParser.GCLDatatype
import Z3.Monad hiding (substitute)
import DataTypes
import SymbolicExecution
import Control.Monad.Reader

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