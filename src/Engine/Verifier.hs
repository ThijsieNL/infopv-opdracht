module Verifier (analyzeProgram) where

import Control.Monad.Reader
import Control.Monad.Writer
import DataTypes
import GCLParser.GCLDatatype
import SymbolicExecution
import Z3.Monad hiding (substitute)

analyzeProgram :: VerifierOptions -> Program -> IO AnalysisResult
analyzeProgram opts program = do
  let initialNode =
        NodeData
          { nodeDepth = 1,
            nodeStmt = stmt program,
            nodeState = (createSymEnv program, LitB True),
            nodeValidity = Valid
          }

  (tree, z3Invocations) <- evalZ3 (runReaderT (runWriterT (symbolicExecution initialNode)) opts)

  return $
    AnalysisResult
      { symbolicTree = tree,
        isValidResult = not $ isTreeInvalid tree,
        z3Invocations = length z3Invocations,
        formulaSize = sum z3Invocations,
        totalPaths = countTotalPaths tree,
        unfeasiblePaths = countUnfeasiblePaths tree
      }

-- | Count the total number of paths in the symbolic execution tree
countTotalPaths :: SymbolicTree -> Int
countTotalPaths (Leaf _) = 1
countTotalPaths (Branch l r) = countTotalPaths l + countTotalPaths r
countTotalPaths (Sequence _ st) = countTotalPaths st

-- | Count the number of unfeasible paths in the symbolic execution tree
countUnfeasiblePaths :: SymbolicTree -> Int
countUnfeasiblePaths (Leaf nd) = if isFeasible (nodeValidity nd) then 0 else 1
countUnfeasiblePaths (Sequence _ st) = countUnfeasiblePaths st
countUnfeasiblePaths (Branch l r) = countUnfeasiblePaths l + countUnfeasiblePaths r