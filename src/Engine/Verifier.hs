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

  let reducedTree = pruneSkipBranches tree

  return $
    AnalysisResult
      { symbolicTree = reducedTree,
        isValidResult = not $ isTreeInvalid reducedTree,
        z3Invocations = length z3Invocations,
        formulaSize = sum z3Invocations,
        totalPaths = countTotalPaths reducedTree,
        unfeasiblePaths = countUnfeasiblePaths reducedTree
      }

-- | Prune the skip placeholder nodes from the symbolic execution tree
pruneSkipBranches :: SymbolicTree -> SymbolicTree
pruneSkipBranches (Branch nd l r) = Branch nd (pruneSkipBranches l) (pruneSkipBranches r)
pruneSkipBranches (Sequence nd br@(Branch _ l r)) = Branch nd (pruneSkipBranches l) (pruneSkipBranches r)
pruneSkipBranches (Sequence nd st) = Sequence nd (pruneSkipBranches st)
pruneSkipBranches leaf = leaf

-- | Count the total number of paths in the symbolic execution tree
countTotalPaths :: SymbolicTree -> Int
countTotalPaths (Leaf _) = 1
countTotalPaths (Branch _ left right) = countTotalPaths left + countTotalPaths right
countTotalPaths (Sequence _ st) = countTotalPaths st

-- | Count the number of unfeasible paths in the symbolic execution tree
countUnfeasiblePaths :: SymbolicTree -> Int
countUnfeasiblePaths (Leaf nd) = if isFeasible (nodeValidity nd) then 0 else 1
countUnfeasiblePaths (Sequence _ st) = countUnfeasiblePaths st
countUnfeasiblePaths (Branch _ left right) = countUnfeasiblePaths left + countUnfeasiblePaths right