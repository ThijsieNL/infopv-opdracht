module DataTypes where

import qualified Data.Map as M
import GCLParser.GCLDatatype

type SymEnv = M.Map String Expr

type SymbolicState = (SymEnv, Expr) -- (Environment, Path Constraint)

data Validity = Valid | Invalid String | Infeasible String -- Valid or Invalid and Infeasible with reason
    deriving (Show, Eq)

isValid :: Validity -> Bool
isValid (Invalid _) = False
isValid _ = True

isFeasible :: Validity -> Bool
isFeasible (Infeasible _) = False
isFeasible _ = True

data NodeData = NodeData
  { nodeDepth :: Int,
    nodeStmt :: Stmt,
    nodeState :: SymbolicState,
    nodeValidity :: Validity
  }
  deriving (Show)

data AnalysisResult = ValidResult SymbolicTree | InvalidResult SymbolicTree
    deriving (Show)

data SymbolicTree = Branch NodeData SymbolicTree SymbolicTree | Sequence NodeData SymbolicTree | Leaf NodeData
    deriving (Show)

getNodeData :: SymbolicTree -> NodeData
getNodeData (Leaf nd) = nd
getNodeData (Sequence nd _) = nd
getNodeData (Branch nd _ _) = nd