module DataTypes where

import Control.Monad.Reader
import Control.Monad.Writer
import qualified Data.Map as M
import GCLParser.GCLDatatype
import Z3.Monad

type SymbolicExecution = WriterT [Int] (ReaderT VerifierOptions Z3)

data VerifierOptions = VerifierOptions
  { maxDepth :: Int,
    prunePercentage :: Double
  }

type SymEnv = M.Map String Expr

-- | Create a symbolic environment from a program's variable declarations
createSymEnv :: Program -> SymEnv
createSymEnv program = mapVarDecls decls
  where
    decls = input program ++ output program

-- | Create a symbolic environment from a list of variable declarations
mapVarDecls :: [VarDeclaration] -> SymEnv
mapVarDecls decls = M.fromList $ concatMap createEntry decls
  where
    createEntry (VarDeclaration var (AType _)) =
      let arrVar = "arr_" ++ var
          lenVar = "len_" ++ var
       in [(arrVar, Var (arrVar ++ "0")), (lenVar, Var (lenVar ++ "0"))]
    createEntry (VarDeclaration var _) = [(var, Var (var ++ "0"))]

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

data AnalysisResult = AnalysisResult
  { symbolicTree :: SymbolicTree,
    isValidResult :: Bool,
    z3Invocations :: Int,
    formulaSize :: Int,
    totalPaths :: Int,
    unfeasiblePaths :: Int
  }
  deriving (Show)

data SymbolicTree = Branch SymbolicTree SymbolicTree | Sequence NodeData SymbolicTree | Leaf NodeData
  deriving (Show)