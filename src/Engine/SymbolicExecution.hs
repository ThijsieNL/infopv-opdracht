module SymbolicExecution (createSymbolicTree, createInitialState) where

import qualified Data.Map as M
import GCLParser.GCLDatatype
import DataTypes
import Algebra
import WLP (substitute, reduceExpr)
import qualified Z3.Monad as Z3
import Z3Utils (exprToZ3, exprIsSat, exprIsValid)
import Data.Map.Internal.Debug (node)

-- | Create a symbolic execution tree for a given statement up to a maximum depth
createSymbolicTree :: Int -> Stmt -> IO SymbolicTree
createSymbolicTree maxDepth stmt = pruneSkipBranches <$> symbolicExecution maxDepth initialNode
  where
    initialState = createInitialState stmt
    initialNode = NodeData
      { nodeDepth = 1,
        nodeStmt = stmt,
        nodeState = initialState,
        nodeValidity = Valid,
        nodeFeasibility = True
      }

    pruneSkipBranches :: SymbolicTree -> SymbolicTree
    pruneSkipBranches (Branch nd l r) = Branch nd (pruneSkipBranches l) (pruneSkipBranches r)
    pruneSkipBranches (Sequence nd br@(Branch _ l r)) = Branch nd (pruneSkipBranches l) (pruneSkipBranches r)
    pruneSkipBranches (Sequence nd st) = Sequence nd (pruneSkipBranches st)
    pruneSkipBranches leaf = leaf

-- | Create a symbolic execution tree for a given statement up to a maximum depth
symbolicExecution :: Int -> NodeData -> IO SymbolicTree
symbolicExecution n nd | nodeDepth nd >= n = return $ Leaf nd { nodeValidity = Invalid "Max depth reached" } -- Stop execution when depth exceeds max depth
symbolicExecution n nd = case nodeStmt nd of
    Skip -> return $ Leaf nd -- No further execution
    Assign var expr -> return $ Leaf nd { nodeState = updateStateVar (nodeState nd) var expr }
    Assume expr -> return $ Leaf nd { nodeState = assumeStateVar (nodeState nd) expr }
    Assert expr -> do
      let fullExpr = BinopExpr Implication (reduceExpr $ updateExprVars (fst $ nodeState nd) expr) (reduceExpr $ snd $ nodeState nd)
      let validityCheck = Z3.evalZ3 $ assertStateVar (nodeState nd) expr
      do
        isValid <- validityCheck
        print ("Checking assertion: " ++ show fullExpr ++ " => " ++ show isValid)
        let validity = if isValid then Valid else error "Assertion failed"
        return $ Leaf nd { nodeValidity = validity }

    Seq s1 s2 ->
      let firstNode = symbolicExecution n nd { nodeStmt = s1 }
          executeOnChildren :: SymbolicTree -> IO SymbolicTree
          executeOnChildren t = case t of
            Leaf childNd
              | nodeDepth childNd < n -> do
                  let secondNodeNd = childNd { nodeStmt = s2, nodeDepth = nodeDepth childNd + 1 }
                  secondNode <- symbolicExecution n secondNodeNd
                  return $ Sequence childNd secondNode
              | otherwise -> return $ Leaf childNd
            Sequence childNd st -> Sequence childNd <$> executeOnChildren st
            Branch childNd l r -> Branch childNd <$> executeOnChildren l <*> executeOnChildren r
        in firstNode >>= executeOnChildren
    IfThenElse guard s1 s2 ->
      let trueBranchNd = nd { nodeStmt = Seq (Assume guard) s1 }
          falseBranchNd = nd { nodeStmt = Seq (Assume (OpNeg guard)) s2 }
          trueBranch = symbolicExecution n trueBranchNd
          falseBranch = symbolicExecution n falseBranchNd
      in Branch nd { nodeStmt = Skip, nodeDepth = nodeDepth nd - 1 } <$> trueBranch <*> falseBranch -- Using Skip as placeholder
    While guard body -> symbolicExecution n nd { nodeStmt = IfThenElse guard (Seq body (While guard body)) Skip }
    _ -> error ("Statement type " ++ show (nodeStmt nd) ++ " not handled yet")

-- | Create the initial symbolic environment for a given statement
createInitialState :: Stmt -> SymbolicState
createInitialState stmt = (foldStmt initialAlgebra stmt, LitB True)
  where
    initialAlgebra :: StmtAlgebra SymEnv
    initialAlgebra =
      StmtAlgebra
        { onAssign = \var _ -> createVar var,
          onAAssign = \var _ _ -> createVar var,
          onDrefAssign = \var _ -> createVar var,
          onBlock = flip (foldr (\(VarDeclaration var _) acc -> createVar var `M.union` acc)),
          onSeq = M.union,
          onIfThenElse = \_ e1 e2 -> M.union e1 e2,
          onWhile = \_ bodyEnv -> bodyEnv,
          onSkip = M.empty,
          onAssert = const M.empty,
          onAssume = const M.empty,
          onTryCatch = \_ tryEnv catchEnv -> M.union tryEnv catchEnv
        }
    createVar var = M.insert var (Var (var ++ "0")) M.empty

isPathFeasible :: SymbolicTree -> Bool
isPathFeasible (Branch nd l r) = isValid (nodeValidity nd) && (isPathFeasible l || isPathFeasible r)
isPathFeasible (Sequence nd n) = isValid (nodeValidity nd) && isPathFeasible n
isPathFeasible (Leaf nd) = isValid (nodeValidity nd)

-- | Function to update the symbolic state with a new assignment
updateStateVar :: SymbolicState -> String -> Expr -> SymbolicState
updateStateVar (env, constraint) var expr =
  let substitutedExpr = updateExprVars env expr
      env' = M.insert var substitutedExpr env
   in (env', constraint)

-- | Function to update expressions based on the current symbolic environment
updateExprVars :: SymEnv -> Expr -> Expr
updateExprVars env expr = foldr (\(k, v) acc -> substitute k v acc) expr (M.toList env)

-- | Function to add a new assumption to the path constraint
assumeStateVar :: SymbolicState -> Expr -> SymbolicState
assumeStateVar (env, constraint) expr =
  let newConstraint = BinopExpr And (updateExprVars env expr) constraint
   in (env, newConstraint)

-- | Function to assert a condition in the symbolic state
assertStateVar :: SymbolicState -> Expr -> Z3.Z3 Bool
assertStateVar (env, constraint) expr = do
  let fullExpr = BinopExpr Implication (updateExprVars env expr) constraint
  exprIsValid fullExpr