module SymbolicExecution where

import Algebra
import qualified Data.Map as M
import Data.Map.Internal.Debug (node)
import DataTypes
import GCLParser.GCLDatatype
import WLP (reduceExpr, substitute)
import qualified Z3.Monad as Z3
import Z3Utils (exprIsSat, exprIsValid, exprToZ3)

-- | Create a symbolic execution tree for a given statement up to a maximum depth
createSymbolicTree :: Int -> Stmt -> IO SymbolicTree
createSymbolicTree maxDepth stmt = pruneSkipBranches <$> symbolicExecution maxDepth initialNode
  where
    initialState = createInitialState stmt
    initialNode =
      NodeData
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
symbolicExecution n nd | nodeDepth nd >= n = return $ Leaf nd {nodeFeasibility = False} -- Stop execution when depth exceeds max depth
symbolicExecution n nd = case nodeStmt nd of
  Skip -> return $ Leaf nd -- No further execution
  Assign var expr -> return $ Leaf nd {nodeState = updateStateVar (nodeState nd) var expr}
  Assume expr -> return $ Leaf nd {nodeState = assumeStateVar (nodeState nd) expr}
  Assert expr -> do
    (isValid, mModel) <- Z3.evalZ3 $ assertStateVar (nodeState nd) expr
    case (isValid, mModel) of
      (True, _) -> return $ Leaf nd {nodeValidity = Valid}
      (False, Just m) -> do
        modelStr <- Z3.evalZ3 (Z3.modelToString m)
        return $ Leaf nd {nodeValidity = Invalid modelStr}
      (False, Nothing) ->
        return $ Leaf nd {nodeValidity = Invalid "No model available"}
  Seq s1 s2 -> do
    firstNode <- symbolicExecution n nd {nodeStmt = s1}

    let shouldContinue nd' =
          nodeDepth nd' < n && isValid (nodeValidity nd') && nodeFeasibility nd'

        go :: SymbolicTree -> IO SymbolicTree
        go (Leaf childNd)
          | shouldContinue childNd = do
              let secondNd = childNd {nodeStmt = s2, nodeDepth = nodeDepth childNd + 1}
              secondNode <- symbolicExecution n secondNd
              return $ Sequence childNd secondNode
          | otherwise = return $ Leaf childNd
        go (Sequence childNd st)
          | shouldContinue childNd = Sequence childNd <$> go st
          | otherwise = return $ Sequence childNd st
        go (Branch childNd l r)
          | shouldContinue childNd = Branch childNd <$> go l <*> go r
          | otherwise = return $ Branch childNd l r

    if not (isPathFeasible firstNode)
      then return firstNode
      else go firstNode
  IfThenElse guard s1 s2 -> do
    let (env, pathConstraint) = nodeState nd
        gTrue = updateExprVars env guard
        gFalse = updateExprVars env (OpNeg guard)
        trueCon = BinopExpr And gTrue pathConstraint
        falseCon = BinopExpr And gFalse pathConstraint

    -- TODO: Use heuristics to prioritize branches
    trueSat <- Z3.evalZ3 $ exprIsSat trueCon
    falseSat <- Z3.evalZ3 $ exprIsSat falseCon

    trueBranch <-
      if trueSat
        then symbolicExecution n nd {nodeStmt = Seq (Assume guard) s1}
        else symbolicExecution n nd {nodeStmt = Assume guard, nodeFeasibility = False}

    falseBranch <-
      if falseSat
        then symbolicExecution n nd {nodeStmt = Seq (Assume (OpNeg guard)) s2}
        else symbolicExecution n nd {nodeStmt = Assume (OpNeg guard), nodeFeasibility = False}

    return $ Branch nd trueBranch falseBranch
  While guard body -> symbolicExecution n nd {nodeStmt = IfThenElse guard (Seq body (While guard body)) Skip}
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

isTreeInvalid :: SymbolicTree -> Bool
isTreeInvalid (Branch nd l r) = not (isValid (nodeValidity nd)) || isTreeInvalid l || isTreeInvalid r
isTreeInvalid (Sequence nd n) = not (isValid (nodeValidity nd)) || isTreeInvalid n
isTreeInvalid (Leaf nd) = not (isValid (nodeValidity nd))

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
assertStateVar :: SymbolicState -> Expr -> Z3.Z3 (Bool, Maybe Z3.Model)
assertStateVar (env, constraint) expr = do
  let fullExpr = BinopExpr Implication (updateExprVars env expr) constraint
  exprIsValid fullExpr