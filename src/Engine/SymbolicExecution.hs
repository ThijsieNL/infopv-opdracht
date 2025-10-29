module SymbolicExecution where

import Algebra
import Control.Monad.Reader
import qualified Data.Map as M
import DataTypes
import GCLParser.GCLDatatype
import WLP
import Z3.Monad hiding (substitute)
import Z3Utils 

-- TODO: Writer for reporting?
type SymbolicExecution = ReaderT VerifierOptions Z3

symbolicExecution :: NodeData -> SymbolicExecution SymbolicTree
symbolicExecution nd = do
  VerifierOptions {maxDepth = md} <- ask
  if nodeDepth nd >= md
    then return $ Leaf nd {nodeValidity = Infeasible "Max depth reached"}
    else case nodeStmt nd of
      Skip -> return $ Leaf nd
      Assign var expr -> return $ Leaf nd {nodeState = updateStateVar (nodeState nd) var expr}
      Assume expr -> return $ Leaf nd {nodeState = assumeStateVar (nodeState nd) expr} -- Move checking to this point
      Assert expr -> do
        (isValid', mModel) <- lift $ assertStateVar (nodeState nd) expr
        case (isValid', mModel) of
          (True, _) -> return $ Leaf nd {nodeValidity = Valid}
          (False, Just m) -> do
            modelStr <- lift $ modelToString m
            let (env, constraint) = nodeState nd
                fullExpr = BinopExpr Implication constraint (updateExprVars env expr)
            return $ Leaf nd {nodeValidity = Invalid modelStr}
          (False, Nothing) -> return $ Leaf nd {nodeValidity = Invalid "No model available"}
      Seq s1 s2 -> do
        firstNode <- symbolicExecution nd {nodeStmt = s1}
        let shouldContinue nd' =
              nodeDepth nd' < md && isValid (nodeValidity nd') && isFeasible (nodeValidity nd')

            go :: SymbolicTree -> SymbolicExecution SymbolicTree
            go (Leaf childNd)
              | shouldContinue childNd = do
                  let secondNd = childNd {nodeStmt = s2, nodeDepth = nodeDepth childNd + 1}
                  secondNode <- symbolicExecution secondNd
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

        trueSat <- lift $ exprIsSat trueCon
        falseSat <- lift $ exprIsSat falseCon

        trueBranch <-
          if trueSat
            then symbolicExecution nd {nodeStmt = Seq (Assume guard) s1}
            else symbolicExecution nd {nodeStmt = Assume guard, nodeValidity = Infeasible "Guard is not satisfiable"}

        falseBranch <-
          if falseSat
            then symbolicExecution nd {nodeStmt = Seq (Assume (OpNeg guard)) s2}
            else symbolicExecution nd {nodeStmt = Assume (OpNeg guard), nodeValidity = Infeasible "Guard is not satisfiable"}

        return $ Branch nd trueBranch falseBranch
      While guard body -> symbolicExecution nd {nodeStmt = IfThenElse guard (Seq body (While guard body)) Skip}
      _ -> error ("Statement type " ++ show (nodeStmt nd) ++ " not handled yet")

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
assertStateVar :: SymbolicState -> Expr -> Z3 (Bool, Maybe Model)
assertStateVar (env, constraint) expr = do
  let fullExpr = BinopExpr Implication constraint (updateExprVars env expr)
  exprIsValidWithModel fullExpr