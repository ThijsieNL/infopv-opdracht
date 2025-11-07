module SymbolicExecution where

import Control.Monad.RWS (MonadState (state))
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
      AAssign var e1 e2 -> do
        let repby = RepBy (Var var) e1 e2
        return $ Leaf nd {nodeState = updateStateVar (nodeState nd) ("arr_" ++ var) repby}
      Assume expr -> do
        let (env, pathConstraint) = nodeState nd
            pathConstraint' = BinopExpr And (updateExprVars env expr) pathConstraint
            depth = nodeDepth nd

        maxDepth <- asks maxDepth
        prunePerc <- asks prunePercentage
        let pruneDepth = case prunePerc of
              Just p -> floor $ fromIntegral maxDepth * p
              Nothing -> maxDepth + 1

        constraintSat <- lift $ exprIsSat pathConstraint'
        if depth <= pruneDepth && constraintSat
          then return $ Leaf nd {nodeValidity = Infeasible "Path constraint is not satisfiable"}
          else return $ Leaf nd {nodeState = assumeStateVar (nodeState nd) expr}
      Assert expr -> do
        (isValid', mModel) <- lift $ assertStateVar (nodeState nd) expr
        case (isValid', mModel) of
          (True, _) -> return $ Leaf nd {nodeValidity = Valid}
          (False, Just (e, m)) -> do
            modelStr <- lift $ modelToString m
            let (env, constraint) = nodeState nd
                fullExpr = BinopExpr Implication constraint (updateExprVars env expr)
            return $ Leaf nd {nodeValidity = Invalid $ show e ++ "<br>(" ++ modelStr ++ ")"}
          (False, Nothing) -> return $ Leaf nd {nodeValidity = Invalid " No model available"}
      Seq s1 s2 -> do
        firstNode <- symbolicExecution nd {nodeStmt = s1}

        -- If firstNode is a Block vars body, we need to remove the vars from the symbolic state before continuing
        let isBlock = case s1 of
              Block _ _ -> True
              _ -> False

        let shouldContinue nd' =
              nodeDepth nd' < md && isValid (nodeValidity nd') && isFeasible (nodeValidity nd')

            go :: SymbolicTree -> SymbolicExecution SymbolicTree
            go (Leaf childNd)
              | shouldContinue childNd = do
                  let secondState =
                        if isBlock
                          then
                            let (symEnv, pathConstraint) = nodeState childNd
                                s1Vars = case s1 of
                                  Block vars _ -> map (\(VarDeclaration v _) -> v) vars
                                  _ -> []
                                newEnv = foldr M.delete symEnv s1Vars
                             in (newEnv, pathConstraint)
                          else nodeState childNd
                  let secondNd = childNd {nodeStmt = s2, nodeDepth = nodeDepth childNd + 1, nodeState = secondState}
                  secondNode <- symbolicExecution secondNd
                  return $ Sequence childNd secondNode
              | otherwise = return $ Leaf childNd
            go (Sequence childNd st)
              | shouldContinue childNd = Sequence childNd <$> go st
              | otherwise = return $ Sequence childNd st
            go (Branch childNd l r)
              | shouldContinue childNd = Branch childNd <$> go l <*> go r
              | otherwise = return $ Branch childNd l r

        if not (isTreeFeasible firstNode)
          then return firstNode
          else go firstNode
      IfThenElse guard s1 s2 ->
        Branch nd
          <$> symbolicExecution nd {nodeStmt = Seq (Assume guard) s1}
          <*> symbolicExecution nd {nodeStmt = Seq (Assume (OpNeg guard)) s2}
      While guard body -> symbolicExecution nd {nodeStmt = IfThenElse guard (Seq body (While guard body)) Skip}
      Block vars body -> do
        let (symEnv, pathConstraint) = nodeState nd
        let symEnv' = M.union symEnv (mapVarDecls vars)
        let nd' = nd {nodeState = (symEnv', pathConstraint), nodeStmt = body}
        symbolicExecution nd'
      _ -> error ("Statement type " ++ show (nodeStmt nd) ++ " not handled yet")

-- | Check if the symbolic execution tree contains any feasible valid paths
isTreeFeasible :: SymbolicTree -> Bool
isTreeFeasible (Branch nd l r) = isValid (nodeValidity nd) && (isTreeFeasible l || isTreeFeasible r)
isTreeFeasible (Sequence nd n) = isValid (nodeValidity nd) && isTreeFeasible n
isTreeFeasible (Leaf nd) = isValid (nodeValidity nd)

-- | Check if the symbolic execution tree contains any invalid paths
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
assertStateVar :: SymbolicState -> Expr -> Z3 (Bool, Maybe (Expr, Model))
assertStateVar (env, constraint) expr = do
  let fullExpr = BinopExpr Implication constraint (updateExprVars env expr)
  result <- exprIsValidWithModel fullExpr
  case result of
    (True, _) -> return (True, Nothing)
    (False, mModel) -> return (False, fmap (\m -> (reduceExpr fullExpr, m)) mModel)