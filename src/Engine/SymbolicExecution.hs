module SymbolicExecution where

import Control.Monad.Reader
import Control.Monad.Writer
import qualified Data.Map as M
import DataTypes
import GCLParser.GCLDatatype
import WLP
import Z3.Monad
import Z3Utils

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
      Assume expr -> Leaf <$> assumeStateVar nd expr
      Assert expr -> Leaf <$> assertStateVar nd expr
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
            go (Branch l r) = Branch <$> go l <*> go r

        if not (isTreeFeasible firstNode)
          then return firstNode
          else go firstNode
      IfThenElse guard s1 s2 ->
        Branch
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
isTreeFeasible (Branch l r) = isTreeFeasible l || isTreeFeasible r
isTreeFeasible (Sequence nd n) = isFeasible (nodeValidity nd) && isTreeFeasible n
isTreeFeasible (Leaf nd) = isFeasible (nodeValidity nd)

-- | Check if the symbolic execution tree contains any invalid paths
isTreeInvalid :: SymbolicTree -> Bool
isTreeInvalid (Branch l r) = isTreeInvalid l || isTreeInvalid r
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
updateExprVars env expr = foldr (\(k, v) acc -> substituteExpr k v acc) expr (M.toList env)

-- | Function to add a new assumption to the path constraint
assumeStateVar :: NodeData -> Expr -> SymbolicExecution NodeData
assumeStateVar nd expr = do
  maxDepth <- asks maxDepth
  prunePerc <- asks prunePercentage
  simplify <- asks simplifyExpr

  let depth = nodeDepth nd
      pruneDepth = floor $ fromIntegral maxDepth * prunePerc
      (env, constraint) = nodeState nd
      constraint' = BinopExpr And constraint (updateExprVars env expr)

  if depth > pruneDepth
    then return nd {nodeState = (env, constraint')} -- Do not simplify or check satisfiability beyond prune depth
    else do
      let reducedExpr = if simplify then reduceExpr constraint' else constraint'
          nd' = nd {nodeState = (env, reducedExpr)}

      constraintSat <- exprIsSat reducedExpr
      if reducedExpr == LitB False || not constraintSat
        then return nd' {nodeValidity = Infeasible "Path constraint is unsatisfiable"}
        else return nd'

-- | Function to assert a condition in the symbolic state
assertStateVar :: NodeData -> Expr -> SymbolicExecution NodeData
assertStateVar nd expr = do
  simplify <- asks simplifyExpr
  let (env, constraint) = nodeState nd
      fullExpr = BinopExpr Implication constraint (updateExprVars env expr)
      reducedExpr = if simplify then reduceExpr fullExpr else fullExpr

  if reducedExpr == LitB True
    then return nd {nodeValidity = Valid} -- Trivially valid
    else do
      result <- exprIsValidWithModel fullExpr
      case result of
        (True, _) -> return nd {nodeValidity = Valid}
        (False, mModel) -> do
          msg <- case mModel of
            Just m -> do
              modelStr <- lift $ modelToString m
              return $ show reducedExpr ++ "<br>(" ++ modelStr ++ ")"
            Nothing -> return "No model available"
          return nd {nodeValidity = Invalid msg}