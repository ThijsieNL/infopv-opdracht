module Tree where

import Data.Hashable (hash)
import Data.List (intercalate)
import qualified Data.Map as M
import GCLParser.GCLDatatype hiding (stmt)
import WLP
import Algebra

type SymEnv = M.Map String Expr

type SymbolicState = (SymEnv, Expr) -- (Environment, Path Constraint)

createInitialState :: Stmt -> SymEnv
createInitialState = foldStmt initialAlgebra
  where
    initialAlgebra :: StmtAlgebra SymEnv
    initialAlgebra =
      StmtAlgebra
        {
          onAssign = \var _ -> createVar var,
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

-- Function to update the symbolic state with a new assignment
updateStateVar :: SymbolicState -> String -> Expr -> SymbolicState
updateStateVar (env, constraint) var expr =
  let substitutedExpr = reduceExpr $ updateExprVars env expr
      env' = M.insert var substitutedExpr env
   in (env', constraint)

updateExprVars :: SymEnv -> Expr -> Expr
updateExprVars env expr = foldr (\(k, v) acc -> substitute k v acc) expr (M.toList env)

-- Function to add a new assumption to the path constraint
assumeStateVar :: SymbolicState -> Expr -> SymbolicState
assumeStateVar (env, constraint) expr =
  let newConstraint = reduceExpr $ BinopExpr And  (updateExprVars env expr) constraint
   in (env, newConstraint)

-- Symbolic execution tree node
data SymNode = SymNode
  { stmt :: Stmt, -- The statement that led to this node
    state :: SymbolicState, -- The symbolic state at this node
    depth :: Int, -- Depth in the tree
    children :: [SymNode] -- Child nodes
  }
  deriving (Show)

showSymbolicState :: SymbolicState -> String
showSymbolicState (env, constraint) = "(" ++ intercalate ", " [k ++ " -> " ++ show v | (k, v) <- M.toList env] ++ ", " ++ show constraint ++ ")"
    

-- | Convert a SymNode tree to a Mermaid state diagram
showMermaid :: SymNode -> SymEnv -> String
showMermaid root initialState =
  unlines $
    "stateDiagram-v2" : indent (origin ++ nodeLines root)
  where
    indent = map ("  " ++)
    origin = ["0 : " ++ showSymbolicState (initialState, LitB True), "0 --> " ++ show (uniqueId root) ++ ": " ++ sanitizeStmt (stmt root)]

-- Generate all node and transition lines
nodeLines :: SymNode -> [String]
nodeLines node =
  thisNode ++ concatMap nodeLines (children node) ++ transitions
  where
    label = " " ++ showSymbolicState (state node) ++ " " ++ show (depth node)

    thisNode = [show (uniqueId node) ++ " : " ++ label]

    transitions =
      [ show (uniqueId node) ++ " --> " ++ show (uniqueId c) ++ " : " ++ sanitizeStmt (stmt c)
        | c <- children node
      ]

uniqueId :: SymNode -> Int
uniqueId node =
  abs $
    hash
      ( show (stmt node),
        depth node,
        map uniqueId (children node),
        show (state node)
      )

-- Replace : with #58; to avoid Mermaid parsing issues
sanitizeStmt :: Stmt -> String
sanitizeStmt = concatMap replaceColon . show
  where
    replaceColon ':' = "#58;"
    replaceColon c = [c]

symbolicExecute :: Int -> Int -> SymNode -> SymNode
symbolicExecute n _ node | depth node > n = node {stmt = Skip } -- Stop execution when depth exceeds max depth
symbolicExecute n k node = case stmt node of
  Skip -> node -- No further execution
  Assign var expr ->
    let state' = updateStateVar (state node) var expr
     in node {state = state'}
  Assume expr -> node {state = assumeStateVar (state node) expr}
  Seq s1 s2 ->
    let n' = symbolicExecute n k node {stmt = s1}
        -- Helper function to execute s2 on the lowest children
        executeOnChildren :: SymNode -> SymNode
        executeOnChildren child@SymNode {children = []} = child {children = [symbolicExecute n k child {stmt = s2, depth = depth child + 1}]}
        executeOnChildren child = child {children = map executeOnChildren (children child)}
     in executeOnChildren n'
--   IfThenElse guard s1 Skip -> -- Special case for if-then without else
--     let trueBranch = symbolicExecute n k node {stmt = Seq (Assume guard) s1}
--         falseBranch = symbolicExecute n k node {stmt = Assume (OpNeg guard)}
--      in node {stmt = Skip, children = [trueBranch, falseBranch], depth = max (depth node - 1) 0}
  IfThenElse guard s1 s2 ->
    let trueBranch = symbolicExecute n k node {stmt = Seq (Assume guard) s1}
        falseBranch = symbolicExecute n k node {stmt = Seq (Assume (OpNeg guard)) s2}
     in node {stmt = Skip, children = [trueBranch, falseBranch], depth = max (depth node - 1) 0}
  While guard body ->
    let -- Unroll the loop up to k times
        unroll :: Int -> Stmt
        unroll 1 = IfThenElse guard body Skip
        unroll i = IfThenElse guard (Seq body (unroll (i - 1))) Skip
     in symbolicExecute n k node {stmt = unroll k}
  _ -> node -- Other statements not handled yet

-- TODO: Filter skip nodes and merge their children into the parent node