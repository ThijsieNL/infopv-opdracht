module Tree where

import Data.Hashable (hash)
import Data.List (intercalate)
import qualified Data.Map as M
import GCLParser.GCLDatatype hiding (stmt)
import WLP

type SymEnv = M.Map String Expr

type SymbolicState = (SymEnv, Expr) -- (Environment, Path Constraint)

-- Function to create an initial symbolic state
initialState :: SymEnv
initialState = M.empty

-- Function to update the symbolic state with a new assignment
updateStateVar :: SymbolicState -> String -> Expr -> SymbolicState
updateStateVar (env, constraint) var expr =
  let oldExpr = M.findWithDefault (Var var) var env
      substitutedExpr = reduceExpr $ substitute var expr oldExpr
      env' = M.insert var substitutedExpr env
   in (env', constraint)

-- Function to add a new assumption to the path constraint
assumeStateVar :: SymbolicState -> Expr -> SymbolicState
assumeStateVar (env, constraint) expr =
  let newConstraint = reduceExpr $ BinopExpr And constraint expr
   in (env, newConstraint)

-- Symbolic execution tree node
data SymNode = SymNode
  { stmt :: Stmt, -- The statement that led to this node
    state :: SymbolicState, -- The symbolic state at this node
    depth :: Int, -- Depth in the tree
    children :: [SymNode] -- Child nodes
  }
  deriving (Show)

-- | Convert a SymNode tree to a Mermaid state diagram
showMermaid :: SymNode -> String
showMermaid root =
  unlines $
    "stateDiagram-v2" : indent (origin ++ nodeLines root)
  where
    indent = map ("  " ++)
    origin = ["0 : (, true)", "0 --> " ++ show (uniqueId root) ++ ": " ++ sanitizeStmt (stmt root)]

-- Generate all node and transition lines
nodeLines :: SymNode -> [String]
nodeLines node =
  thisNode ++ concatMap nodeLines (children node) ++ transitions
  where
    (env, contraint) = state node
    label = " (" ++ intercalate ", " [k ++ " -> " ++ show v | (k, v) <- M.toList env] ++ ", " ++ show contraint ++ ") " ++ show (depth node)

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
symbolicExecute n k node | depth node > n = node -- Stop execution when depth exceeds max depth
symbolicExecute n k node = case stmt node of
  Skip -> node -- No further execution
  Assign var expr ->
    let state' = updateStateVar (state node) var expr
     in node {state = state'}
  Assume expr -> node {state = assumeStateVar (state node) expr}
  Seq s1 s2 ->
    let n' = symbolicExecute n k node {stmt = s1}
        -- Helper function to execute s2 on the lowest children
        -- executeOnChildren :: SymNode -> SymNode
        -- executeOnChildren child@SymNode {children = []} = symbolicExecute n k child {stmt = s2, depth = depth child + 1}
        -- executeOnChildren child = child {children = map executeOnChildren (children child)}

        n'' = symbolicExecute2 n k n' s2

     in n'' 
  IfThenElse guard s1 s2 ->
    let trueBranch = symbolicExecute n k node {stmt = Seq (Assume guard) s1, depth = depth node + 1}
        falseBranch = symbolicExecute n k node {stmt = Seq (Assume (OpNeg guard)) s2, depth = depth node + 1}
     in node {stmt = Skip, children = [trueBranch, falseBranch]} -- TODO: Merge states if possible
  _ -> node -- Other statements not handled yet

symbolicExecute2 :: Int -> Int -> SymNode -> Stmt -> SymNode
symbolicExecute2 n k node@SymNode {children = []} stmt = node { children = [symbolicExecute n k node {stmt = stmt, depth = depth node + 1}]}
symbolicExecute2 n k node stmt = node {children = map (\c -> symbolicExecute2 n k c stmt) (children node)}

getLowestChildren :: SymNode -> [SymNode]
getLowestChildren n = case children n of
  [] -> [n]
  cs -> concatMap getLowestChildren cs