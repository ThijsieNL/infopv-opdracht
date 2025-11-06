module Mermaid (showMermaid) where

import Data.Hashable
import Data.List
import qualified Data.Map as M
import GCLParser.GCLDatatype hiding (stmt)
import DataTypes
import WLP

showMermaid :: Program -> SymbolicTree -> String
showMermaid program root = unlines $ "stateDiagram-v2" : indent (origin ++ nodeLines root)
    where
        indent = map ("  " ++)
        nodeData = getNodeData root
        initialState = (createSymEnv program, LitB True)
        origin = ["0 : " ++ showSymbolicState initialState ++ "0", "0 --> " ++ show (uniqueId root) ++ ": " ++ sanitizeStmt (nodeStmt nodeData)]

-- | Convert a SymbolicTree to a list of lines describing nodes and transitions
nodeLines :: SymbolicTree -> [String]
nodeLines = go
  where
    -- common function to generate a label for a node
    nodeLabel nd = showSymbolicState (nodeState nd) ++ showValidity (nodeValidity nd) ++ show (nodeDepth nd)

    -- common function to generate the node's line
    nodeLine constructor = show (uniqueId constructor) ++ " : " ++ nodeLabel (getNodeData constructor)

    -- common function to generate a transition line
    transitionLine from to = show (uniqueId from) ++ " --> " ++ show (uniqueId to) ++ " : " ++ sanitizeStmt (nodeStmt (getNodeData to))

    showValidity (Infeasible reason) = " [INFEASIBLE#58; " ++ filter (`notElem` "\r\n") reason ++ "]<br>"
    showValidity (Invalid reason) = " [INVALID#58; " ++ filter (`notElem` "\r\n") reason ++ "]<br>"
    showValidity _ = ""

    go (Leaf nd) = [nodeLine (Leaf nd)]
    go (Sequence nd st) =
        let thisNode = nodeLine (Sequence nd st)
            trans = [transitionLine (Sequence nd st) st]
        in thisNode : go st ++ trans
    go (Branch nd left right) =
        let thisNode = nodeLine (Branch nd left right)
            trans = [transitionLine (Branch nd left right) left, transitionLine (Branch nd left right) right]
        in thisNode : go left ++ go right ++ trans

-- | Generate a unique ID for a SymbolicTree based on its content
uniqueId :: SymbolicTree -> Int
uniqueId tree = abs $ hash $ show tree

-- | Sanitize a statement string for Mermaid compatibility
sanitizeStmt :: Stmt -> String
sanitizeStmt = concatMap replaceColon . show
  where
    replaceColon ':' = "#58;"
    replaceColon ';' = "#59;"
    replaceColon c = [c]

-- | Show a symbolic state as a string
showSymbolicState :: SymbolicState -> String
showSymbolicState (env, constraint) = "(" ++ intercalate ", " [k ++ " -> " ++ show (reduceExpr v) | (k, v) <- M.toList env] ++ ")<br>(" ++ show (reduceExpr constraint) ++ ")<br>"