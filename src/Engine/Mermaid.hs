module Mermaid (showMermaid) where

import Data.Hashable
import Data.List
import qualified Data.Map as M
import DataTypes
import GCLParser.GCLDatatype hiding (stmt)
import WLP

showMermaid :: Program -> SymbolicTree -> String
showMermaid program root = unlines $ "stateDiagram-v2" : indent (origin ++ nodeLines root)
  where
    indent = map ("  " ++)
    initialState = (createSymEnv program, LitB True)
    origin = ["0 : " ++ sanitizeStr (showSymbolicState initialState) ++ "0"]

-- | Convert a SymbolicTree to a list of lines describing nodes and transitions
nodeLines :: SymbolicTree -> [String]
nodeLines = go 0
  where
    -- common function to generate a label for a node
    nodeLabel :: NodeData -> String
    nodeLabel nd = sanitizeStr $ showSymbolicState (nodeState nd) ++ showValidity (nodeValidity nd) ++ show (nodeDepth nd)

    -- common function to generate the node's line
    nodeLine :: SymbolicTree -> String
    nodeLine constructor = show (uniqueId constructor) ++ " : " ++ nodeLabel (getNodeData constructor)

    -- common function to generate a transition line
    transitionLine :: Int -> SymbolicTree -> String
    transitionLine from to = show from ++ " --> " ++ show (uniqueId to) ++ " : " ++ sanitizeStr (show (nodeStmt (getNodeData to)))

    lineBreakToComma :: String -> String
    lineBreakToComma [] = []
    lineBreakToComma reason = ": " ++ concatMap (\c -> if c `elem` "\r\n" then ", " else [c]) reason

    showValidity :: Validity -> String
    showValidity (Infeasible reason) = " [INFEASIBLE" ++ lineBreakToComma reason ++ "]<br>"
    showValidity (Invalid reason) = " [INVALID" ++ lineBreakToComma reason ++ "]<br>"
    showValidity _ = ""

    getNodeData :: SymbolicTree -> NodeData
    getNodeData (Leaf nd) = nd
    getNodeData (Sequence nd _) = nd
    getNodeData (Branch _ _) = error "Branch nodes do not have NodeData" 

    go :: Int -> SymbolicTree -> [String]
    go id n@(Leaf _) = [nodeLine n, transitionLine id n]
    go id n@(Sequence _ st) = [nodeLine n, transitionLine id n] ++ go (uniqueId n) st
    go id (Branch l r) = go id l ++ go id r

-- | Generate a unique ID for a SymbolicTree based on its content
uniqueId :: SymbolicTree -> Int
uniqueId tree = abs $ hash $ show tree

-- | Sanitize a mermaid string for compatibility
sanitizeStr :: String -> String
sanitizeStr = concatMap replaceColon
  where
    replaceColon ':' = "#58;"
    replaceColon ';' = "#59;"
    replaceColon c = [c]

-- | Show a symbolic state as a string
showSymbolicState :: SymbolicState -> String
showSymbolicState (env, constraint) = "(" ++ intercalate ", " [k ++ " -> " ++ show (reduceExpr v) | (k, v) <- M.toList env] ++ ")<br>(" ++ show (reduceExpr constraint) ++ ")<br>"