{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -Wno-type-defaults #-}

module Main where

import Algebra
import GCLParser.GCLDatatype
import GCLParser.Parser (parseGCLfile)
import Z3.Monad hiding (substitute)
import Control.Monad.IO.Class

data ProgramTree = Node Stmt [ProgramTree]
  deriving (Show)

-- data TreeNode = TreeNode
--   { stmt :: Stmt,
--     children :: [TreeNode]
--   }

main :: IO ()
main =
  parseGCLfile "examples/min.gcl" >>= \case
    Left err -> putStrLn $ "Error parsing GCL file: " ++ err
    Right program -> do
      putStrLn "Parsed GCL Program:"
      print program

      let programStmt = stmt program
      putStrLn "\nOriginal Statement:"
      print programStmt

      -- This needs to be done for the feasibility checker
      -- let filteredStmt = transformAsserts programStmt
      -- putStrLn "\nFiltered Statement (without asserts):"
      -- print filteredStmt

      -- make a tree of paths through the program

      -- find the WLP of the program tree

      let k = 3 -- The fixed point bound
      let programTree = makeProgramTree programStmt
      -- let wlp = findWLP k programTree
      putStrLn "\nProgram Tree:"
      putStrLn (printProgramTree programTree)


      let wlpFormula = reduceExpr $ stmtToWlp k programStmt (LitB True)
      putStrLn "\nWLP Formula:"
      print wlpFormula

      evalZ3 $ do
        ast <- exprToZ3 wlpFormula
        str <- astToString ast
        liftIO $ putStrLn ("\nZ3 AST String Representation:\n" ++ str)

      putStrLn "\nAnalyzing WLP Formula with Z3:"
      validateExpr wlpFormula >>= \case
        True -> putStrLn "The WLP formula is valid."
        False -> putStrLn "The WLP formula is not valid."

{-TODO: check the assignment, what to do with assumes and asserts in the tree.-}
makeProgramTree :: Stmt -> ProgramTree
makeProgramTree stmt = case stmt of
  Assume _ -> Node stmt []
  Assign _ _ -> Node stmt []
  Seq s1 s2 ->
    linkSeq (makeProgramTree s1) (makeProgramTree s2)
  IfThenElse g s1 s2 ->
      Node Skip [makeProgramTree (Seq (Assume g) s1), makeProgramTree (Seq (Assume (OpNeg g)) s2)]
  While cond body ->
    let unrollLoop 0 = Node Skip []
        unrollLoop n =
          let Node _ children = makeProgramTree (Seq (Assume cond) body)
          in Node (Seq (Assume cond) body) (children ++ [unrollLoop (n - 1)])
    in Node stmt [unrollLoop 3, Node (Assume (OpNeg cond)) []] --we do 3 unrolls for now
  Block _ body ->
    Node stmt [makeProgramTree body]
  TryCatch _ s1 s2 ->
    Node stmt [makeProgramTree s1, makeProgramTree s2] -- Treat try-catch like if-then-else for tree purposes
  Assert s1 -> --check this, this is filler data... 
    Node (Assume s1) [] -- Replace asserts with Skip, making them effectively empty
  _ -> Node stmt []

{- Link two sequential program trees -}
linkSeq :: ProgramTree -> ProgramTree -> ProgramTree
linkSeq (Node stmt []) next = Node stmt [next]
linkSeq (Node stmt children) next = Node stmt (map (`linkSeq` next) children)

-- function to pretty print the program tree
printProgramTree :: ProgramTree -> String
printProgramTree = go 0
  where
    go :: Int -> ProgramTree -> String
    go indent (Node stmt children) =
      replicate indent ' ' ++ show stmt ++ concatMap (\child -> "\n" ++ go (indent + 2) child) children

-- here, k is the fixed point bound for while loops
findWLP :: Int -> ProgramTree -> Expr
findWLP k (Node stmt children) =
  let childWLPs = map (findWLP k) children
      combinedChildWLP = foldr opAnd (LitB True) childWLPs
  in stmtToWlp k stmt combinedChildWLP


validateExpr :: Expr -> IO Bool
validateExpr expr = evalZ3 $ do
  z3expr <- exprToZ3 $ OpNeg expr
  assert z3expr
  res <- check
  case res of
    Sat -> return False
    Unsat -> return True
    Undef -> error "Z3 returned UNKNOWN"

analyzeExpr :: Expr -> IO ()
analyzeExpr expr = evalZ3 $ do
  z3expr <- exprToZ3 expr
  assert z3expr
  res <- check
  case res of
    Sat -> do
      (_, mModel) <- getModel
      case mModel of
        Just mdl -> do
          str <- modelToString mdl
          liftIO $ putStrLn ("SAT\n" ++ str)
        Nothing -> liftIO $ putStrLn "SAT\nNo model available."
    Unsat -> liftIO $ putStrLn "UNSAT"
    Undef -> liftIO $ putStrLn "UNKNOWN"


-- Filter out any assert statements from the program and convert assumes to asserts
transformAsserts :: Stmt -> Stmt
transformAsserts =
  foldStmt
    defaultStmtAlgebra
      { onAssert = const Skip,
        onAssume = Assert
      }

reduceExpr :: Expr -> Expr
reduceExpr = foldExpr reduceAlgebra

reduceAlgebra :: ExprAlgebra Expr
reduceAlgebra = defaultExprAlgebra {
    onOpNeg = \e -> case e of
      LitB b -> LitB (not b)
      OpNeg inner -> inner -- Double negation elimination
      _ -> OpNeg e,
    onBinopExpr = \op e1 e2 -> case (op, e1, e2) of
      (And, LitB True, r) -> r
      (And, l, LitB True) -> l
      (And, LitB False, _) -> LitB False
      (And, _, LitB False) -> LitB False
      (Or, LitB False, r) -> r
      (Or, l, LitB False) -> l
      (Or, LitB True, _) -> LitB True
      (Or, _, LitB True) -> LitB True
      (Implication, LitB False, _) -> LitB True
      (Implication, _, LitB True) -> LitB True
      (Implication, LitB True, r) -> r
      (Implication, l, LitB False) -> OpNeg l
      (Plus, _, LitI 0) -> e1
      (Plus, LitI 0, _) -> e2
      (Plus, LitI i, LitI j) -> LitI (i + j)
      (Plus, BinopExpr Plus l1 (LitI i), LitI j) -> BinopExpr Plus l1 (LitI (i + j)) -- Flatten nested additions 
      (Minus, BinopExpr Minus l1 (LitI i), LitI j) -> BinopExpr Minus l1 (LitI (i + j)) -- Flatten nested additions 
      (Multiply, _, LitI 1) -> e1
      (Multiply, LitI 1, _) -> e2
      (Multiply, _, LitI 0) -> LitI 0
      (Multiply, LitI 0, _) -> LitI 0
      _ -> BinopExpr op e1 e2
}

stmtToWlp :: Int -> Stmt -> Expr -> Expr
stmtToWlp k =
  foldStmt
    StmtAlgebra
      { onSkip = id,
        onAssert = opAnd,
        onAssume = opImplication,
        onAssign = substitute,
        onAAssign = \_ _ _ -> error "WLP for array assignments not implemented yet",
        onDrefAssign = \_ _ -> error "WLP for dereference assignments not implemented yet",
        onSeq = \s1 s2 post -> s1 (s2 post),
        onIfThenElse = \guard s1 s2 post -> opAnd (opImplication guard (s1 post)) (opImplication (OpNeg guard) (s2 post)),
        onWhile = iterateWlpBounded k,
        onBlock = \_ f -> f,
        onTryCatch = \_ _ _ -> error "WLP for TryCatch not implemented yet"
      }

-- We need to create a fixed-point combinator for while loops
iterateWlpBounded :: Int -> Expr -> (Expr -> Expr) -> Expr -> Expr
iterateWlpBounded 0 _ _ post = post
iterateWlpBounded k guard f post =
  opAnd (opImplication (OpNeg guard) post) (opImplication guard (f (iterateWlpBounded (k - 1) guard f post)))

substitute :: String -> Expr -> Expr -> Expr
substitute var new post = foldExpr substituteAlgebra post var new

substituteAlgebra :: ExprAlgebra (String -> Expr -> Expr)
substituteAlgebra =
  ExprAlgebra
    { onVar = \v var new -> if v == var then new else Var v,
      onLitI = \i _ _ -> LitI i,
      onLitB = \b _ _ -> LitB b,
      onLitNull = \_ _ -> LitNull,
      onParens = \e var new -> Parens (e var new),
      onArrayElem = \arr index var new -> ArrayElem (arr var new) (index var new),
      onOpNeg = \e var new -> OpNeg (e var new),
      onBinopExpr = \op e1 e2 var new -> BinopExpr op (e1 var new) (e2 var new),
      onForall = \v e var new -> if v == var then Forall v new else Forall v (e var new), -- Is this correct?
      onExists = \v e var new -> if v == var then Exists v new else Exists v (e var new), -- Is this correct?
      onSizeOf = \arr var new -> SizeOf (arr var new),
      onRepBy = \arr index val var new -> RepBy (arr var new) (index var new) (val var new),
      onCond = \guard e1 e2 var new -> Cond (guard var new) (e1 var new) (e2 var new),
      onNewStore = \_ _ -> NewStore,
      onDereference = \ptr _ _ -> Dereference ptr -- This probably is wrong
    }

exprToZ3 :: Expr -> Z3 AST
exprToZ3 = foldExpr exprToZ3Algebra

exprToZ3Algebra :: ExprAlgebra (Z3 AST)
exprToZ3Algebra =
  ExprAlgebra
    { onVar = \v -> do
        sym <- mkStringSymbol v
        mkIntVar sym,
      onLitI = mkInteger . toInteger,
      onLitB = mkBool,
      onLitNull = mkInteger 0, -- Represent null as 0 for simplicity
      onOpNeg = (>>= mkNot),
      onBinopExpr = \x e1 e2 -> do
        ast1 <- e1
        ast2 <- e2
        case x of
          And -> mkAnd [ast1, ast2]
          Or -> mkOr [ast1, ast2]
          Implication -> mkImplies ast1 ast2
          LessThan -> mkLt ast1 ast2
          LessThanEqual -> mkLe ast1 ast2
          GreaterThan -> mkGt ast1 ast2
          GreaterThanEqual -> mkGe ast1 ast2
          Equal -> mkEq ast1 ast2
          Minus -> mkSub [ast1, ast2]
          Plus -> mkAdd [ast1, ast2]
          Multiply -> mkMul [ast1, ast2]
          Divide -> mkDiv ast1 ast2
          Alias -> error "Alias operation not supported in Z3 translation",

      onParens = id,
      onArrayElem = undefined,
      onForall = undefined,
      onExists = undefined,
      onSizeOf = undefined,
      onRepBy = undefined,
      onCond = undefined,
      onNewStore = undefined,
      onDereference = undefined
    }

{-
necessities:
- WLP calculation (calculate the wlp of a given program)
    - possible also a wlp tree structure, so that we can handle conditionals
      and loops better
- convert WLP to Z3 format
- Z3 interaction (send the formula to Z3 and get the result back)

-}