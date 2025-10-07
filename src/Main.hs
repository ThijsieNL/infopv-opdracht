{-# LANGUAGE LambdaCase #-}

module Main where

import Algebra
import GCLParser.GCLDatatype
import GCLParser.Parser (parseGCLfile)

main :: IO ()
main =
  parseGCLfile "examples/E.gcl" >>= \case
    Left err -> putStrLn $ "Error parsing GCL file: " ++ err
    Right program -> do
      putStrLn "Parsed GCL Program:"
      print program

      let programStmt = stmt program
      putStrLn "\nOriginal Statement:"
      print programStmt

      let filteredStmt = transformAsserts programStmt
      putStrLn "\nFiltered Statement (without asserts):"
      print filteredStmt

      let k = 3 -- The fixed point bound

      let wlpFormula = wlp k filteredStmt (LitB True) -- assuming postcondition is true
      putStrLn "\nWLP Formula:"
      print wlpFormula

-- Filter out any assert statements from the program and convert assumes to asserts
transformAsserts :: Stmt -> Stmt
transformAsserts =
  foldStmt
    defaultStmtAlgebra
      { onAssert = const Skip,
        onAssume = Assert
      }

wlp :: Int -> Stmt -> Expr -> Expr
wlp k =
  foldStmt
    StmtAlgebra
      { onSkip = id,
        onAssert = opAnd,
        onAssume = opImplication,
        onAssign = substitute,
        onAAssign = \_ _ _ -> error "WLP for array assignments not implemented yet",
        onDrefAssign = \_ _ -> error "WLP for dereference assignments not implemented yet",
        onSeq = (.), -- function composition
        onIfThenElse = \guard f1 f2 post -> opAnd (opImplication guard (f1 post)) (opImplication (OpNeg guard) (f2 post)),
        onWhile = iterateWlpBounded k,
        onBlock = \_ f -> f,
        onTryCatch = \_ _ _ -> error "WLP for TryCatch not implemented yet"
      }

-- We need to create a fixed-point combinator for while loops
iterateWlpBounded :: Int -> Expr -> (Expr -> Expr) -> Expr -> Expr
iterateWlpBounded 0 _ _ post = post
iterateWlpBounded k guard f post =
  opAnd (opImplication (OpNeg guard) post) (opImplication guard (f (iterateWlpBounded (k-1) guard f post)))

substitute :: String -> Expr -> Expr -> Expr
substitute var new post = foldExpr substituteAlgebra post var new

substituteAlgebra :: ExprAlgebra (String -> Expr -> Expr)
substituteAlgebra = ExprAlgebra
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

{-
necessities:
- WLP calculation (calculate the wlp of a given program)
    - possible also a wlp tree structure, so that we can handle conditionals
      and loops better
- convert WLP to Z3 format
- Z3 interaction (send the formula to Z3 and get the result back)

-}