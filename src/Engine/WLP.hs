module WLP (reduceExpr, substitute) where

import Algebra
import GCLParser.GCLDatatype
import GHC.RTS.Flags (ProfFlags (retainerSelector))

reduceExpr :: Expr -> Expr
reduceExpr = foldExpr reduceAlgebra

reduceAlgebra :: ExprAlgebra Expr
reduceAlgebra =
  defaultExprAlgebra
    { onOpNeg = \e -> case e of
        LitB b -> LitB (not b)
        OpNeg inner -> inner -- Double negation elimination
        _ -> OpNeg e,
      onParens = id, -- Remove unnecessary parentheses
      onBinopExpr = \op e1 e2 -> case (op, e1, e2) of
        (And, LitB True, r) -> r
        (And, l, LitB True) -> l
        (And, LitB False, _) -> LitB False
        (And, _, LitB False) -> LitB False
        (And, _, _) -> if e1 == e2 then e1 else BinopExpr op e1 e2 -- Idempotent law
        (Or, LitB False, r) -> r
        (Or, l, LitB False) -> l
        (Or, LitB True, _) -> LitB True
        (Or, _, LitB True) -> LitB True
        -- Zero and identity laws
        (Plus, _, LitI 0) -> e1
        (Plus, LitI 0, _) -> e2
        (Minus, _, LitI 0) -> e1
        (Multiply, _, LitI 1) -> e1
        (Multiply, LitI 1, _) -> e2
        (Multiply, _, LitI 0) -> LitI 0
        (Multiply, LitI 0, _) -> LitI 0
        -- Constant folding for arithmetic operations
        (Plus, _, _) -> constantFolding (BinopExpr Plus e1 e2)
        (Minus, _, _) -> constantFolding (BinopExpr Minus e1 e2)
        (Multiply, _, _) -> constantFolding (BinopExpr Multiply e1 e2)
        (Divide, _, _) -> constantFolding (BinopExpr Divide e1 e2)
        _ -> BinopExpr op e1 e2
    }

constantFolding :: Expr -> Expr
constantFolding (BinopExpr op (LitI i) (LitI j)) = LitI (performArithmetic op i j)
constantFolding (BinopExpr op (BinopExpr op' e1 (LitI i)) (LitI j)) = constantFolding (BinopExpr op' e1 (LitI (performArithmetic op i j)))
constantFolding (BinopExpr Plus e1 (LitI i)) | i < 0 = constantFolding (BinopExpr Minus e1 (LitI (abs i)))
constantFolding (BinopExpr Minus e1 (LitI i)) | i < 0 = constantFolding (BinopExpr Plus e1 (LitI (abs i)))
constantFolding e = e

performArithmetic :: BinOp -> Int -> Int -> Int
performArithmetic Plus = (+)
performArithmetic Minus = (-)
performArithmetic Multiply = (*)
performArithmetic Divide = div
performArithmetic _ = error "Unsupported operation for constant folding"

substitute :: String -> Expr -> Expr -> Expr
substitute var new = foldExpr $ substituteAlgebra var new

substituteAlgebra :: String -> Expr -> ExprAlgebra Expr
substituteAlgebra var new =
  defaultExprAlgebra
    { onVar = \v -> if v == var || var == "arr_" ++ v then new else Var v,
      onSizeOf = \e -> case e of
        Var a | "len_" ++ a == var -> new
        Var _ -> SizeOf e
        _ -> error $ "SizeOf expects a variable in substitution, got: " ++ show e
    }