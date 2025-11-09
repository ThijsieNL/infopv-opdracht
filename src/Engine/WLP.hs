module WLP (reduceExpr, substituteExpr) where

import Algebra
import GCLParser.GCLDatatype

-- | Reduce an expression using algebraic simplifications, should be used only if necessary
reduceExpr :: Expr -> Expr
reduceExpr = foldExpr reduceAlgebra

reduceAlgebra :: ExprAlgebra Expr
reduceAlgebra =
  defaultExprAlgebra
    { onOpNeg = \e -> case e of
        LitB b -> LitB (not b) -- Constant folding for negation
        OpNeg inner -> inner -- Double negation elimination
        _ -> OpNeg e,
      onParens = id, -- Remove unnecessary parentheses
      onBinopExpr = \op e1 e2 -> case (op, e1, e2) of
        (And, _, _) -> conjunctionReduction e1 e2
        (Or, _, _) -> disjunctionReduction e1 e2
        (Implication, _, _) -> implicationReduction e1 e2
        -- Zero and identity laws
        (Plus, _, LitI 0) -> e1
        (Plus, LitI 0, _) -> e2
        (Minus, _, LitI 0) -> e1
        (Multiply, _, LitI 1) -> e1
        (Multiply, LitI 1, _) -> e2
        (Multiply, _, LitI 0) -> LitI 0
        (Multiply, LitI 0, _) -> LitI 0
        (Divide, _, LitI 1) -> e1
        (Divide, LitI 0, _) -> LitI 0
        -- Constant folding for arithmetic operations for now only Plus and Minus
        (Plus, _, _) -> constantFolding (BinopExpr Plus e1 e2)
        (Minus, _, _) -> constantFolding (BinopExpr Minus e1 e2)
        _ -> BinopExpr op e1 e2,
      onArrayElem = \arrExpr i ->
        case arrExpr of
          RepBy arr idx val ->
            if idx == i
              then val -- Direct replacement if index matches
              else ArrayElem arr i
          _ -> ArrayElem arrExpr i
    }

    where
      -- | Reduction rules for conjunctions
      conjunctionReduction :: Expr -> Expr -> Expr
      conjunctionReduction (LitB True) r = r
      conjunctionReduction l (LitB True) = l
      conjunctionReduction (LitB False) _ = LitB False
      conjunctionReduction _ (LitB False) = LitB False
      conjunctionReduction l r | l == r = l -- Idempotent law
      conjunctionReduction l r = BinopExpr And l r

      -- | Reduction rules for disjunctions
      disjunctionReduction :: Expr -> Expr -> Expr
      disjunctionReduction (LitB False) r = r
      disjunctionReduction l (LitB False) = l
      disjunctionReduction (LitB True) _ = LitB True
      disjunctionReduction _ (LitB True) = LitB True
      disjunctionReduction l r | l == r = l -- Idempotent law
      disjunctionReduction l r = BinopExpr Or l r

      -- | Reduction rules for implications
      implicationReduction :: Expr -> Expr -> Expr
      implicationReduction (LitB False) _ = LitB True
      implicationReduction _ (LitB True) = LitB True
      implicationReduction (LitB True) r = r
      implicationReduction l (LitB False) = OpNeg l -- Negation
      implicationReduction l r | l == r = LitB True -- Tautology
      implicationReduction l r = BinopExpr Implication l r

      constantFolding :: Expr -> Expr
      constantFolding (BinopExpr op (LitI i) (LitI j)) = LitI (performArithmetic op i j)
      -- Fold nested addition: (e + i) + j  ==> e + (i + j)
      constantFolding (BinopExpr Plus (BinopExpr Plus e1 (LitI i)) (LitI j)) =
          constantFolding (BinopExpr Plus e1 (LitI (i + j)))

      -- Fold nested subtraction: (e - i) - j  ==> e - (i + j)
      constantFolding (BinopExpr Minus (BinopExpr Minus e1 (LitI i)) (LitI j)) =
          constantFolding (BinopExpr Minus e1 (LitI (i + j)))

      -- Simplify adding a negative number: e + (-i) ==> e - i
      constantFolding (BinopExpr Plus e1 (LitI i)) | i < 0 =
          constantFolding (BinopExpr Minus e1 (LitI (abs i)))

      -- Simplify subtracting a negative number: e - (-i) ==> e + i
      constantFolding (BinopExpr Minus e1 (LitI i)) | i < 0 =
          constantFolding (BinopExpr Plus e1 (LitI (abs i)))
      constantFolding e = e

      performArithmetic :: BinOp -> Int -> Int -> Int
      performArithmetic Plus = (+)
      performArithmetic Minus = (-)
      performArithmetic Multiply = (*)
      performArithmetic Divide = div
      performArithmetic _ = error "Unsupported operation for constant folding"

substituteExpr :: String -> Expr -> Expr -> Expr
substituteExpr var new = foldExpr $ substituteAlgebra var new

substituteAlgebra :: String -> Expr -> ExprAlgebra Expr
substituteAlgebra var new =
  defaultExprAlgebra
    { onVar = \v -> if v == var || var == "arr_" ++ v then new else Var v,
      onSizeOf = \e -> case e of
        Var a | "len_" ++ a == var -> new
        Var _ -> SizeOf e
        _ -> error $ "SizeOf expects a variable in substitution, got: " ++ show e
    }