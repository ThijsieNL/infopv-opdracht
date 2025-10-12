module WLP where

import Algebra
import GCLParser.GCLDatatype

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