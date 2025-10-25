module Z3Utils where

import Z3.Monad
import GCLParser.GCLDatatype
import Algebra

exprIsSat :: Expr -> Z3 Bool
exprIsSat expr = local $ do
  z3expr <- exprToZ3 expr
  assert z3expr
  result <- check
  case result of
    Unsat -> return False
    Sat -> return True
    Undef -> error "Z3 returned UNKNOWN"
  
exprIsValid :: Expr -> Z3 Bool
exprIsValid expr = do
  z3expr <- exprToZ3 expr
  notExpr <- mkNot z3expr
  assert notExpr
  result <- check
  case result of
    Unsat -> return True
    Sat -> return False
    Undef -> error "Z3 returned UNKNOWN"


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