{-# LANGUAGE LambdaCase #-}
module Z3Utils(exprIsSat, exprIsSatWithModel, exprIsValid, exprIsValidWithModel) where

import Z3.Monad
import GCLParser.GCLDatatype
import Algebra
import Debug.Trace

exprIsSat :: Expr -> Z3 Bool
exprIsSat = fmap ((== Sat) . fst) . exprIsSatWithModel

exprIsSatWithModel :: Expr -> Z3 (Result, Maybe Model)
exprIsSatWithModel expr = trace ("Z3 evaluation on: " ++ show expr) $ local $ do
  z3expr <- exprToZ3 expr
  -- z3expr <- mkBool True -- TODO: Fix translation
  assert z3expr
  result <- check
  getModel

exprIsValidWithModel :: Expr -> Z3 (Bool, Maybe Model)
exprIsValidWithModel expr = exprIsSatWithModel (OpNeg expr) >>= \case
  (Unsat, _) -> return (True, Nothing)
  (Sat, m)   -> return (False, m)
  (Undef, _) -> error "Z3 returned UNKNOWN"

exprIsValid :: Expr -> Z3 Bool
exprIsValid = fmap fst . exprIsValidWithModel

exprToZ3 :: Expr -> Z3 AST
exprToZ3 = foldExpr exprToZ3Algebra

exprToZ3Algebra :: ExprAlgebra (Z3 AST)
exprToZ3Algebra =
  ExprAlgebra
    { onVar = \v -> do
        sym <- mkStringSymbol v
        intSort <- mkIntSort
        if take 4 v == "arr_" then do
          arrSort <- mkArraySort intSort intSort
          mkConst sym arrSort
        else do
          mkConst sym intSort,
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
      onArrayElem = \arr idx -> do
        arrAst <- arr
        idxAst <- idx
        mkSelect arrAst idxAst,
      onForall = \var body -> do 
        bodyAst <- body
        intSort <- mkIntSort
        symbol <- mkStringSymbol var
        mkForall [] [symbol] [intSort] bodyAst,
      onExists = \var body -> do 
        bodyAst <- body
        intSort <- mkIntSort
        symbol <- mkStringSymbol var
        mkExists [] [symbol] [intSort] bodyAst,
      onSizeOf = id,
      onRepBy = \arr idx val -> do
        arrAst <- arr
        idxAst <- idx
        valAst <- val
        mkStore arrAst idxAst valAst,
      onCond = error "Conditional expressions not supported in Z3 translation",
      onNewStore = error "NewStore not supported in Z3 translation",
      onDereference = error "Dereference not supported in Z3 translation"
    }