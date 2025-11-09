module Z3Utils (exprIsSat, exprIsSatWithModel, exprIsValid, exprIsValidWithModel) where

import Algebra
import Control.Monad.Reader hiding (local)
import Control.Monad.Writer
import DataTypes (SymbolicExecution)
import GCLParser.GCLDatatype
import Z3.Monad

-- | Calculate the size of all literals and variables in an expression
getFormulaSize :: Expr -> Int
getFormulaSize = foldExpr sizeAlgebra
  where
    sizeAlgebra :: ExprAlgebra Int
    sizeAlgebra =
      ExprAlgebra
        { onVar = const 1,
          onLitI = const 1,
          onLitB = const 1,
          onLitNull = 1,
          onParens = id,
          onArrayElem = (+),
          onOpNeg = id,
          onBinopExpr = \_ e1 e2 -> e1 + e2,
          onForall = \_ body -> body,
          onExists = \_ body -> body,
          onSizeOf = id,
          onRepBy = \arr idx val -> arr + idx + val,
          onCond = \cond thenE elseE -> cond + thenE + elseE,
          onNewStore = id,
          onDereference = const 1
        }

exprIsSat :: Expr -> SymbolicExecution Bool
exprIsSat = fmap ((== Sat) . fst) . exprIsSatWithModel

exprIsSatWithModel :: Expr -> SymbolicExecution (Result, Maybe Model)
exprIsSatWithModel expr = do
  tell [getFormulaSize expr] -- Log the formula size
  lift $ lift $ local $ do
    z3expr <- exprToZ3 expr
    assert z3expr
    result <- check
    getModel

exprIsValidWithModel :: Expr -> SymbolicExecution (Bool, Maybe Model)
exprIsValidWithModel expr =
  exprIsSatWithModel (OpNeg expr) >>= \case
    (Unsat, _) -> return (True, Nothing)
    (Sat, m) -> return (False, m)
    (Undef, _) -> error "Z3 returned UNKNOWN"

exprIsValid :: Expr -> SymbolicExecution Bool
exprIsValid = fmap fst . exprIsValidWithModel

exprToZ3 :: Expr -> Z3 AST
exprToZ3 = foldExpr exprToZ3Algebra

exprToZ3Algebra :: ExprAlgebra (Z3 AST)
exprToZ3Algebra =
  ExprAlgebra
    { onVar = \v -> do
        sym <- mkStringSymbol v
        intSort <- mkIntSort
        if take 4 v == "arr_"
          then do
            arrSort <- mkArraySort intSort intSort
            mkConst sym arrSort
          else mkConst sym intSort,
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
      onCond = \cond thenE elseE -> do
        condAst <- cond
        thenAst <- thenE
        elseAst <- elseE
        mkIte condAst thenAst elseAst, 
      onNewStore = error "NewStore not supported in Z3 translation",
      onDereference = error "Dereference not supported in Z3 translation"
    }