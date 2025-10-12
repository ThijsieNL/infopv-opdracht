module Algebra where

import GCLParser.GCLDatatype
  ( BinOp,
    Expr (..),
    Stmt (..),
    VarDeclaration,
  )

data ExprAlgebra r = ExprAlgebra
  { onVar :: String -> r,
    onLitI :: Int -> r,
    onLitB :: Bool -> r,
    onLitNull :: r,
    onParens :: r -> r,
    onArrayElem :: r -> r -> r,
    onOpNeg :: r -> r,
    onBinopExpr :: BinOp -> r -> r -> r,
    onForall :: String -> r -> r,
    onExists :: String -> r -> r,
    onSizeOf :: r -> r,
    onRepBy :: r -> r -> r -> r,
    onCond :: r -> r -> r -> r,
    onNewStore :: r -> r,
    onDereference :: String -> r
  }

foldExpr :: ExprAlgebra r -> Expr -> r
foldExpr f = go
  where
    go (Var v) = onVar f v
    go (LitI x) = onLitI f x
    go (LitB b) = onLitB f b
    go LitNull = onLitNull f
    go (Parens e) = onParens f (go e)
    go (ArrayElem arr idx) = onArrayElem f (go arr) (go idx)
    go (OpNeg e) = onOpNeg f (go e)
    go (BinopExpr op e1 e2) = onBinopExpr f op (go e1) (go e2)
    go (Forall var e) = onForall f var (go e)
    go (Exists var e) = onExists f var (go e)
    go (SizeOf e) = onSizeOf f (go e)
    go (RepBy arr idx val) = onRepBy f (go arr) (go idx) (go val)
    go (Cond cond thenE elseE) = onCond f (go cond) (go thenE) (go elseE)
    go (NewStore e) = onNewStore f (go e)
    go (Dereference var) = onDereference f var

defaultExprAlgebra :: ExprAlgebra Expr
defaultExprAlgebra =
  ExprAlgebra
    { onVar = Var,
      onLitI = LitI,
      onLitB = LitB,
      onLitNull = LitNull,
      onParens = Parens,
      onArrayElem = ArrayElem,
      onOpNeg = OpNeg,
      onBinopExpr = BinopExpr,
      onForall = Forall,
      onExists = Exists,
      onSizeOf = SizeOf,
      onRepBy = RepBy,
      onCond = Cond,
      onNewStore = NewStore,
      onDereference = Dereference
    }

data StmtAlgebra r = StmtAlgebra
  { onSkip :: r,
    onAssert :: Expr -> r,
    onAssume :: Expr -> r,
    onAssign :: String -> Expr -> r,
    onAAssign :: String -> Expr -> Expr -> r,
    onDrefAssign :: String -> Expr -> r,
    onSeq :: r -> r -> r,
    onIfThenElse :: Expr -> r -> r -> r,
    onWhile :: Expr -> r -> r,
    onBlock :: [VarDeclaration] -> r -> r,
    onTryCatch :: String -> r -> r -> r
  }

foldStmt :: StmtAlgebra r -> Stmt -> r
foldStmt f = go
  where
    go Skip = onSkip f
    go (Assert expr) = onAssert f expr
    go (Assume expr) = onAssume f expr
    go (Assign var expr) = onAssign f var expr
    go (AAssign var index expr) = onAAssign f var index expr
    go (DrefAssign var expr) = onDrefAssign f var expr
    go (Seq s1 s2) = onSeq f (go s1) (go s2)
    go (IfThenElse guard s1 s2) = onIfThenElse f guard (go s1) (go s2)
    go (While guard body) = onWhile f guard (go body)
    go (Block vars body) = onBlock f vars (go body)
    go (TryCatch e s1 s2) = onTryCatch f e (go s1) (go s2)

defaultStmtAlgebra :: StmtAlgebra Stmt
defaultStmtAlgebra =
  StmtAlgebra
    { onSkip = Skip,
      onAssert = Assert,
      onAssume = Assume,
      onAssign = Assign,
      onAAssign = AAssign,
      onDrefAssign = DrefAssign,
      onSeq = Seq,
      onIfThenElse = IfThenElse,
      onWhile = While,
      onBlock = Block,
      onTryCatch = TryCatch
    }
