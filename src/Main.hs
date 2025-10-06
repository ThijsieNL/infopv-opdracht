{-# LANGUAGE LambdaCase #-}
module Main where

import GCLParser.GCLDatatype
import GCLParser.Parser ( parseGCLfile )

main :: IO ()
main = parseGCLfile "examples/min.gcl" >>= \case
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

        let wlpFormula = wlp filteredStmt (LitB True)  -- assuming postcondition is true
        putStrLn "\nWLP Formula:"
        print wlpFormula


-- Filter out any assert statements from the program and convert assumes to asserts
transformAsserts :: Stmt -> Stmt
transformAsserts (Assert _) = Skip
transformAsserts (Assume expr) = Assert expr
transformAsserts (Seq s1 s2) = Seq (transformAsserts s1) (transformAsserts s2)
transformAsserts (IfThenElse guard s1 s2) = IfThenElse guard (transformAsserts s1) (transformAsserts s2)
transformAsserts (While guard body) = While guard (transformAsserts body)
transformAsserts (Block vars body) = Block vars (transformAsserts body)
transformAsserts (TryCatch e s1 s2) = TryCatch e (transformAsserts s1) (transformAsserts s2)
transformAsserts stmt = stmt  -- For other statements, return as is

wlp :: Stmt -> Expr -> Expr
wlp Skip post = post
wlp (Assign var expr) post = substitute var expr post
wlp (Seq s1 s2) post = wlp s1 (wlp s2 post)
wlp (Assert condition) post = opAnd condition post
wlp (Assume condition) post = opImplication condition post
wlp (IfThenElse guard s1 s2) post = opAnd (opImplication guard (wlp s1 post)) (opImplication (OpNeg guard) (wlp s2 post))
wlp (While guard body) post = error "WLP for While loops not implemented yet"
wlp stmt _ = error $ "WLP for " ++ show stmt ++ " not implemented yet"

substitute :: String -> Expr -> Expr -> Expr
substitute var new (Var v) | v == var = new
                           | otherwise = Var v 
substitute var new (BinopExpr And e1 e2) = opAnd (substitute var new e1) (substitute var new e2)
substitute var new (BinopExpr Or e1 e2) = opOr (substitute var new e1) (substitute var new e2)
substitute var new (BinopExpr Implication e1 e2) = opImplication (substitute var new e1) (substitute var new e2)
substitute var new (OpNeg e) = OpNeg (substitute var new e)
substitute var new (BinopExpr Equal e1 e2) = opEqual (substitute var new e1) (substitute var new e2)
substitute var new (BinopExpr LessThan e1 e2) = opLessThan (substitute var new e1) (substitute var new e2)
substitute var new (BinopExpr GreaterThan e1 e2) = opGreaterThan (substitute var new e1) (substitute var new e2)
substitute var new (BinopExpr LessThanEqual e1 e2) = opLessThanEqual (substitute var new e1) (substitute var new e2)
substitute var new (BinopExpr GreaterThanEqual e1 e2) = opGreaterThanEqual (substitute var new e1) (substitute var new e2)
substitute _ _ post = post 
-- TODO: Is this correct? What about other Expr constructors?


{-
necessities: 
- WLP calculation (calculate the wlp of a given program)
    - possible also a wlp tree structure, so that we can handle conditionals
      and loops better
- convert WLP to Z3 format
- Z3 interaction (send the formula to Z3 and get the result back)

-}