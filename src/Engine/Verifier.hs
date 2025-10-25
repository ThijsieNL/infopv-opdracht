module Verifier where

import GCLParser.GCLDatatype
import Z3.Monad (Z3)

x :: Stmt -> Z3 ()
x = undefined