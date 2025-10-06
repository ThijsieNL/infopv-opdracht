module Main where

main :: IO ()
main = putStrLn "This is the MuGCL module. Please use the functions in it \
                 \mannually."

-- in the folder examples we have some .gcl files, these are programs over which I need to find the WLP
-- placeholder, this function should read a .gcl file and return its WLP
wlp :: String -> String
wlp program = "WLP of the program: " ++ program

{-
necessities: 
- WLP calculation (calculate the wlp of a given program)
    - possible also a wlp tree structure, so that we can handle conditionals
      and loops better
- convert WLP to Z3 format
- Z3 interaction (send the formula to Z3 and get the result back)

-}