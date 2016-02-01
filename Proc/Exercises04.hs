{-|

Programming Languages
Fall 2015

Implementation in Haskell of the Proc Language described in
Chapter 2 of Nielson & Nielson, Semantics with Applications

Author: Pablo López

-}

module Exercises04 where

import Proc
import ProcNaturalSemantics
-- import Test.HUnit hiding (State)

-- | 'Proc.hs' defines the syntax of PROC, a simple, block structured,
-- | imperative programming language with static scope. You should not
-- | modify Proc.hs
-- |
-- | 'ProcNaturalSemantics.hs' contains some definitions for a natural
-- | semantics for PROC. Most definitions are omitted. You must modify
-- | 'ProcNaturalSemantics.hs' to complete the definition.
-- |
-- | 'Exercises04.hs' contains directions, testing code, and expected
-- | outputs. You should not modify 'Exercises04.hs'.
-- |
-- | The only file to modify and submit is 'ProcNaturalSemantics.hs'.

-- |----------------------------------------------------------------------
-- | Exercise 1 - Variable Declarations
-- |----------------------------------------------------------------------

-- | Exercise 1.1
-- |
-- | 'ProcNaturalSemantics.hs' contains definitions for locations, stores,
-- | and variable environments. Complete the definitions of 'updateV' and
-- | 'updateS' in 'ProcNaturalSemantics.hs'.

-- | Exercise 1.2

-- | 'ProcNaturalSemantics.hs' defines the algebraic data type 'ConfigD' to
-- | represent configurations of the transition system for variable
-- | declarations using locations -> D. Modify 'ProcNaturalSemantics.hs' and
-- | complete the definition of function 'nsDecV' that implements the transition
-- | system shown on slide 68.

-- | The code below tests your definitions. First we initialize variable
-- | environment and the store:

-- note that global variables are not allowed in PROC
initEnvV :: EnvVar
initEnvV x = error $ "undefined variable " ++ x

-- accessing a non-allocated location yields an error
initStore :: Store
initStore l
  | l == next = 1
  | otherwise = error $ "undefined location " ++ show l

-- | 'showDecV' shows the variables declared in a 'DecVar', that is, the section
-- | of a block containing variable declarations. For each variable 'v' in the list
-- | 'vars', it shows its location and value:

showDecV :: DecVar -> EnvVar -> Store -> [Var] -> String
showDecV decs env sto vars = foldr (showVar env' sto')  [] vars
  where
     FinalD env' sto' = nsDecV (InterD decs env sto)
     showVar env sto x s = "var " ++ x ++ " loc " ++ show (env' x) ++ " val " ++ show (sto' . env' $ x) ++ "\n" ++ s

-- | Some variable declarations:

declarations :: DecVar
declarations =  Dec "x" (N 5)
               (Dec "y" (N 2)
               (Dec "z" (Mult (V "x") (V "y"))
               (Dec "x" (Add (V "x") (N 1))
                EndDec)))

-- | Finally, a simple test for variable declarations:

testVarDec :: IO()
testVarDec = putStr $ showDecV declarations initEnvV initStore ["x", "y", "z"]

-- | And the expected output:

{-

*Exercises03> testVarDec
var x loc 4 val 6
var y loc 2 val 2
var z loc 3 val 10

-}

-- |----------------------------------------------------------------------
-- | Exercise 2
-- |----------------------------------------------------------------------

-- | 'ProcNaturalSemantics.hs' defines an algebraic data type 'EnvProc' to
-- | represent procedure environments.

-- | Exercise 2.1
-- |
-- | Complete the definition of 'updP' in 'ProcNaturalSemantics.hs' (function
-- | updD is shown on slide 69).

-- | Exercise 2.2
-- |
-- | Complete the definition of 'envProc' in 'ProcNaturalSemantics.hs'.
-- | 'envProc envP p' looks up a definition for procedure 'p' in  the
-- | procedure environment 'envP'. If 'p' is defined in 'envP', then
-- | 'envProc' returns a tuple (s, envV', envP') with 's', the body of 'p',
-- | and the snapshots of the variable and procedure environments 'envV''
-- | and 'envP'' associated to 'p'. If 'p' is not defined in 'envP', the
-- | function raises an error "undefined procedure"

-- | The code below tests your definitions. First we initialize the procedure
-- | environment:

initEnvP :: EnvProc
initEnvP = EmptyEnvProc

-- | 'showDecP' shows the procedures declared in a 'DecProc', that is, the section
-- | of a block containing procedure declarations. For each procedure 'p', it shows
-- | the other procedures it knows (i.e., can be invoked from 'p').

showDecP :: DecProc -> String
showDecP procs =
   showDecP' $ updP procs undefined EmptyEnvProc
   where
      showDecP' EmptyEnvProc = ""
      showDecP' (EnvP p s envV envP envP') = p ++ " knows " ++ knows envP ++ "\n" ++ showDecP' envP'
      knows EmptyEnvProc = ""
      knows (EnvP p s envV envP envP') = p ++ " " ++ knows envP'
--      showDecP' (EnvP p s envV envP envP') = p ++ "\n" ++ showDecP' envP'

-- | Some procedure declarations:

procedures :: DecProc
procedures =  Proc "p" Skip
             (Proc "q" Skip
             (Proc "t" Skip
              EndProc))

-- | Finally, a simple test for procedure declarations:

testProcDec :: IO()
testProcDec = putStr $ showDecP procedures

-- | And the expected output:

{-

*Exercises03> testProcDec
t knows q p
q knows p
p knows

-}

-- |----------------------------------------------------------------------
-- | Exercise 3
-- |----------------------------------------------------------------------

-- | Finally, we can implement the natural semantics for PROC.
-- | 'ProcNaturalSemantics.hs' defines the algebraic data type
-- | 'Config' that represents the configurations of the transition
-- | system.

-- | Exercise 3.1
-- |
-- | Complete the definition of the transition relation 'nsStm'.
-- | The rules and axioms are shown on slides 71 to 78.
-- | Note that there are two rules for 'call p', depending on whether
-- | PROC allows recursive procedures or not. Code both rules, but
-- | comment out one of them when testing your code.

-- | The code below tests your definitions.

-- | 'showStore' shows the contents of a 'Store' (a memory dump).
-- | Recall that variable names are missing, but you can relate
-- | memory cells to variables by numbering the variables from 1.

showStore :: Store -> [(Integer, Integer)]
showStore sto = [(l, v) | l <- [1..sto next - 1], let v = sto l]

-- | This is a simple program to compute the factorial of 5 (the number
-- | appearing in the condition of the while loop)

prog1 :: Stm
prog1 = Block (Dec "x" (N 1)  -- located in 1
              (Dec "y" (N 1)  -- located in 2
               EndDec))

               EndProc

               
                      (Or (Ass "x" (Mult (V "x") (N 3)) )
                            (Ass "y" (Add (V "y") (N 1)))
                      )
               

-- | This runs 'prog1' and shows the final store:

execProg1 = xs
  where 
    xs = [showStore sto | (Final sto) <- nsStm initEnvV initEnvP (Inter prog1 initStore)]

-- | The expected output is:

{-

*Exercises04> execProg1
[(1,120),(2,6)

recall: x is located in 1, y is located in 2

-}


