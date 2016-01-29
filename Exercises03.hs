{-|

Programming Languages
Fall 2015

Implementation in Haskell of the Structural Operational Semantics
described in Chapter 2 of Nielson & Nielson, Semantics with Applications

Author: Haritz Puerto-San-Roman

-}

module Exercises03 where

import While
import StructuralSemantics

-- |----------------------------------------------------------------------
-- | Exercise 1
-- |----------------------------------------------------------------------

-- | Given the type synonym 'DerivSeq' to represent derivation sequences
-- | of the structural operational semantics:

type DerivSeq = [Config]

-- | Define a function 'derivSeq' that given a WHILE statement 'st' and an
-- | initial state 's' returns the corresponding derivation sequence:

derivSeq :: Stm -> State -> DerivSeq
derivSeq st ini
  | isFinal (sosStm (Inter st ini)) =  [Inter st ini] ++ [sosStm (Inter st ini)]
  | otherwise = [Inter st ini] ++ (derivSeq st' s')
    where
      (Inter st' s') = sosStm (Inter st ini)
-- | To test your definition of 'derivSeq' you can use the code below.
-- | The function 'facSeq' returns the derivation sequence of the 'factorial'
-- | statement executed from the initial state 'sInit':

facSeq :: DerivSeq
facSeq = derivSeq factorial sInit

-- | The function 'showDerivSeq' returns a String representation  of
-- | a derivation sequence 'dseq'. The 'vars' argument is a list of variables
-- | that holds the variables to be shown in the state:

showDerivSeq :: [Var] -> DerivSeq -> String
showDerivSeq vars dseq = unlines (map showConfig dseq)
  where
    showConfig (Final s) = "Final state:\n" ++ unlines (showVars s vars)
    showConfig (Inter ss s) = show ss ++ "\n" ++ unlines (showVars s vars)
    showVars s vs = map (showVal s) vs
    showVal s x = " s(" ++ x ++ ")= " ++ show (s x)

-- | Therefore, you can print the derivation sequence of 'factorial' with:

showFacSeq :: IO()
showFacSeq = putStrLn $ showDerivSeq ["x", "y"] facSeq

-- | You should get an output identical to 'derivSeqForFactorial.txt'

-- | The function 'sSoS' below is the semantic function of the
-- | structural operational semantics of WHILE. Given a WHILE statement 'st'
-- | and an initial state 's' returns the final configuration of the
-- | corresponding derivation sequence:

sSos :: Stm -> State -> State
sSos ss s = s'
  where Final s' = last (derivSeq ss s)

sFac' :: State
sFac' = sSos factorial sInit

-- |----------------------------------------------------------------------
-- | Exercise 2
-- |----------------------------------------------------------------------
-- | The WHILE language can be extended with a 'repeat S until b' construct.

-- | Exercise 2.1
-- | Define the structural operational semantics of this new construct. You
-- | are not allowed to rely on the 'while b do S' statement.

{- Formal definition of 'repeat S until b'


        [repeat-sos] <repeat S until b, s> => <S; if !b repeat S until b else Skip, s>

-}

-- | Exercise 2.2
-- | Modify the definition of 'sosStm' in 'StructuralSemantics.hs' to deal
-- | with the 'repeat until' construct




-- | Exercise 2.3
-- | Write a WHILE program to test your definition of the repeat statement.
sum3 :: Stm 
sum3 = Comp (Ass "x" (N 0))
             (Repeat 
              (Ass "x" (Add (V "x") (N 1))) (Eq (V "x") (N 3)))


factorial2 :: Stm
factorial2 = Comp (Ass "y" (N 1))
                 (Repeat 
                    (Comp (Ass "y" (Mult (V "y") (V "x")))
                          (Ass "x" (Sub (V "x") (N 1))))
                    ( (Eq (V "x") (N 1))))
facSeq2 :: DerivSeq
facSeq2 = derivSeq factorial2 sInit

showFacSeq2 :: IO()
showFacSeq2 = putStrLn $ showDerivSeq ["x", "y"] facSeq2

sum3Seq :: DerivSeq
sum3Seq = derivSeq sum3 sInit

showSum3Seq = putStrLn $ showDerivSeq ["x"] sum3Seq


-- |----------------------------------------------------------------------
-- | Exercise 3
-- |----------------------------------------------------------------------

-- |  Extend WHILE with the 'Abort' statement.  The informal semantics of
-- |'Abort' is to abruptly stop the execution of the program, similar to
-- | a call to 'exit(0)' in other mainstream languages.

-- | Exercise 3.1
-- | Modify the definition of 'sosStm' in 'StructuralSemantics.hs' to deal
-- | with the 'abort' statement


-- | Exercise 3.2
-- | Define a function 'derivSeqAbort' similar to 'derivSeq' except
-- | that it deals with stuck configurations.

derivSeqAbort :: Stm -> State -> DerivSeq
derivSeqAbort Abort ini = [Final ini]
derivSeqAbort st ini 
  | isFinal (sosStm (Inter st ini)) =  [Inter st ini] ++ [sosStm (Inter st ini)]
  | otherwise = [Inter st ini] ++ (derivSeq st' s')
    where
      (Inter st' s') = sosStm (Inter st ini)
-- | You can test your code with the examples below and the function
-- | 'showAbortSeq':

showAbortSeq :: IO()
showAbortSeq = putStrLn $ showDerivSeq ["x", "y"] (derivSeqAbort abortExample1 sInit)

abortExample0 :: Stm
abortExample0 = Abort

abortExample1 :: Stm
abortExample1 =  Comp (Ass "x" (N 1))
                (Comp (Ass "y" (N 2))
                      Abort)

abortExample2 :: Stm
abortExample2 =  Comp (Ass "x" (N 1))
                (Comp (Ass "y" (N 2))
                (Comp  Abort
                      (Ass "z" (N 3))))

abortExample3 :: Stm
abortExample3 = Comp (Ass "x" (N 1))
                     (While (Le (V "x") (N 5))
                         (If (Eq (V "x") (N 3))
                             Abort
                             (Ass "x" (Add (V "x") (N 1))))
                     )


-- |----------------------------------------------------------------------
-- | TEST for x:= a1 to a2 do S
-- |----------------------------------------------------------------------

showForSeq :: IO()
showForSeq = putStrLn $ showDerivSeq ["x"] (derivSeqAbort exampleFor sInit)

-- |----------------------------------------------------------------------
-- | Exercise 4
-- |----------------------------------------------------------------------

-- | Implement in Haskell the Structural Operational Semantics for the
-- | evaluation of arithmetic expressions Aexp.

{-
   Structural Operational Semantics for the left-to-right evaluation of
   arithmetic expressions:

   A configuration is either intermediate <Aexp, State> or final Z.

   Note we are abusing notation and write 'n' for both a literal (syntax)
   and an integer (semantics). Same goes for arithmetic operators (+,-,*).

   [N]  ----------------
         < n, s > => n

   [V] ------------------------
        < x, s > => < s x, s >

   [+] -----------------------------  where n3 = n1 + n2
        < n1 + n2, s > => < n3, s >

            < a2, s > => < a2', s >
   [+] ----------------------------------
        < n1 + a2, s > => <n1 + a2', s >

            < a1, s > => < a1', s >
   [+] -----------------------------------
        < a1 + a2, s > => < a1' + a2, s >

   The rules for * and - are similar.

-}

-- | We use the algebraic data type 'AexpConfig' to represent the
-- | configuration of the transition system

data AexpConfig = Redex Aexp State  -- a redex is a reducible expression
                | Value Z           -- a value is not reducible; it is in normal form


-- |----------------------------------------------------------------------
-- | Exercise 4.1
-- |----------------------------------------------------------------------

-- | Define a function 'sosAexp' that given a configuration 'AexpConfig'
-- | evaluates the expression in 'AexpConfig' one step and returns the
-- | next configuration.

sosAexp :: AexpConfig -> AexpConfig

-- n
sosAexp (Redex (N n) _) = Value n

-- x
sosAexp (Redex (V x) s) = Redex (N (s x)) s

-- a1 + a2
sosAexp (Redex (Add (N n1) (N n2)) s) =  Redex (N (n1 + n2)) s

sosAexp (Redex (Add (N n) a2) s) = Redex (Add (N n) a2') s'
  where
    Redex a2' s' = sosAexp (Redex a2 s)

sosAexp (Redex (Add a1 a2) s) = Redex (Add a1' a2) s'
  where
    Redex a1' s' = sosAexp (Redex a1 s)

-- a1 * a2
sosAexp (Redex (Mult (N n1) (N n2)) s) =  Redex (N (n1 + n2)) s

sosAexp (Redex (Mult (N n) a2) s) = Redex (Mult (N n) a2') s'
  where
    Redex a2' s' = sosAexp (Redex a2 s)

sosAexp (Redex (Mult a1 a2) s) = Redex (Mult a1' a2) s'
  where
    Redex a1' s' = sosAexp (Redex a1 s)
-- a1 - a2

sosAexp (Redex (Sub (N n1) (N n2)) s) =  Redex (N (n1 + n2)) s

sosAexp (Redex (Sub (N n) a2) s) = Redex (Sub (N n) a2') s'
  where
    Redex a2' s' = sosAexp (Redex a2 s)

sosAexp (Redex (Sub a1 a2) s) = Redex (Sub a1' a2) s'
  where
    Redex a1' s' = sosAexp (Redex a1 s)

-- |----------------------------------------------------------------------
-- | Exercise 4.2
-- |----------------------------------------------------------------------

-- | Given the type synonym 'AexpDerivSeq' to represent derivation sequences
-- | of the structural operational semantics for arithmetic expressions 'Aexp':

type AexpDerivSeq = [AexpConfig]

-- | Define a function 'aExpDerivSeq' that given a 'Aexp' expression 'a' and an
-- | initial state 's' returns the corresponding derivation sequence:

aExpDerivSeq :: Aexp -> State -> AexpDerivSeq
aExpDerivSeq (N n) s = (Redex (N n) s):[sosAexp (Redex (N n) s)]
aExpDerivSeq (V x) s = (Redex (V x) s):(aExpDerivSeq a' s')
  where
    Redex a' s' = sosAexp (Redex (V x) s)
aExpDerivSeq a s = (Redex a s):(aExpDerivSeq a' s')
  where
    Redex a' s' = sosAexp (Redex a s)

-- | To test your code, you can use the function 'showAexpDerivSeq' that
-- | returns a String representation  of a derivation sequence 'dseq':

showAexpDerivSeq :: [Var] -> AexpDerivSeq -> String
showAexpDerivSeq vars dseq = unlines (map showConfig dseq)
  where
    showConfig (Value n) = "Final value:\n" ++ show n
    showConfig (Redex ss s) = show ss ++ "\n" ++ unlines (map (showVal s) vars)
    showVal s x = " s(" ++ x ++ ")= " ++ show (s x)

-- | Therefore, you can print the derivation sequence of an 'Aexp' with:

exp1 :: Aexp
exp1 = ( (V "x") `Add` (V "y") ) `Add` (V "z")

exp2 :: Aexp
exp2 =  (V "x") `Add` ( (V "y") `Add` (V "z") )

exp3 :: Aexp
exp3 = Mult (V "x") (Add (V "y") (Sub (V "z") (N 1)))

sExp :: State
sExp "x" = 1
sExp "y" = 2
sExp "z" = 3
sExp  _  = 0

showAexpSeq :: Aexp -> State -> IO()
showAexpSeq a s = putStrLn $ showAexpDerivSeq ["x", "y", "z"] (aExpDerivSeq a s)

-- | Test you code printing derivation sequences for the expressions above as follows:

showExp1 :: IO ()
showExp1 = showAexpSeq exp1 sExp

-- | For the example above, you should get an output identical to 'derivSeqForExp1.txt'

-- |----------------------------------------------------------------------
-- | Exercise 5
-- |----------------------------------------------------------------------

-- | Implement in Haskell the Structural Operational Semantics for the
-- | parallel evaluation of arithmetic expressions 'Aexp'.

{-
   Structural Operational Semantics for the parallel evaluation of arithmetic
   expressions:

   [N]  ----------------
         < n, s > => n

   [V] ------------------------
        < x, s > => < s x, s >

   [+] -----------------------------  where n3 = n1 + n2
        < n1 + n2, s > => < n3, s >

            < a1, s > => < a1', s >
   [+] -----------------------------------
        < a1 + a2, s > => < a1' + a2, s >

            < a2, s > => < a2', s >
   [+] ----------------------------------
        < a1 + a2, s > => <a1 + a2', s >

   The rules for * and - are similar.

-}

-- | Define a function 'sosAexp'' that given a configuration 'AexpConfig'
-- | evaluates the expression in 'AexpConfig' one step and returns a list
-- | with the next configurations.
-- | Note that given an arithmetic expression, a parallel evaluation strategy
-- | can lead to more than one configuration. For example, the following
-- | arithmetic expression 'example':

example :: [AexpConfig]
example = sosAexp' (Redex (Add (Add (Add (N 1) (N 2)) (Add (N 3) (N 4))) (Add (Add (N 5) (N 6)) (Add (N 7) (N 8)))) sInit)

-- | can lead to 4 next configurations:

{-
*Exercises03> showConfigs example
["Add (Add (N 3) (Add (N 3) (N 4))) (Add (Add (N 5) (N 6)) (Add (N 7) (N 8)))",
 "Add (Add (Add (N 1) (N 2)) (N 7)) (Add (Add (N 5) (N 6)) (Add (N 7) (N 8)))",
 "Add (Add (Add (N 1) (N 2)) (Add (N 3) (N 4))) (Add (N 11) (Add (N 7) (N 8)))",
 "Add (Add (Add (N 1) (N 2)) (Add (N 3) (N 4))) (Add (Add (N 5) (N 6)) (N 15))"]
-}

showConfigs :: [AexpConfig] -> [String]
showConfigs = map showConfig
   where
     showConfig (Redex a _) = show a
     showConfig (Value n) = show n



-------------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------------
-- Parallel Structural Operational Semantics for Aexp
-------------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------------
sosAexp' :: AexpConfig -> [AexpConfig]

-- n
sosAexp' (Redex (N n) _) = [Value n]

-- x
sosAexp' (Redex (V x) s) = sosAexp' (Redex (N (s x)) s)

-- a1 + a2
sosAexp' (Redex (Add (N n1) (N n2)) s) = [Redex (N (n1 + n2)) s]

sosAexp' (Redex (Add a1 a2) s) = [Redex (Add a1' a2) s | (Redex a1' _) <- sosAexp' (Redex a1 s)] ++ [Redex (Add a1 a2') s | (Redex a2' _) <- sosAexp' (Redex a2 s)]

-- a1 * a2

sosAexp' (Redex (Mult (N n1) (N n2)) s) = [Redex (N (n1 + n2)) s]

sosAexp' (Redex (Mult a1 a2) s) = [Redex (Mult a1' a2) s | (Redex a1' _) <- sosAexp' (Redex a1 s)] ++ [Redex (Mult a1 a2') s | (Redex a2' _) <- sosAexp' (Redex a2 s)]

-- a1 - a2

sosAexp' (Redex (Sub (N n1) (N n2)) s) = [Redex (N (n1 + n2)) s]

sosAexp' (Redex (Sub a1 a2) s) = [Redex (Sub a1' a2) s | (Redex a1' _) <- sosAexp' (Redex a1 s)] ++ [Redex (Sub a1 a2') s | (Redex a2' _) <- sosAexp' (Redex a2 s)]



-------------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------------
-- Structural Operational Semantics for Bexp
-------------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------------
data BexpConfig = RedexB Bexp State  -- a redex is a reducible expression
                | ValueB Bool           -- a value is not reducible; it is in normal form

sosBexp :: BexpConfig -> BexpConfig
sosBexp (RedexB TRUE _) = ValueB True
sosBexp (RedexB FALSE _) = ValueB False

sosBexp (RedexB (Eq a1 a2) s) 
  | (aVal a1 s) == (aVal a2 s) = RedexB TRUE s
  | otherwise = RedexB FALSE s


sosBexp (RedexB (Le a1 a2) s) 
  | (aVal a1 s) <= (aVal a2 s) =  RedexB TRUE s
  | otherwise = RedexB FALSE s


sosBexp (RedexB (Neg TRUE) s) = RedexB FALSE s
sosBexp (RedexB (Neg FALSE) s) = RedexB TRUE s


sosBexp (RedexB (Neg b) s) = RedexB (Neg b') s
  where 
    RedexB b' s= sosBexp (RedexB b s) -- It cannot be a ValueB because we have the previous rule


sosBexp (RedexB (And TRUE b2) s) = RedexB b2 s

sosBexp (RedexB (And FALSE b2) s) = RedexB FALSE s

sosBexp (RedexB (And b1 b2) s) = RedexB (And b1' b2) s
  where
    RedexB b1' s = sosBexp (RedexB b1 s)

-- | Given the type synonym 'BexpDerivSeq' to represent derivation sequences
-- | of the structural operational semantics for arithmetic expressions 'Bexp':

type BexpDerivSeq = [BexpConfig]

-- | Define a function 'aExpDerivSeq' that given a 'Bexp' expression 'b' and an
-- | initial state 's' returns the corresponding derivation sequence:

bExpDerivSeq :: Bexp -> State -> BexpDerivSeq
bExpDerivSeq TRUE s = (RedexB TRUE s):[sosBexp (RedexB TRUE s)]
bExpDerivSeq FALSE s = (RedexB FALSE s):[sosBexp (RedexB FALSE s)]

bExpDerivSeq (Eq e1 e2) s = (RedexB (Eq e1 e2) s):(bExpDerivSeq a' s')
  where
    RedexB a' s' = sosBexp (RedexB (Eq e1 e2) s)

bExpDerivSeq (Le e1 e2) s = (RedexB (Le e1 e2) s):(bExpDerivSeq a' s')
  where
    RedexB a' s' = sosBexp (RedexB (Le e1 e2) s)

bExpDerivSeq b s = (RedexB b s):(bExpDerivSeq b' s')
  where
    RedexB b' s' = sosBexp (RedexB b s)

-- | To test your code, you can use the function 'showBexpDerivSeq' that
-- | returns a String representation  of a derivation sequence 'dseq':

showBexpDerivSeq :: [Var] -> BexpDerivSeq -> String
showBexpDerivSeq vars dseq = unlines (map showConfig dseq)
  where
    showConfig (ValueB n) = "Final value:\n" ++ show n
    showConfig (RedexB ss s) = show ss ++ "\n" ++ unlines (map (showVal s) vars)
    showVal s x = " s(" ++ x ++ ")= " ++ show (s x)

-- | Therefore, you can print the derivation sequence of an 'Bexp' with:

bexp1 :: Bexp
bexp1 = TRUE

bexp2 :: Bexp
bexp2 = FALSE

bexp3 :: Bexp
bexp3 = (Eq (N 1) (N 1))

bexp4 :: Bexp
bexp4 = (Eq (N 1) (N 2))

bexp5 :: Bexp
bexp5 = (Le (N 1) (N 2))

bexp6 :: Bexp
bexp6 = (Le (N 2) (N 1))

bexp7 :: Bexp
bexp7 = (Neg bexp6)

bexp8 :: Bexp
bexp8 = (And bexp3 bexp5)

showBexpSeq :: Bexp -> State -> IO()
showBexpSeq b s = putStrLn $ showBexpDerivSeq [] (bExpDerivSeq b s)


-- | Test you code printing derivation sequences for the expressions above as follows:

showBexp4 :: IO ()
showBexp4 = showBexpSeq bexp8 sExp