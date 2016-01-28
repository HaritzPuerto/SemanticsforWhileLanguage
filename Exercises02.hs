{-|

Programming Languages
Fall 2015

Implementation in Haskell of the Natural Semantics described in Chapter 2 of
Nielson & Nielson, Semantics with Applications

Author: Haritz Puerto-San-Roman

-}

module Exercises02 where

import While
import NaturalSemantics
import Exercises01
import Test.HUnit hiding (State)
import Data.List

-- |----------------------------------------------------------------------
-- | Exercise 1
-- |----------------------------------------------------------------------
-- | The function 'sNs' returns the final state of the execution of a
-- |  WHILE statement 'st' from a given initial state 's'. For example:
-- |
-- |  sNs factorial sInit
-- |
-- | returns the final state:
-- |
-- |    s x = 1
-- |    s y = 6
-- |    s _ = 0
-- |
-- | Since a state is a function it cannot be printed thus you cannot
-- | add 'deriving Show' to the algebraic data type 'Config'.
-- | The goal of this exercise is to define a number of functions to
-- | "show" a state thus you can inspect the final state yield by the
-- | natural semantics of WHILE.

-- | Exercise 1.1
-- | Define a function 'showState' that given a state 's' and a list
-- | of variables 'vs' returns a list of strings showing the bindings
-- | of the variables  mentioned in 'vs'. For example, for the state
-- | 's' above we get:
-- |
-- |    showState s ["x"] = ["x -> 1"]
-- |    showState s ["y"] = ["y -> 6"]
-- |    showState s ["x", "y"] = ["x -> 1", "y -> 6"]
-- |    showState s ["y", "z", "x"] = ["y -> 6", "z -> 0", "x -> 1"]

showState :: State -> [Var] -> [String]
showState s [] = []
showState s (x:xs) = [x ++ " -> " ++ (show $ s x)] ++ showState s xs

-- | Test your function with HUnit.

testShowState :: Test
testShowState = test["showState sInit x" ~: ["x -> 3"] ~=? showState sInit ["x"]]

-- | Exercise 1.2
-- | Define a function 'fvStm' that returns the free variables of a WHILE
-- | statement. For example:
-- |
-- | fvStm factorial = ["y","x"]
-- |
-- | Note: the order of appearance is not relevant.

fvStm :: Stm -> [Var]
fvStm (Skip) = []
fvStm (Ass v a) = nub $ v:(fvAexp' a)
fvStm (Comp s1 s2) = nub $ (fvStm s1) ++ (fvStm s2)
fvStm (If b s1 s2) = nub $ (fvBexp' b) ++ (fvStm s1) ++ (fvStm s2)
fvStm (While b s) = nub $ (fvBexp' b) ++ (fvStm s)
fvStm (Repeat s b) = nub $ (fvStm s) ++  (fvBexp' b)

-- | Test your function with HUnit. Beware the order or appearance.
testFvStm :: Test
testFvStm = test["fvStm factorial" ~: ["y", "x"] ~=? fvStm factorial]

-- | Exercise 1.3
-- | Define a function 'showFinalState' that given a WHILE statement and a
-- | initial state returns a list of strings with the bindings of
-- | the free variables of the statement in the final state. For
-- | example:
-- |
-- |  showFinalState factorial sInit = ["y->6","x->1"]

showFinalState :: Stm -> State -> [String]
showFinalState st s = showState s' vars
	where
		s' = sNs st s
		vars = fvStm st

-- | Test your function with HUnit. Beware the order or appearance.

testShowFinalState :: Test
testShowFinalState = test ["showFinalState factorial sInit" ~: ["y -> 6","x -> 1"] ~=? showFinalState factorial sInit]
-- |----------------------------------------------------------------------
-- | Exercise 2
-- |----------------------------------------------------------------------
-- | Write a program in WHILE to compute z = x^y and check it by obtaining a
-- | number of final states.

power = undefined -- WHILE statement to compute z = x^y

-- | Test your function with HUnit. Inspect the final states of at least
-- | four different executions.


-- |----------------------------------------------------------------------
-- | Exercise 3
-- |----------------------------------------------------------------------
-- | The WHILE language can be extended with a 'repeat S until b' construct.

-- | Exercise 3.1
-- | Define the natural semantics of this new construct. You are not allowed
-- | to rely on the 'while b do S' statement.

{- Formal definition of 'repeat S until b'


        [repeat-ff]  ------------------------------   ¿condition?




        [repeat-tt]  ------------------------------   ¿condition?


-}

-- | Extend the definitions of data type 'Stm' (in module While.hs) and
-- | 'nsStm' (in module NaturalSemantics.hs) to include the 'repeat S until b'
-- | construct. Write a couple of WHILE programs that use the 'repeat' statement
-- | and test your functions with HUnit.
sum3 :: Stm 
sum3 = Comp (Ass "x" (N 0))
             (Repeat 
              (Ass "x" (Add (V "x") (N 1))) (Eq (V "x") (N 3)))


testSum3 :: Test
testSum3 = test ["sum3 sInit --> x = 3"  ~: ["x -> 3"] ~=? showFinalState sum3 sInit]


-- |----------------------------------------------------------------------
-- | Exercise 4
-- |----------------------------------------------------------------------

-- | Define the semantics of arithmetic expressions (Aexp) by means of
-- | natural semantics. To that end, define an algebraic datatype 'ConfigAexp'
-- | to represent the configurations, and a function 'nsAexp' to represent
-- | the transition relation.

-- representation of configurations for Aexp

-- data ConfigAExp = ...

-- representation of the transition relation <A, s> -> s'
data ConfigAexp = NonTerminal Aexp State 
	   			| Terminal Z

nsAexp :: ConfigAexp -> ConfigAexp
nsAexp (NonTerminal (N n) _) = Terminal n
nsAexp (NonTerminal (V x) s) = Terminal (s x)
nsAexp (NonTerminal (Add x y) s) = Terminal z
	where
		Terminal z1 = nsAexp (NonTerminal x s)
		Terminal z2 = nsAexp (NonTerminal y s) 
		z = z1 + z2
nsAexp (NonTerminal (Mult x y) s) = Terminal z
	where
		Terminal z1 = nsAexp (NonTerminal x s) 
		Terminal z2 = nsAexp (NonTerminal y s)
		z = z1 * z2
nsAexp (NonTerminal (Sub x y) s) = Terminal z
	where
		Terminal z1 = nsAexp (NonTerminal x s)
		Terminal z2 = nsAexp (NonTerminal y s)
		z = z1 - z2

aNs ::  Aexp -> State -> Z
aNs x s = s'
  where Terminal s' = nsAexp (NonTerminal x s)
-- | Test your function with HUnit. Inspect the final states of at least
-- | four different evaluations.

stateInvar::State
stateInvar "x" = 9
stateInvar _   = 0

aexp1 :: Aexp
aexp1 = (Add (V "x") (N 1))

aexp2 :: Aexp
aexp2 = (N 1)

aexp3 :: Aexp
aexp3 = (Add (Mult (N 1) (N 2)) (V "x"))

aexp4 :: Aexp 
aexp4 = (Mult (N 10) (N 2))



testAexps :: Test
testAexps = test ["aexp1  = 10"  ~: 10 ~=? aNs aexp1 stateInvar,
                  "aexp2 = 1"    ~: 1 ~=? aNs aexp2 stateInvar,
                  "aexp3 = 2+9"  ~: 11 ~=? aNs aexp3 stateInvar,
                  "aexp4 = 20"   ~: 20 ~=? aNs aexp4 stateInvar,
                  "aNs (Sub (N 5) (N 5)) sInit = 0" ~: 0 ~=? aNs (Sub (N 5) (N 5)) sInit
                  ]

-- |----------------------------------------------------------------------
-- | Exercise 5
-- |----------------------------------------------------------------------

-- | Given the algebraic data type 'DerivTree' to represent derivation trees
-- | of the natural semantics:

data Transition = Config :-->:  State

data DerivTree = AssNS     Transition
               | SkipNS    Transition
               | CompNS    Transition DerivTree DerivTree
               | IfTTNS    Transition DerivTree
               | IfFFNS    Transition DerivTree
               | WhileTTNS Transition DerivTree DerivTree
               | WhileFFNS Transition
               | RepeatTTNS Transition DerivTree 
               | RepeatFFNS Transition DerivTree DerivTree

-- | and the function 'getFinalState' to access the final state of the root
-- | of a derivation tree:

getFinalState :: DerivTree -> State
getFinalState (AssNS  (_ :-->: s)) = s
getFinalState (SkipNS (_ :-->: s)) = s
getFinalState (CompNS (_ :-->: s) _ _ ) = s
getFinalState (IfTTNS (_ :-->: s) _ ) = s
getFinalState (IfFFNS (_ :-->: s) _ ) = s
getFinalState (WhileTTNS (_ :-->: s) _ _ ) = s
getFinalState (WhileFFNS (_ :-->: s)) = s
getFinalState (RepeatTTNS (_ :-->: s) _) = s
getFinalState (RepeatFFNS (_ :-->: s) _ _) = s


-- | Define a function 'nsDeriv' that given a WHILE statement 'st' and an
-- | initial state 's' returns corresponding derivation tree.

nsDeriv :: Stm -> State -> DerivTree
nsDeriv Skip s = SkipNS ((Inter Skip s) :-->: s)
nsDeriv (Ass v a) s = AssNS ((Inter (Ass v a) s) :-->: (sNs (Ass v a) s))
nsDeriv (Comp s1 s2) s = CompNS ( (Inter (Comp s1 s2) s) :-->: (sNs (Comp s1 s2) s))  (nsDeriv s1 s) (nsDeriv s2 s)
nsDeriv (If b s1 s2) s 
	| bVal b s = IfTTNS ( (Inter (If b s1 s2) s) :-->: (sNs (If b s1 s2) s)) (nsDeriv s1 s)
	| otherwise = IfFFNS ( (Inter (If b s1 s2) s) :-->: (sNs (If b s1 s2) s)) (nsDeriv s2 s)
nsDeriv (While b st) s 
	| bVal b s = WhileTTNS ((Inter (While b st) s ) :-->: (sNs (While b st) s)) (nsDeriv st s) (nsDeriv (While b st) s)
	| otherwise = WhileFFNS ((Inter (While b st) s ) :-->: (sNs (While b st) s))
nsDeriv (Repeat st b) s
	| bVal b s' = RepeatTTNS ((Inter (Repeat st b) s) :-->: s') (nsDeriv st s)
	| otherwise = RepeatFFNS ((Inter (Repeat st b) s) :-->: (sNs (Repeat st b) s')) (nsDeriv st s) (nsDeriv (Repeat st b) s')
	where
		s' = sNs st s


