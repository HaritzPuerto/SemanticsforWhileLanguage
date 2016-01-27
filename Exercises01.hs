{-|

Programming Languages
Fall 2015

Implementation in Haskell of the concepts covered in Chapter 1 of
Nielson & Nielson, Semantics with Applications

Author: Haritz Puerto-San-Roman

-}

module Exercises01 where

import While
import Test.HUnit hiding (State)
import Data.List

-- |----------------------------------------------------------------------
-- | Exercise 1
-- |----------------------------------------------------------------------
-- | Given the algebraic data type 'Bin' for the binary numerals:

data Bit = O
         | I
         deriving Show

data Bin = MSB Bit
         | B Bin Bit

-- | and the following values of type 'Bin':

zero :: Bin
zero = MSB O

one :: Bin
one = MSB I

three :: Bin
three = B (B (MSB O) I) I

six :: Bin
six = B (B (MSB I) I) O

-- | define a semantic function 'binVal' that associates
-- | a binary number (Bin) to a decimal number.

binVal :: Bin -> Z
binVal (MSB O) = 0
binVal (MSB I) = 1
binVal (B b O) = 2*(binVal b)
binVal (B b I) = 2*(binVal b) + 1

-- | Test your function with HUnit.

testBinVal :: Test
testBinVal = test ["value of zero"  ~: 0 ~=? binVal zero,
                   "value of one"   ~: 1 ~=? binVal one,
                   "value of three" ~: 3 ~=? binVal three,
                   "value of six"   ~: 6 ~=? binVal six]

-- | If you dare, define a function 'foldBin' to fold a value of type 'Bin'

foldBin :: (Bit -> Z -> Z) -> Z -> Bin -> Z
foldBin f base x = solve x
	where
		solve (MSB z) = z `f` base
		solve (B x z) = z `f` (solve x)


fbin :: Bit -> Z -> Z
fbin O x = 2 * x
fbin I x = 1 + 2 * x


-- | and use 'foldBin' to define a function 'binVal''  equivalent to 'binVal'

binVal' :: Bin -> Integer
binVal' b = foldBin fbin 0 b

-- | Test your function with HUnit.

testBinVal' :: Test
testBinVal' = test ["value of zero" ~: 0 ~=? binVal' zero,
					"value of one"   ~: 1 ~=? binVal one,
                    "value of three" ~: 3 ~=? binVal three,
                    "value of six"   ~: 6 ~=? binVal six]

-- |----------------------------------------------------------------------
-- | Exercise 2
-- |----------------------------------------------------------------------
-- | Define the function 'fvAexp' that computes the set of free variables
-- | occurring in an arithmetic expression. Ensure that each free variable
-- | occurs once in the resulting list.

fvAexp :: Aexp -> [Var]
fvAexp (N x) = []
fvAexp (V x) = [x]
fvAexp (Add x y) = nub $ (fvAexp x) ++ (fvAexp y)
fvAexp (Mult x y) = nub $ (fvAexp x) ++ (fvAexp y)
fvAexp (Sub x y) = nub $ (fvAexp x) ++ (fvAexp y)

-- nub is available at Data.List It removes repeated elements
removeRepeatedElems :: Eq a => [a] -> [a]
removeRepeatedElems [] = []
removeRepeatedElems (x:xs)
	| elem x xs = xs
	| otherwise = x:xs

-- | Test your function with HUnit.

testfvAexp :: Test
testfvAexp = test ["FV(x)" ~: ["x"] ~=? fvAexp (V "x"),
				   "FV(5)" ~: [] ~=? fvAexp (N 5),
				   "FV(x + 3)" ~: ["x"] ~=? fvAexp (Add (V "x") (N 3)),
				   "FV(x * 3)" ~: ["x"] ~=? fvAexp (Mult (V "x") (N 3)),
				   "FV(x - y)" ~: ["x", "y"] ~=? fvAexp (Add (V "x") (V "y"))]

-- | Define the function 'fvBexp' that computes the set of free variables
-- | occurring in a Boolean expression.
fvBexp :: Bexp -> [Var]
fvBexp TRUE = []
fvBexp FALSE = []
fvBexp (Eq x y) = nub $ (fvAexp x) ++ (fvAexp y)
fvBexp (Le x y) = nub $ (fvAexp x) ++ (fvAexp y)
fvBexp (Neg b) = nub $ (fvBexp b)
fvBexp (And b bb) = nub $ (fvBexp b) ++ (fvBexp bb) 


-- | Test your function with HUnit.

testfvBexp :: Test
testfvBexp = test ["FV(TRUE)" ~: ["x"] ~=? fvBexp TRUE,
				   "FV(FALSE)" ~: [] ~=? fvBexp FALSE,
				   "FV((Eq (V x) (V y) ))" ~: ["x", "y"] ~=? fvBexp (Eq (V "x") (V "y") ),
				   "FV((Le (V x) (V y) ))" ~: ["x", "y"] ~=? fvBexp ((Le (V "x") (V "y") )),
				   "FV((Neg (Eq (V x) (V y) )))" ~: ["x", "y"] ~=? fvBexp (Neg (Eq (V "x") (V "y") )),
				   "FV((And (Eq (V x) (V y) ) (Eq (V x) (V y) ) ))" ~: ["x", "y"] ~=? fvBexp (And (Eq (V "x") (V "y") ) (Eq (V "x") (V "y") )) ]
-- |----------------------------------------------------------------------
-- | Exercise 3
-- |----------------------------------------------------------------------
-- | Given the algebraic data type 'Subst' for representing substitutions:

data Subst = Var :->: Aexp

-- | define a function 'substAexp' that takes an arithmetic expression
-- | 'a' and a substitution 'y:->:a0' and returns the substitution a [y:->:a0];
-- | i.e., replaces every occurrence of 'y' in 'a' by 'a0'.

substAexp :: Aexp -> Subst -> Aexp
substAexp (N x) _ = (N x)
substAexp (V x) (y:->:a0) 
			| x == y = a0
			| otherwise = (V x)
substAexp (Add a1 a2) s = Add (substAexp a1 s) (substAexp a2 s)
substAexp (Mult a1 a2) s = Mult (substAexp a1 s) (substAexp a2 s)
substAexp (Sub a1 a2) s = Sub (substAexp a1 s) (substAexp a2 s)

testSubstAexp :: Test
testSubstAexp = test ["5 [y:->:x]" ~: (N 5) ~=? substAexp (N 5) ("y":->: (V "x")),
					  "y [y:->:x]" ~: (V "x") ~=? substAexp (V "y") ("y":->: (V "x")),
					  "y [z:->:x]" ~: (V "y") ~=? substAexp (V "y") ("z":->: (V "x")),
					  "(Add (N 5) (V y)) [y:->:x]" ~: (Add (N 5) (V "x")) ~=? substAexp (Add (N 5) (V "y")) ("y":->: (V "x")),
					  "(Mult (N 5) (V y)) [y:->:x]" ~: (Mult (N 5) (V "x")) ~=? substAexp (Mult (N 5) (V "y")) ("y":->: (V "x")),
					  "(Sub (N 5) (V y)) [y:->:x]" ~: (Sub (N 5) (V "x")) ~=? substAexp (Sub (N 5) (V "y")) ("y":->: (V "x"))]

-- | Define a function 'substBexp' that implements substitution for
-- | Boolean expressions.

substBexp :: Bexp -> Subst -> Bexp 
substBexp TRUE _ = TRUE
substBexp FALSE _ = FALSE
substBexp (Eq x y) subs =  (Eq (substAexp x subs) (substAexp y subs))
substBexp (Le x y) subs = (Le (substAexp x subs) (substAexp y subs))
substBexp (Neg b) subs = (Neg (substBexp b subs))
substBexp (And b bb) subs = (And (substBexp b subs) (substBexp bb subs))

-- | Test your function with HUnit.
testsubstBexp :: Test
testsubstBexp = test ["sInit [y:->:x]" ~: TRUE ~=? substBexp TRUE ("y":->: (V "x")),
					  "FALSE [y:->:x]" ~: FALSE ~=? substBexp FALSE ("y":->: (V "x")),
					  "(a1 == a2) [y:->:x]" ~: (Eq (V "x") (N 5) ) ~=? substBexp (Eq (V "y") (N 5) ) ("y":->: (V "x")),
					  "(a1 < a2) [y:->:x]" ~: (Le (V "x") (N 5) ) ~=? substBexp (Le (V "y") (N 5) ) ("y":->: (V "x")),
					  "(! (a1 == a2) ) [y:->:x]" ~: (Neg (Eq (V "x") (N 5) )) ~=? substBexp (Eq (V "y") (N 5) ) ("y":->: (V "x")),
					  "(AND TRUE (V y)) [y:->:x]" ~: (And (Eq (V "z") (N 5) ) (Le (V "x") (N 5) )) ~=? substBexp (And (Eq (V "z") (N 5) ) (Le (V "y") (N 5) )) ("y":->: (V "x"))]


-- |----------------------------------------------------------------------
-- | Exercise 4
-- |----------------------------------------------------------------------
-- | Given the algebraic data type 'Update' for state updates:

data Update = Var :=>: Z

-- | define a function 'update' that takes a state 's' and an update 'x :=>: v'
-- | and returns the updated state 's [x :=> y]'

update :: State -> Update -> State
update s (x :=>: v) y
	| x == y = v
	| otherwise = s y

testUpdate :: Test
testUpdate = test ["sInit [x:=>:5]" ~: 5 ~=? (update sInit ("x":=>: 5)) "x",
					  "sInit [y:=>:5]" ~: 3 ~=? (update sInit ("y":=>: 5)) "x"]
					  

-- | Define a function 'updates' that takes a state 's' and a list of updates
-- | 'us' and returns the updated states resulting from applying the updates
-- | in 'us' from head to tail. For example:
-- |
-- |    updates s ["x" :=> 1, "y" :=> 2, "x" :=> 3]
-- |
-- | returns a state that binds "x" to 3 (the most recent update for "x").

updates :: State ->  [Update] -> State
updates s [] = s
updates s (x:xs) = updates (update s x) xs

-- |----------------------------------------------------------------------
-- | Exercise 5
-- |----------------------------------------------------------------------
-- | Define a function 'foldAexp' to fold an arithmetic expression

foldAexp :: (Integer -> a) ->
			(Var -> a) ->
			(a -> a -> a) ->
			(a -> a -> a) ->
			(a -> a -> a) ->
			Aexp ->
			a
foldAexp n v a m s exp = resolver exp
	where
		resolver (N const) = n const
		resolver (V x) = v x
		resolver (Add e1 e2) = a (resolver e1)  (resolver e2)
		resolver (Mult e1 e2) = m (resolver e1) (resolver e2)
		resolver (Sub e1 e2) = s (resolver e1) (resolver e2)

-- | Use 'foldAexp' to fefine the functions 'aVal'', 'fvAexp'', and 'substAexp''
-- | and test your definitions with HUnit.
aVal' :: Aexp -> State -> Z
aVal' e s = foldAexp (\n -> n) (\x -> s x) (\x1 x2 -> x1 + x2) (\x1 x2 -> x1 * x2) (\x1 x2 -> x1 - x2) e

fvAexp' :: Aexp -> [Var]
fvAexp' = foldAexp (\x -> []) (\x -> [x]) (\x1 x2 -> nub $  x1 ++ x2) (\x1 x2 -> nub $  x1 ++ x2) (\x1 x2 -> nub $  x1 ++ x2)


substAexp' :: Aexp -> Subst -> Aexp
substAexp' e s = foldAexp (\x -> (N x)) (subsVar s) (\x1 x2 -> (Add x1 x2)) (\x1 x2 -> (Mult x1 x2)) (\x1 x2 -> (Sub x1 x2)) e

subsVar :: Subst -> Var -> Aexp
subsVar (y:->:a0) x
	| x == y = a0
	| otherwise = (V x)

-- | Define a function 'foldBexp' to fold a Boolean expression and use it
-- | to define the functions 'bVal'', 'fvBexp'', and 'substAexp''. Test
-- | your definitions with HUnit.

foldBexp :: a
foldBexp = undefined

bVal' :: Bexp -> State -> Bool
bVal' = undefined

fvBexp' :: Bexp -> [Var]
fvBexp' = undefined

substBexp' :: Bexp -> Subst -> Bexp
substBexp' = undefined


