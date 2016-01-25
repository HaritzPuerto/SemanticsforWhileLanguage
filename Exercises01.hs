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

foldBin :: a
foldBin = undefined

-- | and use 'foldBin' to define a function 'binVal''  equivalent to 'binVal'

binVal' :: Bin -> Integer
binVal' = undefined

-- | Test your function with HUnit.

-- todo

-- |----------------------------------------------------------------------
-- | Exercise 2
-- |----------------------------------------------------------------------
-- | Define the function 'fvAexp' that computes the set of free variables
-- | occurring in an arithmetic expression. Ensure that each free variable
-- | occurs once in the resulting list.

fvAexp :: Aexp -> [Var]
fvAexp = undefined

-- | Test your function with HUnit.

-- todo

-- | Define the function 'fvBexp' that computes the set of free variables
-- | occurring in a Boolean expression.

fvBexp :: Bexp -> [Var]
fvBexp = undefined

-- | Test your function with HUnit.

-- todo

-- |----------------------------------------------------------------------
-- | Exercise 3
-- |----------------------------------------------------------------------
-- | Given the algebraic data type 'Subst' for representing substitutions:

data Subst = Var :->: Aexp

-- | define a function 'substAexp' that takes an arithmetic expression
-- | 'a' and a substitution 'y:->:a0' and returns the substitution a [y:->:a0];
-- | i.e., replaces every occurrence of 'y' in 'a' by 'a0'.

substAexp :: Aexp -> Subst -> Aexp
substAexp = undefined

-- | Test your function with HUnit.

-- todo

-- | Define a function 'substBexp' that implements substitution for
-- | Boolean expressions.

substBexp :: Bexp -> Subst -> Bexp
substBexp = undefined

-- | Test your function with HUnit.

-- todo

-- |----------------------------------------------------------------------
-- | Exercise 4
-- |----------------------------------------------------------------------
-- | Given the algebraic data type 'Update' for state updates:

data Update = Var :=>: Z

-- | define a function 'update' that takes a state 's' and an update 'x :=> v'
-- | and returns the updated state 's [x :=> y]'

update :: State -> Update -> State
update = undefined

-- | Test your function with HUnit.

-- todo

-- | Define a fuunction 'updates' that takes a state 's' and a list of updates
-- | 'us' and returns the updated states resulting from applying the updates
-- | in 'us' from head to tail. For example:
-- |
-- |    updates s ["x" :=> 1, "y" :=> 2, "x" :=> 3]
-- |
-- | returns a state that binds "x" to 3 (the most recent update for "x").

updates :: State ->  [Update] -> State
updates = undefined

-- |----------------------------------------------------------------------
-- | Exercise 5
-- |----------------------------------------------------------------------
-- | Define a function 'foldAexp' to fold an arithmetic expression

foldAexp :: a
foldAexp = undefined

-- | Use 'foldAexp' to fefine the functions 'aVal'', 'fvAexp'', and 'substAexp''
-- | and test your definitions with HUnit.

aVal' :: Aexp -> State -> Z
aVal' = undefined

fvAexp' :: Aexp -> [Var]
fvAexp' = undefined

substAexp' :: Aexp -> Subst -> Aexp
substAexp' = undefined

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


