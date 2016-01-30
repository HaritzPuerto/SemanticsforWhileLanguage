----------------------------------------------------------------------
--
-- ProcNaturalSemantics.hs
-- Programming Languages
-- Fall 2015
--
-- Natural Semantics for Proc
-- [Nielson and Nielson, semantics with applications]
--
-- Author: Haritz Puerto-San-Roman
----------------------------------------------------------------------

module ProcNaturalSemantics where

import Proc

----------------------------------------------------------------------
-- Variable Declarations
----------------------------------------------------------------------

-- locations

type Loc = Integer

new :: Loc -> Loc
new l = l + 1

-- variable environment

type EnvVar = Var -> Loc

-- store

-- 'sto[next]' refers to the first available cell in the store 'sto'
next :: Loc
next = 0

type Store = Loc -> Z

-- | Exercise 1.1

-- update a variable environment with a new binding envV [x -> l]
updateV :: EnvVar -> Var -> Loc -> EnvVar
updateV envV x l = undefined

-- update a store with a new binding sto [l -> v]
updateS :: Store -> Loc -> Z -> Store
updateS sto l v = undefined

-- variable declaration configurations

data ConfigD = InterD DecVar EnvVar Store  -- <Dv, envV, store>
             | FinalD EnvVar Store         -- <envV, store>

nsDecV :: ConfigD -> ConfigD

-- | Exercise 1.2

-- var x := a
nsDecV (InterD (Dec x a decs) envV store) = undefined

-- epsilon
nsDecV (InterD EndDec envV store) = undefined

----------------------------------------------------------------------
-- Procedure Declarations
----------------------------------------------------------------------

-- procedure environment

--                    p    s    snapshots    previous
--                    |    |     /    \         |
data EnvProc = EnvP Pname Stm EnvVar EnvProc EnvProc
             | EmptyEnvProc

-- | Exercise 2.1

-- update the procedure environment
updP :: DecProc -> EnvVar -> EnvProc -> EnvProc
updP (Proc p s procs) envV envP = undefined
updP EndProc envV envP = undefined

-- | Exercise 2.2

-- lookup procedure p
envProc :: EnvProc -> Pname -> (Stm, EnvVar, EnvProc)
envProc (EnvP q s envV envP envs) p = undefined
envProc EmptyEnvProc p = undefined

-- representation of configurations for Proc

data Config = Inter Stm Store  -- <S, sto>
            | Final Store      -- sto

-- representation of the transition relation <S, sto> -> stos'

nsStm :: EnvVar -> EnvProc -> Config -> Config

-- | Exercise 3.1

-- x := a

nsStm envV envP (Inter (Ass x a) sto) = undefined


-- skip

nsStm envV envP (Inter Skip sto) = undefined


-- s1; s2

nsStm envV envP (Inter (Comp ss1 ss2) sto) = undefined

-- if b then s1 else s2

nsStm envV envP (Inter (If b s1 s2) sto) = undefined

-- while b do s

nsStm envV envP (Inter (While b s) sto) = undefined


nsStm envV envP (Inter (Block vars procs s) sto) = undefined

-- non-recursive procedure call
{-
nsStm envV envP (Inter (Call p) sto) = undefined


-}

-- recursive procedure call
nsStm envV envP (Inter (Call p) sto) = undefined

-- | Exercise 3.2

sNs :: Stm -> Store -> Store
sNs s sto = undefined

