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
updateV envV x l  y 
	| x == y = l
	| otherwise = envV y

-- update a store with a new binding sto [l -> v]
updateS :: Store -> Loc -> Z -> Store
updateS sto l v l'
	| l == l' = v
	| otherwise = sto l'

-- variable declaration configurations

data ConfigD = InterD DecVar EnvVar Store  -- <Dv, envV, store>
             | FinalD EnvVar Store         -- <envV, store>

nsDecV :: ConfigD -> ConfigD

-- | Exercise 1.2

-- var x := a
nsDecV (InterD (Dec x a decs) envV store) = nsDecV (InterD decs envV' sto'')
	where
		l = store next
		envV' = updateV envV x l 
		sto' = updateS store l (aVal a (store . envV))
		sto'' = updateS sto' next (new l)

-- epsilon
nsDecV (InterD EndDec envV store) = FinalD envV store

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
updP (Proc p s procs) envV envP = updP procs envV (EnvP p s envV envP envP)
updP EndProc envV envP = envP

-- | Exercise 2.2

-- lookup procedure p
envProc :: EnvProc -> Pname -> (Stm, EnvVar, EnvProc)
envProc (EnvP q s envV envP envs) p 
	| p == q = (s, envV, envP)
	| otherwise = envProc envs p
envProc EmptyEnvProc p = error "undefined procedure"

-- representation of configurations for Proc

data Config = Inter Stm Store  -- <S, sto>
            | Final Store      -- sto

-- representation of the transition relation <S, sto> -> stos'

nsStm :: EnvVar -> EnvProc -> Config -> Config

-- | Exercise 3.1

-- x := a

nsStm envV envP (Inter (Ass x a) sto) = Final sto'
	where
		sto' = updateS sto l v
		l = envV x
		v = aVal a (sto . envV)


-- skip

nsStm envV envP (Inter Skip sto) = Final sto


-- s1; s2

nsStm envV envP (Inter (Comp ss1 ss2) sto) = Final sto''
	where
		Final sto' = nsStm envV envP (Inter ss1 sto)
		Final sto'' = nsStm envV envP (Inter ss2 sto')

-- if b then s1 else s2

nsStm envV envP (Inter (If b s1 s2) sto) 
	| bVal b (sto . envV) = Final sto1
	| otherwise = Final sto2
	where
		Final sto1 = nsStm envV envP (Inter s1 sto)
		Final sto2 = nsStm envV envP (Inter s2 sto)

-- while b do s

nsStm envV envP (Inter (While b s) sto)
	| bVal b (sto . envV) = Final sto''
 	| otherwise = Final sto
 		where
 			Final sto' = nsStm envV envP (Inter s sto)
 			Final sto'' = nsStm envV envP (Inter (While b s) sto')


nsStm envV envP (Inter (Block vars procs s) sto) = Final sto''
	where
		FinalD envV' sto' = nsDecV (InterD vars envV sto)
		envP' = updP procs  envV' envP
		Final sto'' = nsStm envV' envP' (Inter s sto')

-- non-recursive procedure call
{-
nsStm envV envP (Inter (Call p) sto) = Final sto'
	where
		Final sto' = nsStm envV' envP' (Inter s sto)
		(s, envV', envP') = envProc envP p 
-}




-- recursive procedure call
nsStm envV envP (Inter (Call p) sto) = Final sto'
	where
		Final sto' = nsStm envV' envP'' (Inter s sto)
		(s, envV', envP') = envProc envP p
		envP'' = updP (Proc p s EndProc)  envV' envP'


-- For x:= a1 to a2 do S statement
nsStm envV envP (Inter (For x a1 a2 stm) sto) 
	| (aVal a1 (sto . envV)) <= (aVal a2 (sto . envV)) = Final finalSto
	| otherwise = Final sto
	where
		decv = Dec x a1 EndDec 
		FinalD envV' sto' = nsDecV (InterD decv envV sto) -- New scope for the for block
		Final sto'' = nsStm envV' envP (Inter (Ass x a1) sto') -- x := a1
		Final sto''' = nsStm envV' envP (Inter stm sto'') -- execute the statement
		Final finalSto = nsStm envV' envP (Inter (For x (Add (V x) (N 1)) a2 stm) sto''') -- for x := x +1 to a2 do stm


-- Repeat S until b
nsStm envV envP (Inter (Repeat stm b) sto) 
	| bVal b (sto' . envV) = Final sto'
	| otherwise = Final sto''
		where
			Final sto' = nsStm envV envP (Inter stm sto)
			Final sto'' = nsStm envV envP (Inter (Repeat stm b) sto')

-- | Exercise 3.2

sNs :: Stm -> Store -> Store
sNs s sto = sto'
	where
		Final sto' = nsStm emptyEnvV emptyEnvP (Inter s sto)

emptyEnvV :: EnvVar
emptyEnvV x = error $ "undefined variable " ++ x

emptyEnvP :: EnvProc
emptyEnvP = EmptyEnvProc