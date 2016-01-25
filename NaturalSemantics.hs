-- -------------------------------------------------------------------
--
-- NaturalSemantics.hs
--
-- An implementation of appendix C of
-- [Nielson and Nielson, semantics with applications]
--
-- -------------------------------------------------------------------

module NaturalSemantics where

import While


-- representation of configurations for While

data Config = Inter Stm State  -- <S, s>
            | Final State      -- s

-- representation of the transition relation <S, s> -> s'

nsStm :: Config -> Config

-- x := a

nsStm (Inter (Ass x a) s) = Final (update s x (aVal a s))
  where
    update s x v y = if x == y then v else s y

-- skip

nsStm (Inter Skip s) = Final s

-- s1; s2

nsStm (Inter (Comp ss1 ss2) s) = Final s''
  where
    Final s'  = nsStm (Inter ss1 s)
    Final s'' = nsStm (Inter ss2 s')

-- if b then s1 else s2

nsStm (Inter (If b ss1 ss2) s)
  | bVal b s = Final s'
  where
    Final s' = nsStm (Inter ss1 s)

nsStm (Inter (If b ss1 ss2) s)
  | not(bVal b s) = Final s'
  where
    Final s' = nsStm (Inter ss2 s)

-- while b do s

nsStm (Inter (While b ss) s)
  | bVal b s = Final s''
  where
    Final s'  = nsStm (Inter ss s)
    Final s'' = nsStm (Inter (While b ss) s')

nsStm (Inter (While b ss) s)
   | not(bVal b s) = Final s

-- semantic function for natural semantics
sNs :: Stm -> State -> State
sNs ss s = s'
  where Final s' = nsStm (Inter ss s)

-- Example C.1
sFac = sNs factorial sInit
-- End Example C.1
