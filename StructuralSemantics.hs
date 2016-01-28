-- -------------------------------------------------------------------
--
-- StructuralSemantics.hs
--
-- An implementation of appendix C of
-- [Nielson and Nielson, semantics with applications]
--
-- Author: Haritz Puerto-San-Roman
--
-- -------------------------------------------------------------------

module StructuralSemantics where

import While

-- representation of configurations for While

data Config = Inter Stm State  -- <S, s>
            | Final State      -- s

isFinal :: Config -> Bool
isFinal (Inter ss s) = False
isFinal (Final s)    = True

-- representation of the transition relation <S, s> => s'

sosStm :: Config -> Config

-- x := a

sosStm (Inter (Ass x a) s) = Final (update s x (aVal a s))
  where
    update s x v y = if x == y then v else s y

-- skip

sosStm (Inter Skip s) = Final s

-- s1; s2

sosStm (Inter (Comp ss1 ss2) s)
  | isFinal(sosStm (Inter ss1 s)) = Inter ss2 s'
  where Final s' = sosStm (Inter ss1 s)

sosStm (Inter (Comp ss1 ss2) s)
  | isAbort(sosStm (Inter ss1 s)) = Inter Abort s
  where isAbort (Inter Abort _) = True
        isAbort _ = False

sosStm (Inter (Comp ss1 ss2) s)
  | not(isFinal(sosStm (Inter ss1 s))) = Inter (Comp ss1' ss2) s'
  where Inter ss1' s' = sosStm (Inter ss1 s)

-- if b then s1 else s2

sosStm (Inter (If b ss1 ss2) s)
  | bVal b s = Inter ss1 s

sosStm (Inter (If b ss1 ss2) s)
  | not(bVal b s) = Inter ss2 s

-- while b do s

sosStm (Inter (While b st) s) = Inter (If b (Comp st (While b st)) Skip) s

-- abort

sosStm (Inter Abort s) = Inter Abort s
