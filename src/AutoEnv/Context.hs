module AutoEnv.Context where

import AutoEnv.Lib
import AutoEnv.Env
import AutoEnv.Classes

----------------------------------------------------------------
-- For dependently-typed languages
----------------------------------------------------------------

type Ctx v n = Env v n n

-- This is not weakening --- it increments all variables by one
shiftC :: forall v c n. (Subst v c) => c n -> c (S n)
shiftC = applyE @v shift1E

shiftCtx :: (Subst v v) => Env v n n -> Env v n (S n)
shiftCtx g = g .>> shift1E

emptyC :: Ctx v N0
emptyC = zeroE

(+++) :: forall v n. (Subst v v) => Ctx v n -> v n -> Ctx v (S n)
g +++ a = shiftC @v @v a .: shiftCtx g
