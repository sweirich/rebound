module AutoEnv.Context where

import AutoEnv.Classes
import AutoEnv.Env
import AutoEnv.Lib

----------------------------------------------------------------
-- For dependently-typed languages
----------------------------------------------------------------

type Ctx v n = Env v n n

-- This is not weakening --- it increments all variables by one
shiftC :: forall v c n. (Subst v c) => c n -> c (S n)
shiftC = applyE @v shift1E

shiftCtx :: (Subst v v) => Env v n n -> Env v n (S n)
shiftCtx g = g .>> shift1E

-- | An empty context, that includes no variable assumptions
emptyC :: Ctx v N0
emptyC = zeroE

-- | Append a new definition to the context
-- All existing types in the context need to be shifted (lazily)
(+++) :: forall v n. (Subst v v) => Ctx v n -> v n -> Ctx v (S n)
g +++ a = shiftC @v @v a .: shiftCtx g