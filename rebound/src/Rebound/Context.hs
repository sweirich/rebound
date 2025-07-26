module Rebound.Context(Ctx, emptyC, (+++), (++++)) where

import Rebound.Lib
import Rebound.Env
import Rebound.Classes

----------------------------------------------------------------
-- Typing context utilities for dependently-typed languages
----------------------------------------------------------------

-- A typing context maps indices to type in the same scope
type Ctx v n = Env v n n

-- This is not weakening --- it increments all variables by one
shiftC :: forall v n. (SubstVar v) => v n -> v (S n)
shiftC = applyE @v shift1E

shiftCtx :: (SubstVar v) => Env v n n -> Env v n (S n)
shiftCtx g = g .>> shift1E

-- | An empty context, that includes no variable assumptions
emptyC :: Ctx v N0
emptyC = zeroE

-- | 'Snoc' a new definition to the end of the context
-- All existing types in the context need to be shifted (lazily)
(+++) :: forall v n. (SubstVar v) => Ctx v n -> v n -> Ctx v (S n)
g +++ a = applyE @v shift1E a .: (g .>> shift1E)


-- | Append contexts. Shifts all indices in the first argument by the length 
-- of the second.
(++++) :: forall v n n' m. (SNatI n', SubstVar v) => Env v n m -> Env v n' (n' + m) -> Env v (n' + n) (n' + m)
l ++++ r =
  let p = snat @n'
   in r .++ (l .>> shiftNE p)


-- Example usage

data Exp n = Star | Var (Fin n) deriving Show
instance SubstVar Exp where var = Var
instance Subst Exp Exp where
    applyE s Star = Star
    applyE s (Var x) = applyEnv s x


-- c :: Ctx Exp N4
-- x : * , y : x, z : x , w : *
c = emptyC +++ Star +++ Var FZ +++ Var (FS FZ) +++ Star

-- >>> applyEnv c (FS FZ)
-- Var 3

