
module AutoEnv.Classes where

import AutoEnv.Lib

-- | An environment (or explicit substitution) that map
-- indices bounded by `m`, to values of type `v n`
-- For now, we represent this directly as a function,
-- but we might want to change that. So we wrap it in
-- a newtype to hide the representation.
newtype Env v m n = Env {applyEnv :: Fin m -> v n}

-- | Well-scoped types that can be the range of
-- an environment. This should generally be the `Var`
-- constructor from the syntax.
class SubstVar (v :: Nat -> Type) where
  var :: Fin n -> v n

-- | Apply the environment throughout a term of
-- type `c n`, replacing variables with values
-- of type `v m`
class (SubstVar v) => Subst v c where
  applyE :: Env v n m -> c n -> c m

-- | Does a variable appear free?
class FV (t :: Nat -> Type) where
  appearsFree :: Fin n -> t n -> Bool

-- | Are the two terms alpha equivalent? The terms do not 
-- need to be in the same scope
class Alpha (t :: Nat -> Type) where
    aeq :: t n1 -> t n2 -> Bool


-- Strengthening cannot be implemented through substitution because it
-- must fail if the term uses invalid variables. Therefore, we make a
-- class of nat-indexed types that can be strengthened. We also provide
-- default definitions for strengthening by one and by n. Only one of
-- these functions need to be provided
class Strengthen t where
  strengthenOne' :: SNat n -> t (S n) -> Maybe (t n)
  strengthenOne' = strengthen' (SS SZ)

  strengthen' :: SNat m -> SNat n -> t (Plus m n) -> Maybe (t n)
  strengthen' SZ n f = Just f
  strengthen' (SS m) SZ f = Nothing
  strengthen' (SS m) (SS n) f = do
    f' <- strengthenOne' (sPlus m (SS n)) f
    strengthen' m (SS n) f'

strengthen :: forall m n t. 
    (Strengthen t, SNatI m, SNatI n) => t (Plus m n) -> Maybe (t n)
strengthen = strengthen' (snat :: SNat m) (snat :: SNat n)

---------------------------------------------------------


instance Strengthen Fin where
  strengthen' :: SNat m -> SNat n -> Fin (Plus m n) -> Maybe (Fin n)
  strengthen' = strengthenFin


-- >>> strengthenOne' (SS (SS SZ)) (FZ :: Fin N3) :: Maybe (Fin N2)
-- Just 0

-- >>> strengthen' (SS (SS SZ)) (SS SZ) (FZ :: Fin N3) :: Maybe (Fin N1)
-- Just 0