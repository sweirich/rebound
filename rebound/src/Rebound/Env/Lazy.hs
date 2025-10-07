{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# OPTIONS_HADDOCK hide #-}
module Rebound.Env.Lazy where

-- "Defunctionalized" representation of environment
-- stored values are lazy
-- *rest* of the environment is strict
-- Includes optimized composition (Inc and Cons cancel)
-- Includes Wadler's optimizations for the empty environment

import Rebound.Lib
import Data.Fin (Fin(..))
import qualified Data.Fin as Fin
import GHC.Generics hiding (S)
import Control.DeepSeq (NFData (..))

------------------------------------------------------------------------------
-- Substitution class declarations
------------------------------------------------------------------------------
-- | Well-scoped types that can be the range of
-- an environment. This should generally be the @Var@
-- constructor from the syntax.
class (Subst v v) => SubstVar (v :: Nat -> Type) where
  var :: Fin n -> v n

-- | Apply the environment throughout a term of
-- type `c n`, replacing variables with values
-- of type `v m`
class (SubstVar v) => Subst v c where
  applyE :: Env v n m -> c n -> c m
  default applyE :: (Generic1 c, GSubst v (Rep1 c), SubstVar v) => Env v m n -> c m -> c n
  applyE = gapplyE
  {-# INLINE applyE #-}
  isVar :: c n -> Maybe (v :~: c, Fin n)
  isVar _ = Nothing
  {-# INLINE isVar #-}

-- | Generic programming variant of 'applyE'.
gapplyE :: forall c v m n. (Generic1 c, GSubst v (Rep1 c), Subst v c) => Env v m n -> c m -> c n
gapplyE r e | Just (Refl, x) <- isVar @v @c e = applyEnv r x
gapplyE r e = applyOpt (\s x -> to1 $ gsubst s (from1 x)) r e
{-# INLINEABLE gapplyE #-}

-- | Generic programming support for 'Subst'.
class GSubst v (e :: Nat -> Type) where
  gsubst :: Env v m n -> e m -> e n


------------------------------------------------------------------------------
-- Environment representation
------------------------------------------------------------------------------

-- | Maps variables in scope @n@ to terms (of type @a@) in scope @m@.
data Env (a :: Nat -> Type) (n :: Nat) (m :: Nat) where
  Zero  :: Env a Z n
  WeakR :: (SNat m) -> Env a n (n + m) --  weaken values in range by m
  Weak  :: (SNat m) -> Env a n (m + n) --  weaken values in range by m
  Inc   :: (SNat m) -> Env a n (m + n) --  increment values in range (shift) by m
  Cons  :: (a m) -> (Env a n m) -> Env a ('S n) m --  extend a substitution (like cons)
  (:<>) :: (Env a m n) -> (Env a n p) -> Env a m p --  compose substitutions


instance (forall n. NFData (a n)) => NFData (Env a n m) where
  rnf Zero = ()
  rnf (WeakR m) = rnf m
  rnf (Weak m) = rnf m
  rnf (Inc m) = rnf m
  rnf (Cons x r) = rnf x `seq` rnf r
  rnf (r1 :<> r2) = rnf r1 `seq` rnf r2

------------------------------------------------------------------------------
-- Application
------------------------------------------------------------------------------

-- | Value of the index x in the substitution s

applyEnv :: SubstVar a => Env a n m -> Fin n -> a m
applyEnv Zero x = Fin.absurd x
applyEnv (Inc m) x = var (Fin.shiftN m x)
applyEnv (WeakR m) x = var (Fin.weakenFinRight m x)
applyEnv (Weak m) x = var (Fin.weakenFin m x)
applyEnv (Cons ty _s) FZ = ty
applyEnv (Cons _ty s) (FS x) = applyEnv s x
applyEnv (s1 :<> s2) x = applyE s2 (applyEnv s1 x)
{-# INLINEABLE applyEnv #-}

-- | Build an optimized version of applyE.
-- Checks to see if we are applying the identity substitution first.
applyOpt :: (Env v n m -> c n -> c m) -> (Env v n m -> c n -> c m)
applyOpt f (Inc SZ) x = x
applyOpt f (Weak SZ) x = x
applyOpt f (WeakR SZ) (x :: c m) =
  case axiomPlusZ @m of Refl -> x
applyOpt f r x = f r x
{-# INLINEABLE applyOpt #-}

------------------------------------------------------------------------------
-- Construction and modification
------------------------------------------------------------------------------

-- | The empty environment (zero domain)
zeroE :: Env v Z n
zeroE = Zero
{-# INLINEABLE zeroE #-}

-- | Increase the bound on free variables (on the right), without changing any free variable.
weakenER :: forall m v n. (SubstVar v) => SNat m -> Env v n (n + m)
weakenER = WeakR
{-# INLINEABLE weakenER #-}

-- | Increase the bound on free variables (on the left), without changing any free variable.
weakenE' :: forall m v n. (SubstVar v) => SNat m -> Env v n (m + n)
weakenE' = Weak
{-# INLINEABLE weakenE' #-}

-- | Shift the term, increasing every free variable as well as the bound by the provided amount.
shiftNE :: (SubstVar v) => (SubstVar v) => SNat m -> Env v n (m + n)
shiftNE = Inc
{-# INLINEABLE shiftNE #-}

-- | @cons@ an environment, adding a new mapping
-- for index '0'. All keys are shifted over.
(.:) :: v m -> Env v n m -> Env v (S n) m
(.:) = Cons
{-# INLINEABLE (.:) #-}

-- | @uncons@ an environment, removing the mapping for index '0'.
-- All other keys are shifted back.
tail :: (SubstVar v) => Env v (S n) m -> Env v n m
tail x = shiftNE s1 .>> x
{-# INLINEABLE tail #-}

-- | Compose two environments, applying them in sequence (left then right).
-- Some optimizations will be applied to optimize the resulting environment.
(.>>) :: (Subst v v) => Env v p n -> Env v n m -> Env v p m
(.>>) = comp
{-# INLINEABLE (.>>) #-}

-- | Compose two environments, applying them in sequence (left then right).
-- Some optimizations will be applied to optimize the resulting environment.
--
-- Some of the applied optimizations are:
-- - Identity environments (e.g., @'shiftNE' SZ@) are eliminated
-- - Absorbing environments on the right (i.e., 'zeroE') are eliminated
-- - Compatible environments are fused (e.g., @'weakenER' n@ and @'weakenER' m)
comp :: forall a m n p. SubstVar a =>
         Env a m n -> Env a n p -> Env a m p
comp Zero s = Zero
comp (Weak (k1 :: SNat m1)) (Weak (k2 :: SNat m2))  =
  case axiomAssoc @m2 @m1 @m of
    Refl -> Weak (sPlus k2 k1)
comp (Weak SZ) s = s
comp s (Weak SZ) = s
comp (WeakR (k1 :: SNat m1)) (WeakR (k2 :: SNat m2))  =
  case axiomAssoc @m @m1 @m2 of
    Refl -> WeakR (sPlus k1 k2)
comp (WeakR SZ) s =
  case axiomPlusZ @m of
    Refl -> s
comp s (WeakR SZ) =
  case axiomPlusZ @n of
    Refl -> s
comp (Inc (k1 :: SNat m1)) (Inc (k2 :: SNat m2))  =
  case axiomAssoc @m2 @m1 @m of
    Refl -> Inc (sPlus k2 k1)
comp s (Inc SZ) = s
comp (Inc SZ) s = s
comp (Inc (snat_ -> SS_ p1)) (Cons _t p) = comp (Inc p1) p
comp (s1 :<> s2) s3 = comp s1 (comp s2 s3)
comp (Cons t s1) s2 = Cons (applyE s2 t) (comp s1 s2)
comp s1 s2 = s1 :<> s2
{-# INLINEABLE comp #-}

-- | Adapt an environment to go under a binder.
up :: (SubstVar v) => Env v m n -> Env v (S m) (S n)
up (Inc SZ) = Inc SZ
up (Weak SZ) = Weak SZ
up (WeakR SZ) = WeakR SZ
up e = var Fin.f0 .: comp e (Inc s1)
{-# INLINEABLE up #-}

-- | Map the range of an environment. Has to preserve the scope of the range.
transform :: (SubstVar b) => (forall m. a m -> b m) -> Env a n m -> Env b n m
transform f Zero = Zero
transform f (Weak x) = Weak x
transform f (WeakR x) = WeakR x
transform f (Inc x) = Inc x
transform f (Cons a r) = Cons (f a) (transform f r)
transform f (r1 :<> r2) = transform f r1 :<> transform f r2

