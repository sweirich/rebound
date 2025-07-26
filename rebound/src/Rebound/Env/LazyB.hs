{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE UndecidableSuperClasses #-}
module Rebound.Env.LazyB where

-- "Defunctionalized" representation of environment
-- stored values are lazy
-- *rest* of the environment is lazy
-- No optimized composition (Inc and Cons cancel)
-- No Wadler's optimizations for the empty environment

import Rebound.Lib
import Data.Fin (Fin(..))
import qualified Data.Fin as Fin
import GHC.Generics hiding (S)
import Control.DeepSeq (NFData (..))

------------------------------------------------------------------------------
-- Substitution class declarations
------------------------------------------------------------------------------
-- | Well-scoped types that can be the range of
-- an environment. This should generally be the `Var`
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
  
gapplyE :: forall c v m n. (Generic1 c, GSubst v (Rep1 c), Subst v c) => Env v m n -> c m -> c n
gapplyE r e | Just (Refl, x) <- isVar @v @c e = applyEnv r x
gapplyE r e = applyOpt (\s x -> to1 $ gsubst s (from1 x)) r e
{-# INLINEABLE gapplyE #-}

-- Generic programming
class GSubst v (e :: Nat -> Type) where
  gsubst :: Env v m n -> e m -> e n

------------------------------------------------------------------------------
-- Environment representation
------------------------------------------------------------------------------
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
applyEnv Zero x = case x of {}
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
{- applyOpt f (Inc SZ) x = x
applyOpt f (Weak SZ) x = x
applyOpt f (WeakR SZ) (x :: c m) =
  case axiomPlusZ @m of Refl -> x -}
applyOpt f r x = f r x
{-# INLINEABLE applyOpt #-}

------------------------------------------------------------------------------
-- Construction and modification
------------------------------------------------------------------------------

-- | The empty environment (zero domain)
zeroE :: Env v Z n
zeroE = Zero
{-# INLINEABLE zeroE #-}

-- make the bound bigger, on the right, but do not change any indices.
-- this is an identity function
weakenER :: forall m v n. (SubstVar v) => SNat m -> Env v n (n + m)
weakenER = WeakR 
{-# INLINEABLE weakenER #-}

-- make the bound bigger, on the left, but do not change any indices.
-- this is an identity function
weakenE' :: forall m v n. (SubstVar v) => SNat m -> Env v n (m + n)
weakenE' = Weak
{-# INLINEABLE weakenE' #-}

-- | increment all free variables by m
shiftNE :: (SubstVar v) => SNat m -> Env v n (m + n)
shiftNE = Inc
{-# INLINEABLE shiftNE #-}

-- | `cons` -- extend an environment with a new mapping
-- for index '0'. All existing mappings are shifted over.
(.:) :: (SubstVar v) => v m -> Env v n m -> Env v (S n) m
(.:) = Cons 
{-# INLINEABLE (.:) #-}


-- | inverse of `cons` -- remove the first mapping
tail :: (SubstVar v) => Env v (S n) m -> Env v n m
tail x = shiftNE s1 .>> x
{-# INLINEABLE tail #-}

-- | composition: do f then g
-- No optimizations here
(.>>) :: (Subst v v) => Env v p n -> Env v n m -> Env v p m
(.>>) = (:<>)
{-# INLINEABLE (.>>) #-}

-- | modify an environment so that it can go under a binder
up :: (SubstVar v) => Env v m n -> Env v (S m) (S n)
{- up (Inc SZ) = Inc SZ
up (Weak SZ) = Weak SZ
up (WeakR SZ) = WeakR SZ  -}
up e = var Fin.f0 .: (e :<> Inc s1)
{-# INLINEABLE up #-}

-- | mapping operation for range of the environment
transform :: (SubstVar b) => (forall m. a m -> b m) -> Env a n m -> Env b n m
transform f Zero = Zero
transform f (Weak x) = Weak x
transform f (WeakR x) = WeakR x
transform f (Inc x) = Inc x
transform f (Cons a r) = Cons (f a) (transform f r)
transform f (r1 :<> r2) = transform f r1 :<> transform f r2

