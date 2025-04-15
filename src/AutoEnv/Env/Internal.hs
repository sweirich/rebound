{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE UndecidableSuperClasses #-}
module AutoEnv.Env.Internal where

-- This is a lazy environment: values stored are not forced
-- Includes Wadler's optimizations for the empty environment


import AutoEnv.Lib
import Data.Fin (Fin(..))
import qualified Data.Fin as Fin
import qualified Data.FinAux as Fin
import GHC.Generics hiding (S)

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

-- Generic programming
class GSubst v (e :: Nat -> Type) where
  gsubst :: Env v m n -> e m -> e n

gapplyE :: (Generic1 c, GSubst v (Rep1 c), SubstVar v) => Env v m n -> c m -> c n
gapplyE = applyOpt (\s x -> to1 $ gsubst s (from1 x))
{-# INLINEABLE gapplyE #-}

------------------------------------------------------------------------------
-- Environment representation
------------------------------------------------------------------------------
data Env (a :: Nat -> Type) (n :: Nat) (m :: Nat) where
  Zero  :: Env a Z n
  WeakR :: !(SNat m) -> Env a n (n + m) --  weaken values in range by m
  Weak  :: !(SNat m) -> Env a n (m + n) --  weaken values in range by m
  Inc   :: !(SNat m) -> Env a n (m + n) --  increment values in range (shift) by m
  Cons  :: (a m) -> !(Env a n m) -> Env a ('S n) m --  extend a substitution (like cons)
  (:<>) :: !(Env a m n) -> !(Env a n p) -> Env a m p --  compose substitutions



-- | The empty environment (zero domain)
zeroE :: Env v Z n
zeroE = Zero

-- make the bound bigger, on the right, but do not change any indices. 
-- this is an identity function
weakenER :: forall m v n. SNat m -> Env v n (n + m)
weakenER = WeakR 

-- make the bound bigger, on the left, but do not change any indices.
-- this is an identity function
weakenE' :: forall m v n. SNat m -> Env v n (m + n)
weakenE' = Weak

-- | increment all free variables by m
shiftNE :: (SubstVar v) => SNat m -> Env v n (m + n)
shiftNE = Inc

-- | `cons` -- extend an environment with a new mapping
-- for index '0'. All existing mappings are shifted over.
(.:) :: v m -> Env v n m -> Env v (S n) m
v .: f = Cons v f

-- | composition: do f then g
(.>>) :: (Subst v v) => Env v p n -> Env v n m -> Env v p m
f .>> g = comp f g


--  Value of the index x in the substitution s
applyEnv :: (SubstVar a) => Env a n m -> Fin n -> a m
applyEnv Zero x = case x of {}
applyEnv (Inc m) x = var (Fin.shiftN m x)
applyEnv (WeakR m) x = var (Fin.weakenFinRight m x)
applyEnv (Weak m) x = var (Fin.weakenFin m x)
applyEnv (Cons ty _s) FZ = ty
applyEnv (Cons _ty s) (FS x) = applyEnv s x
applyEnv (s1 :<> s2) x = applyE s2 (applyEnv s1 x)
{-# INLINEABLE applyEnv #-}


-- | smart constructor for composition
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

-- optimized version of applyE. Checks to see if we are applying the 
-- identity substitution first.
applyOpt :: (Env v n m -> c n -> c m) -> (Env v n m -> c n -> c m)
applyOpt f (Inc SZ) x = x
applyOpt f (Weak SZ) x = x
applyOpt f (WeakR SZ) (x :: c m) = 
  case axiomPlusZ @m of Refl -> x
applyOpt f r x = f r x
{-# INLINEABLE applyOpt #-}

-- | modify an environment so that it can go under
-- a binder
up :: (SubstVar v) => Env v m n -> Env v (S m) (S n)
up (Inc SZ) = Inc SZ
up (Weak SZ) = Weak SZ
up (WeakR SZ) = WeakR SZ 
up e = var Fin.f0 .: comp e (Inc s1)
{-# INLINEABLE up #-}


-- | mapping operation for range of the environment
transform :: (forall m. a m -> b m) -> Env a n m -> Env b n m
transform f Zero = Zero
transform f (Weak x) = Weak x 
transform f (WeakR x) = WeakR x
transform f (Inc x) = Inc x
transform f (Cons a r) = Cons (f a) (transform f r)
transform f (r1 :<> r2) = transform f r1 :<> transform f r2
