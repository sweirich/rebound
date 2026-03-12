-- This implementation is adapted from
-- https://mathisbd.github.io/blog/esubstitutions.html
-- TODO: still missing weakenER, but should be able to test and run it now
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE UndecidableSuperClasses #-}
module Rebound.Env.ShiftList where

import Data.Nat
import Data.Fin

import Rebound.Lib hiding (apply)
import Unsafe.Coerce (unsafeCoerce)
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

-- The 'SNat k' in this representation is an embedded shift 
-- that means that 'Inc k' is the same as 'Inc k'
data Env a m n where
    Zero :: Env a Z n
    Inc  :: !(SNat k) -> Env a n (k + n)
    Cons :: !(SNat k) -> a m -> !(Env a n m) -> Env a (S n) (k + m)

instance (forall n. NFData (a n)) => NFData (Env a n m) where
  rnf :: (forall (n1 :: Nat). NFData (a n1)) => Env a n m -> ()
  rnf Zero = ()
  rnf (Inc x) = rnf x 
  rnf (Cons x a xs) = rnf x `seq` rnf a `seq` rnf xs 

------------------------------------------------------------------------------
-- Application
------------------------------------------------------------------------------

weaken :: forall a k n. Subst a a => SNat k -> a n -> a (k + n)
weaken k t = applyE @a (shiftNE k) t

applyEnv ::  SubstVar a => Env a n m -> Fin n -> a m
applyEnv s i = applyRec @N0 snat s i
{-# INLINEABLE applyEnv #-}

-- | Build an optimized version of applyE.
-- Checks to see if we are applying the identity substitution first.
applyOpt :: (Env v n m -> c n -> c m) -> (Env v n m -> c n -> c m)
applyOpt f (Inc SZ) x = x
applyOpt f r x = f r x
{-# INLINEABLE applyOpt #-}

-- | As we traverse the list, accumulate the shifting amount and 
-- apply it all at once.
applyRec :: forall acc a n m . SubstVar a => 
    SNat acc -> Env a n m -> Fin n -> a (acc + m)
applyRec acc s i = 
    case s of 
        Zero -> case i of {}
        Inc (k :: SNat k) -- renaming
              | Refl <- axiomPlusZ @m
              , Refl <- axiomAssoc @acc @k @n
              -> var (shiftN (sPlus acc k) i)
        Cons (k :: SNat k) (t :: a m1) s 
              | Refl <- axiomAssoc @acc @k @m1 
              -> case i of 
                   FZ   -> weaken (sPlus acc k) t  -- substitution
                   FS j -> applyRec (sPlus acc k) s j


zeroE :: Env a Z n
zeroE = Zero
{-# INLINEABLE zeroE #-}

weakenER :: forall m v n. (SubstVar v) => SNat m -> Env v n (n + m)
weakenER = undefined

shiftNE :: SNat k -> Env a n (k + n)
shiftNE k = Inc k
{-# INLINEABLE shiftNE #-}

(.:) :: a m -> Env a n m -> Env a (S n) m
(.:) = Cons SZ 
{-# INLINEABLE (.:) #-}


-- | inverse of @cons@ -- remove the first mapping
tail :: (SubstVar v) => Env v (S n) m -> Env v n m
tail x = shiftNE s1 .>> x
{-# INLINEABLE tail #-}

-- Compose a substitution with shifting, just add the shifting amount 
-- to the head of the substitution
-- skip k s == s .>> Inc k 
skip0 :: forall k0 a n m. SNatI k0 => Env a n m -> Env a n (k0 + m)
skip0 s = case s of
              Zero -> Zero
              (Inc (k :: SNat k)) 
                | Refl <- axiomAssoc @k0 @k @n
                    -> Inc (sPlus (snat @k0) k)
              (Cons (k :: SNat k) (t :: a m1) s)
                | Refl <- axiomAssoc @k0 @k @m1
                    -> Cons (sPlus (snat @k0) k) t s
{-# INLINEABLE skip0 #-}

up :: forall a n m. SubstVar a => Env a n m -> Env a (S n) (S m)
up s = var f0 .: (skip0 @N1 s)

-- NB: there is a generic definition of upN in Env.hs, but I don't know 
-- how efficient it is.

-- | Compose two environments, applying them in sequence (left then right).
(.>>) :: (SubstVar v) => Env v p n -> Env v n m -> Env v p m
(.>>) = comp
{-# INLINEABLE (.>>) #-}

-- | look at the two arguments and compose them together smartly
comp :: forall a m n p. (SubstVar a) =>
         Env a m n -> Env a n p -> Env a m p
comp Zero s = Zero    
-- if the second argument is a shift, we can use skip    
comp s (Inc (k :: SNat k)) = withSNat k $ skip0 @k s
-- if the first argument is a shift, we can drop substitutions in the second
-- argument
comp (Inc SZ) s = s
comp (Inc (snat_ -> SS_ m1)) (Cons (k :: SNat k) _ xs) = 
    comp (Inc m1) (withSNat k $ skip0 @k xs)
-- for the Cons/Cons case, we need to apply the second substitution 
-- to 'x' (after it has been shifted by k)
comp (Cons (k :: SNat k) (x :: a n1) xs) s = Cons SZ head tail where
    head = applyE @a (comp (Inc k) s) x
    tail = comp (withSNat k $ skip0 @k xs) s

-- | Map the range of an environment. Has to preserve the scope of the range.
transform :: (SubstVar b) => 
   (forall m. a m -> b m) -> Env a n m -> Env b n m
transform f Zero = Zero
transform f (Inc k) = Inc k
transform f (Cons k x xs) = Cons k (f x) (transform f xs)