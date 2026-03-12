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
-- that means that 'Nil k' is the same as 'Inc k'
data Env a m n where
    Nil  :: !(SNat k) -> Env a n (k + n)
    Cons :: !(SNat k) -> a m -> !(Env a n m) -> Env a (S n) (k + m)

instance (forall n. NFData (a n)) => NFData (Env a n m) where
  rnf :: (forall (n1 :: Nat). NFData (a n1)) => Env a n m -> ()
  rnf (Nil x) = rnf x 
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
applyOpt f (Nil SZ) x = x
applyOpt f r x = f r x
{-# INLINEABLE applyOpt #-}

-- | As we traverse the list, accumulate the shifting amount and 
-- apply it all at once.
applyRec :: forall acc a n m . SubstVar a => 
    SNat acc -> Env a n m -> Fin n -> a (acc + m)
applyRec acc s i = 
    case s of 
        Nil (k :: SNat k) -- renaming
              | Refl <- axiomPlusZ @m
              , Refl <- axiomAssoc @acc @k @n
              -> var (shiftN (sPlus acc k) i)
        Cons (k :: SNat k) (t :: a m1) s 
              | Refl <- axiomAssoc @acc @k @m1 
              -> case i of 
                   FZ   -> weaken (sPlus acc k) t  -- substitution
                   FS j -> applyRec (sPlus acc k) s j


zeroE :: forall n a. SNatI n => Env a Z n
zeroE | Refl <- axiomPlusZ @n 
      = Nil (snat @n)
{-# INLINEABLE zeroE #-}

weakenER :: forall m v n. (SubstVar v) => SNat m -> Env v n (n + m)
weakenER = undefined

id :: SNatI n => Env a n n
id = Nil SZ
{-# INLINEABLE id #-}

shiftNE :: SNat k -> Env a n (k + n)
shiftNE k = Nil k
{-# INLINEABLE shiftNE #-}

(.:) :: a m -> Env a n m -> Env a (S n) m
(.:) = Cons SZ 
{-# INLINEABLE (.:) #-}

-- Compose a substitution with shifting, just add the shifting amount 
-- to the head of the substitution
-- skip k s == s .>> Nil k 
skip :: forall k0 a n m. SNatI k0 => Env a n m -> Env a n (k0 + m)
skip s = case s of
              (Nil (k :: SNat k)) 
                | Refl <- axiomAssoc @k0 @k @n
                    -> Nil (sPlus (snat @k0) k)
              (Cons (k :: SNat k) (t :: a m1) s)
                | Refl <- axiomAssoc @k0 @k @m1
                    -> Cons (sPlus (snat @k0) k) t s
{-# INLINEABLE skip #-}

up :: forall a n m. SubstVar a => Env a n m -> Env a (S n) (S m)
up s = var f0 .: (skip @N1 s)

-- NB: there is a generic definition of upN in Env.hs, but I don't know 
-- how efficient it is.

-- | Compose two environments, applying them in sequence (left then right).
(.>>) :: (SubstVar v, SNatI p) => Env v p n -> Env v n m -> Env v p m
(.>>) = comp
{-# INLINEABLE (.>>) #-}

-- | look at the two arguments and compose them together smartly
comp :: forall a m n p. (SubstVar a) =>
         Env a m n -> Env a n p -> Env a m p
-- if the second argument is a shift, we can use skip         
comp s (Nil (k :: SNat k)) = withSNat k $ skip @k s
-- if the first argument is a shift, we can drop substitutions in the second
-- argument
comp (Nil SZ) s = s
comp (Nil (snat_ -> SS_ m1)) (Cons (k :: SNat k) _ xs) = 
    comp (Nil m1) (withSNat k $ skip @k xs)
-- for the Cons/Cons case, we need to apply the second substitution 
-- to 'x' (after it has been shifted by k)
comp (Cons (k :: SNat k) (x :: a n1) xs) s = Cons SZ head tail where
    head = applyE @a (comp (Nil k) s) x
    tail = comp (withSNat k $ skip @k xs) s

-- | Map the range of an environment. Has to preserve the scope of the range.
transform :: (SubstVar b) => 
   (forall m. a m -> b m) -> Env a n m -> Env b n m
transform f (Nil k) = Nil k
transform f (Cons k x xs) = Cons k (f x) (transform f xs)