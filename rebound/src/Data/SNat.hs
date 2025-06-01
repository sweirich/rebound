{-# LANGUAGE PatternSynonyms #-} 
{-# LANGUAGE RoleAnnotations #-}
module Data.SNat(
  Nat(..), pattern UnsafeSNat, 
  SNat(SZ,SS), snatToNatural, fromSNat,
  SNatI(..), withSNat, 
  type (+), 
  N0, N1, N2, N3,
  s0, s1, s2, s3, 
  sPlus,
  axiomPlusZ,
  axiomAssoc,
  SNat_(..), snat_,
  prev, ss,
  ToInt(..),
  induction,
 ) where

-- We want a type-level natural number with an inductive structure but uses machine ints for the runtime representation. 
-- GHC.TypeLits gets us part-way there, but the type level is not inductive.

import Prelude hiding (pred, succ)

import Data.Void
import Data.Type.Equality
import Test.QuickCheck

import GHC.Num.Natural ( Natural )
import GHC.Show ( appPrec, appPrec1 )
import GHC.Exts

import Unsafe.Coerce (unsafeCoerce)

-----------------------------------------------------
-- Type-level Natural numbers w/addition
-----------------------------------------------------

data Nat = Z | S Nat

type family (m :: Nat) + (n :: Nat) :: Nat where
  Z + n = n
  (S m) + n = S (m + n)

-- Monoid properties for plus (axioms)
axiomPlusZ :: forall m. m + Z :~: m
axiomPlusZ = unsafeCoerce Refl

axiomAssoc :: forall p m n. p + (m + n) :~: (p + m) + n
axiomAssoc = unsafeCoerce Refl


-- constants
type N0 = Z

type N1 = S N0

type N2 = S N1

type N3 = S N2

type N4 = S N3

---------------------------------------------------------
-- Singleton naturals (implementation adapted from GHC.TypeNats)
-- Like GHC.TypeNats, runtime naturals are implemented as 
-- non-negative maching integers. 
-- The difference is that these SNats are indexed by inductive Nats
-- instead of the more abstract type-level Nats of GHC.TypeNats
---------------------------------------------------------

newtype SNat (n :: Nat) = UnsafeSNat Int
type role SNat nominal

decNat :: SNat a -> SNat b -> Either (a :~: b -> Void) (a :~: b)
decNat (UnsafeSNat x) (UnsafeSNat y)
  | x == y    = Right (unsafeCoerce Refl)
  | otherwise = Left (\Refl -> errorWithoutStackTrace ("decideNat: Impossible equality proof " ++ show x ++ " :~: " ++ show y))

instance Eq (SNat n) where
  _ == _ = True

instance Ord (SNat n) where
  compare :: SNat n -> SNat n -> Ordering
  compare _ _ = EQ

instance Show (SNat n) where
  showsPrec p (UnsafeSNat n)
    = showParen (p > appPrec)
      ( showString "SNat @"
        . showsPrec appPrec1 n
      )

instance TestEquality SNat where
  testEquality a b = case decNat a b of
    Right x -> Just x
    Left _  -> Nothing

-- | Return the 'Natural' number corresponding to @n@ in an @'SNat' n@ value.
--
fromSNat :: SNat n -> Int
fromSNat (UnsafeSNat n) = n

snatToNatural :: SNat n -> Natural
snatToNatural = fromInteger . toInteger . fromSNat

-- | Add two runtime nats
sPlus :: forall n1 n2. SNat n1 -> SNat n2 -> SNat (n1 + n2)
sPlus (UnsafeSNat n1) (UnsafeSNat n2) = UnsafeSNat (n1 + n2)

---------------------------------------------------------
-- Induction
---------------------------------------------------------

induction' :: forall n v. SNat n -> v Z -> 
  (forall m. SNatI m => v m -> v (S m)) -> v n
induction' (snat_ -> SZ_) base step = base
induction' (snat_ -> SS_ x) base step = 
  withSNat x $ step (induction' x base step)

induction :: forall n v. (SNatI n) => v Z -> 
  (forall m. SNatI m => v m -> v (S m)) -> v n
induction = induction' (snat @n)

---------------------------------------------------------
-- Implicit Singletons
---------------------------------------------------------

class SNatI (n :: Nat) where
  snat :: SNat n

instance SNatI Z where snat = UnsafeSNat 0
instance SNatI n => SNatI (S n) where snat = ss snat

-- | Convert an explicit @'SNat' n@ value into an implicit @'SNatI' n@
-- constraint.
--
withSNat :: forall n r.  SNat n -> (SNatI n => r) -> r
withSNat = withDict 


s0 :: SNat N0
s0 = snat

s1 :: SNat N1
s1 = snat

s2 :: SNat N2
s2 = snat

s3 :: SNat N3
s3 = snat

instance (SNatI n) => Arbitrary (SNat n) where
  arbitrary :: (SNatI n) => Gen (SNat n)
  arbitrary = pure snat

class ToInt a where
  toInt :: a -> Int

instance ToInt (SNat n) where
  toInt :: SNat n -> Int
  toInt = fromSNat

---------------------------------------------------------
-- View pattern access to the predecessor
---------------------------------------------------------

prev :: SNat (S n) -> SNat n
prev (UnsafeSNat n) = (UnsafeSNat (n-1))

ss :: SNat n -> SNat (S n)
ss (UnsafeSNat x) = UnsafeSNat (x+1)

data SNat_ (n :: Nat) where
  SZ_ :: (Z ~ n) => SNat_ n
  SS_ :: (S k ~ n) => SNat k -> SNat_ n

snat_ :: forall n. SNat n -> SNat_ n
snat_ (UnsafeSNat 0) = unsafeCoerce SZ_
snat_ (UnsafeSNat n) = unsafeCoerce (SS_ (UnsafeSNat (n-1)))

pattern SZ :: () => (Z ~ n) => SNat n
pattern SZ <- (snat_ -> SZ_)
  where SZ = (UnsafeSNat 0)

-- Pattern SS for the S k case
-- NOTE: this doesn't provide GADT-like pattern matching.
-- Use the view pattern directly.
pattern SS :: forall k . SNat k -> SNat (S k)
pattern SS prev <- (snat_ -> SS_ prev)
  where
    SS = ss

