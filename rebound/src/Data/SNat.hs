-- |
-- Module      : Data.SNat
-- Description : Singleton naturals
--
-- Runtime data that connects to type-level nats.
module Data.SNat(
  Nat(..), toNatural, fromNatural,
  SNat(..),  snatToNat,
  SNatI(..), snat, withSNat, reify, reflect,
  type (+),
  N0, N1, N2, N3,
  s0, s1, s2, s3,
  sPlus,
  axiomPlusZ,
  axiomAssoc,
  SNat_(..), snat_,
  prev,
  next,
  ToInt(..),
 ) where

-- Singleton nats are purely runtime

import Data.Type.Equality
import Data.Type.Nat
import Test.QuickCheck
import Unsafe.Coerce (unsafeCoerce)
import Prelude hiding (pred, succ)

-----------------------------------------------------
-- axioms (use unsafeCoerce)
-----------------------------------------------------

-- | '0' is identity element for @+@
axiomPlusZ :: forall m. m + Z :~: m
axiomPlusZ = unsafeCoerce Refl

-- | @+@ is associative.
axiomAssoc :: forall p m n. p + (m + n) :~: (p + m) + n
axiomAssoc = unsafeCoerce Refl

-----------------------------------------------------
-- Nats (singleton nats and implicit singletons)
-----------------------------------------------------

-- | 0.
type N0 = Z

-- | 1.
type N1 = S N0

-- | 2.
type N2 = S N1

-- | 3.
type N3 = S N2

---------------------------------------------------------
-- Singletons and instances
---------------------------------------------------------

-- | 0.
s0 :: SNat N0
s0 = snat

-- | 1.
s1 :: SNat N1
s1 = snat

-- | 2.
s2 :: SNat N2
s2 = snat

-- | 3.
s3 :: SNat N3
s3 = snat

instance (SNatI n) => Arbitrary (SNat n) where
  arbitrary :: (SNatI n) => Gen (SNat n)
  arbitrary = pure snat

-- | Conversion to 'Int'.
class ToInt a where
  toInt :: a -> Int

instance ToInt (SNat n) where
  toInt :: SNat n -> Int
  toInt = fromInteger . toInteger . snatToNat

---------------------------------------------------------
-- Addition
---------------------------------------------------------

-- | Notation for the addition of naturals.
type family (n :: Nat) + (m :: Nat) :: Nat where
  m + n = Plus m n

-- | Addition of singleton naturals.
sPlus :: forall n1 n2. SNat n1 -> SNat n2 -> SNat (n1 + n2)
sPlus SZ n = n
sPlus x@SS y = withSNat (sPlus (prev x) y) SS

-- >>> reflect $ sPlus s3 s1
-- 4

---------------------------------------------------------
-- View pattern access to the predecessor
---------------------------------------------------------

-- | View pattern allowing pattern matching on naturals.
-- See 'snat_'.
data SNat_ n where
  SZ_ :: SNat_ Z
  SS_ :: SNat n -> SNat_ (S n)

-- | View pattern allowing pattern matching on naturals.
--
-- @
-- f :: forall p. SNat p -> ...
-- f SZ = ...
-- f (snat_ -> SS_ m) = ...
-- @
snat_ :: SNat n -> SNat_ n
snat_ SZ = SZ_
snat_ SS = SS_ snat

-- | Predecessor of a natural.
prev :: SNat (S n) -> SNat n
prev SS = snat

-- | Successor of a natural.
next :: SNat n -> SNat (S n)
next x = withSNat x SS