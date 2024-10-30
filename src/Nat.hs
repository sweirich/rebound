module Nat where

-- similar to https://hackage.haskell.org/package/fin-0.3.1/docs/Data-Nat.html#t:Nat
-- Singleton nats are purely runtime.

import Data.Type.Equality
import Test.QuickCheck


-----------------------------------------------------
class ToInt n where
    toInt :: n -> Int
instance ToInt Nat where toInt = toIntNat
instance ToInt (SNat n) where toInt = toIntSNat
-----------------------------------------------------

-----------------------------------------------------
-- Nats (and singleton nats and implicit singletons)
-----------------------------------------------------
data Nat = Z | S Nat
    deriving (Eq, Ord)

instance Show Nat where show = show . toIntNat

nat0 :: Nat
nat0 = Z
nat1 :: Nat
nat1 = S nat1
nat2 :: Nat
nat2 = S nat2 

toIntNat :: Nat -> Int
toIntNat Z = 0
toIntNat (S n) = 1 + toIntNat n

type N0 = Z
type N1 = S N0
type N2 = S N1
type N3 = S N2

type family Plus (n :: Nat) (m :: Nat) :: Nat where
    Plus Z m = m
    Plus (S n) m = S (Plus n m)

---------------------------------------------------------
-- Singleton
---------------------------------------------------------

data SNat (n :: Nat) where
    SZ :: SNat Z
    SS :: SNat n -> SNat (S n)

snat0 :: SNat N0
snat0 = SZ
snat1 :: SNat N1
snat1 = SS snat0
snat2 :: SNat N2
snat2 = SS snat1 
snat3 :: SNat N3
snat3 = SS snat2

toIntSNat :: SNat n -> Int
toIntSNat SZ = 0
toIntSNat (SS n) = 1 + toIntSNat n

instance TestEquality SNat where
    testEquality :: SNat a -> SNat b -> Maybe (a :~: b)
    testEquality SZ SZ = Just Refl
    testEquality (SS x) (SS y) 
       | Just Refl <- testEquality x y = Just Refl
    testEquality _ _ = Nothing

instance SNatI n => Arbitrary (SNat n) where
    arbitrary :: SNatI n => Gen (SNat n)
    arbitrary = pure snat

instance Show (SNat n) where show = show . toIntSNat

---------------------------------------------------------
-- Implicit Singleton
---------------------------------------------------------

class SNatI (n :: Nat) where
    snat :: SNat n
instance SNatI Z where 
    snat :: SNat Z
    snat = SZ
instance SNatI n => SNatI (S n) where 
    snat :: SNatI n => SNat (S n)
    snat = SS snat

-- Construct an implicit SNat from an implicit one
withSNat :: SNat n -> (SNatI n => r) -> r
withSNat SZ k = k
withSNat (SS n) k = withSNat n k