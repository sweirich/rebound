{-# LANGUAGE UndecidableInstances #-}
module Fin where

-- similar to
-- https://hackage.haskell.org/package/fin-0.3.1/docs/Data-Fin.html#t:Fin

import Nat 

import Test.QuickCheck

-----------------------------------------------------
-- Fins
-----------------------------------------------------
data Fin (n :: Nat) where
    FZ :: Fin (S n)
    FS :: Fin n -> Fin (S n)

f0 :: Fin (S n)
f0 = FZ

f1 :: Fin (S (S n))
f1 = FS f0

f2 :: Fin (S (S (S n)))
f2 = FS f1

instance ToInt (Fin n) where
   toInt :: Fin n -> Int
   toInt FZ = 0
   toInt (FS x) = 1 + toInt x


-- >>> [minBound .. maxBound] :: [Fin Three]
-- [0,1,2]

instance (n ~ S m, SNatI m) => Bounded (Fin n) where
    minBound = FZ
    maxBound = largest snat

largest :: SNat n -> Fin (S n)
largest SZ = FZ 
largest (SS n) = FS (largest n)


instance SNatI n => Enum (Fin n) where
    toEnum :: Int -> Fin n
    toEnum = aux (snat :: SNat n) where
        aux :: forall n. SNat n -> Int -> Fin n
        aux SZ _ = error "to large"
        aux (SS n) 0 = FZ
        aux (SS n) m = FS (aux n (m - 1))

    fromEnum :: Fin n -> Int
    fromEnum = toInt


deriving instance Eq (Fin n)
deriving instance Ord (Fin n)
instance Show (Fin n) where show = show . toInt

instance SNatI n => Arbitrary (Fin n) where
    arbitrary :: Gen (Fin n)
    arbitrary = elements (enumFin snat)

-- list all numbers up to some size

-- >>> enumFin snat3
-- Variable not in scope: snat3 :: SNat n_aa82F[sk:1]

enumFin :: SNat n -> [Fin n]
enumFin SZ = []
enumFin (SS n) = FZ : map FS (enumFin n)



universe :: SNatI n => [Fin n]
universe = enumFin snat

---------------------------------
-- Plus 

-- increase the bound of a Fin.
-- this is an identity function 
weakenLeft1 :: Fin n -> Fin (S n)
weakenLeft1 FZ = FZ
weakenLeft1 (FS f) = FS (weakenLeft1 f)


------------------------------------

pick :: Fin N0 -> a -> a -> a
pick f x y = case f of
    FZ -> x
    (FS _) -> y
