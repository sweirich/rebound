{-|
Module      : Fin
Description : Bounded natural numbers
Stability   : experimental

A data type of bounded natural numbers. The type `Fin (S n)` contains numbers 
within the range [0 .. n]. The type `Fin 0` is empty.

By design, this module is similar to
    https://hackage.haskell.org/package/fin-0.3.1/docs/Data-Fin.html
but simpler. Eventually, this file may be replaced by that module.

This module is designed to be imported as 

      import Fin (Fin (..))
      import qualified Fin

-}

{-# LANGUAGE UndecidableInstances #-}
module Fin where

import Nat 

import Test.QuickCheck

import Data.Type.Equality

-----------------------------------------------------
-- Type
-----------------------------------------------------
data Fin (n :: Nat) where
    FZ :: Fin (S n)
    FS :: Fin n -> Fin (S n)

-- | Fold 'Fin' 
cata :: forall a n. a -> (a -> a) -> Fin n -> a
cata z f = go where
    go :: Fin m -> a
    go FZ = z
    go (FS n) = f (go n)

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

deriving instance Eq (Fin n)
deriving instance Ord (Fin n)

-- | 'Fin' is printed as 'Int'.
instance Show (Fin n) where show = show . toInt

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

-------------------------------------------------------------------------------
-- Plus-like operations
-------------------------------------------------------------------------------

-- | increase the bound of a Fin.
-- this is an identity function 
weakenLeft1 :: Fin n -> Fin (S n)
weakenLeft1 FZ = FZ
weakenLeft1 (FS f) = FS (weakenLeft1 f)


------------------------------------

pick :: Fin N2 -> a -> a -> a
pick f x y = case f of
    FZ -> x
    (FS _) -> y

-------------------------------------------------------------------------------
-- Aliases
-------------------------------------------------------------------------------


f0 :: Fin (S n)
f1 :: Fin (S (S n))
f2 :: Fin (S (S (S n)))

f0 = FZ
f1 = FS f0
f2 = FS f1
