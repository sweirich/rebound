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
{-# LANGUAGE AllowAmbiguousTypes #-}
module Fin where

import Nat 

import Test.QuickCheck

import Data.Type.Equality

import Unsafe.Coerce ( unsafeCoerce )


-- a property about addition
axiom :: forall m n. Plus m (S n) :~: S (Plus m n)
axiom = unsafeCoerce Refl

-- that property generalized to +m
axiomM :: forall m p n. Plus p (Plus m n) :~: Plus m (Plus p n)
axiomM = unsafeCoerce Refl

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
-- Weakening and Strengthening
-------------------------------------------------------------------------------

-- Weakenening and Strengthening just change the bound of a nat-indexed type.
-- These operations can either be defined for the n-ary case (as in Fin below)
-- or be defined in terms of a single-step operation (though the latter is likely
-- to be inefficient.)
-- Both of these operations should be identity functions, so it would also be 
-- justified to use unsafeCoerce.


-- | weaken the bound of a Fin by an arbitrary amount
-- We don't overload this function because we can use substitution 
-- to implement weakening most of the type
weakenFin :: SNat m -> Fin n -> Fin (Plus m n)
weakenFin SZ f = f 
weakenFin (SS m) FZ = FZ
weakenFin (SS (m :: SNat m0)) (FS (f :: Fin n0)) = case axiom @m0 @n0 of 
        Refl -> FS (weakenFin (SS m) f)

weaken1Fin :: Fin n -> Fin (S n)
weaken1Fin = weakenFin s1


-- Strengthening cannot be implemented through substitution because it 
-- must fail if the term uses invalid variables. Therefore, we make a 
-- class of nat-indexed types that can be strengthened.

class CoerceIndex t where
    weakenOne :: t n -> t (S n)
    weakenOne = weaken' (SS SZ)

    strengthenOne' :: SNat n -> t (S n) -> Maybe (t n)
    strengthenOne' = strengthen' (SS SZ)

    weaken' :: SNat m -> t n -> t (Plus m n)
    weaken' SZ t = t 
    weaken' (SS m1) t = weakenOne (weaken' m1 t)

    strengthen' :: SNat m -> SNat n -> t (Plus m n) -> Maybe (t n)
    strengthen' SZ n f = Just f
    strengthen' (SS m) SZ f = Nothing
    strengthen' (SS m) (SS n) f = do 
        f' <- strengthenOne' (sPlus m (SS n)) f 
        strengthen' m (SS n) f'
    
weaken :: forall m n t. (CoerceIndex t, SNatI m) => t n -> t (Plus m n)
weaken = weaken' (snat :: SNat m)

strengthen :: forall m n t. (CoerceIndex t, SNatI m, SNatI n) => t (Plus m n) -> Maybe (t n)
strengthen = strengthen' (snat :: SNat m) (snat :: SNat n)

instance CoerceIndex Fin where 
    weaken' :: SNat m -> Fin n -> Fin (Plus m n)
    weaken' = weakenFin

    strengthen' :: SNat m -> SNat n -> Fin (Plus m n) -> Maybe (Fin n)
    strengthen' = strengthenFin

strengthenFin :: forall m n. SNat m -> SNat n -> Fin (Plus m n) -> Maybe (Fin n)
strengthenFin SZ SZ f = Just f
strengthenFin (SS m) SZ f = Nothing
strengthenFin m (SS n) FZ = Just FZ
strengthenFin m (SS (n0 :: SNat n0)) (FS f) = 
    case axiom @m @n0 of 
        Refl -> FS <$> strengthenFin m n0 f

    

t0 :: Fin N3
t0 = FZ 

-- >>> strengthenOne' (SS (SS SZ)) t0 :: Maybe (Fin N2)
-- Just 0

-- >>> strengthen' (SS (SS SZ)) (SS SZ) t0 :: Maybe (Fin N1)
-- Just 0


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
