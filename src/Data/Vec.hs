module Data.Vec where

--- replace with
-- https://hackage.haskell.org/package/fin
-- https://hackage.haskell.org/package/vec

-- Library for length-indexed lists
-- Should be imported qualified as it includes operations that
-- conflict with list operations in the Prelude

import Data.Type.Equality
import Data.Fin hiding (enumFin)
import Data.Nat
import Test.QuickCheck
import Prelude hiding (lookup, repeat, zipWith)

-----------------------------------------------------
-- Vectors
-----------------------------------------------------

data Vec n a where
  VNil :: Vec Z a
  (:::) :: a -> Vec n a -> Vec (S n) a

infixr 7 :::

deriving instance Functor (Vec n)

deriving instance Foldable (Vec n)

deriving instance (Show a) => Show (Vec n a)

head :: Vec (S n) a -> a
head (x ::: _) = x

lookup :: Fin n -> Vec n a -> a
lookup FZ (v ::: _) = v
lookup (FS v) (_ ::: env) = lookup v env

(!) :: Vec n a -> Fin n -> a
v ! f = lookup f v

setAt :: Fin n -> Vec n a -> a -> Vec n a
setAt FZ (_ ::: vs) w = w ::: vs
setAt (FS x) (w1 ::: env) w2 = w1 ::: setAt x env w2

repeat :: SNat n -> a -> Vec n a
repeat SZ x = VNil
repeat (SS n) x = x ::: repeat n x

zipWith :: (a -> b -> c) -> Vec n a -> Vec n b -> Vec n c
zipWith f VNil VNil = VNil
zipWith f (x ::: xs) (y ::: ys) = f x y ::: zipWith f xs ys

append :: forall n m a. Vec n a -> Vec m a -> Vec (Plus n m) a
append VNil v = v
append (x ::: v) w = x ::: append v w

vlength :: Vec n a -> SNat n
vlength VNil = SZ
vlength (_ ::: v) = SS (vlength v)

-- | is there a non O(n^2) implementation of this function?
enumFin :: SNat n -> Vec n (Fin n)
enumFin SZ = VNil
enumFin (SS n) = FZ ::: fmap FS (enumFin n)

-- >>> enumFin s3
-- 0 ::: (1 ::: (2 ::: VNil))


-- enumFin :: SNat n -> Vec n (Fin n)
-- enumFin x = go x FZ where
--  go :: forall n m. SNat n -> Fin m -> Vec n (Fin _)
--  go SZ _ = VNil
--  go (SS n) f = f ::: go n (FS f)

tabulate :: SNat n -> (Fin n -> a) -> Vec n a
tabulate x f = fmap f (enumFin x)
