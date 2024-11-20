module Vec where

--- replace with
-- https://hackage.haskell.org/package/fin
-- https://hackage.haskell.org/package/vec

-- Library for length-indexed lists
-- Should be imported qualified as it includes operations that
-- conflict with list operations in the Prelude

import Data.Type.Equality
import Fin
import Nat
import Test.QuickCheck
import Prelude hiding (lookup, repeat, zipWith)

-----------------------------------------------------
-- Vectors
-----------------------------------------------------

data Vec n a where
  VNil :: Vec Z a
  (:::) :: a -> Vec n a -> Vec (S n) a

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
