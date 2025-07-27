-- | Library for length-indexed lists
-- reexports https://hackage.haskell.org/package/vec
-- Should be imported qualified as it includes operations that
-- conflict with list operations in the Prelude
module Data.Vec
  ( module Data.Vec.Lazy,
    vlength,
    append,
    setAt,
    all2
 ) where

-- based on
-- https://hackage.haskell.org/package/fin


import Data.Fin (Fin (..))
import Data.Fin qualified
import Data.Nat
import Data.SNat
import Data.Type.Equality
import Data.Vec.Lazy
import Test.QuickCheck
import Prelude hiding (lookup, repeat, zipWith)

-----------------------------------------------------
-- Vectors (additional definitions)
-----------------------------------------------------

-- | Update a vector value at a given index
setAt :: Fin n -> Vec n a -> a -> Vec n a
setAt FZ (_ ::: vs) w = w ::: vs
setAt (FS x) (w1 ::: env) w2 = w1 ::: setAt x env w2

-- | Concatenate two vectors
append :: forall n m a. Vec n a -> Vec m a -> Vec (n + m) a
append = (Data.Vec.Lazy.++)

-- | Access elements by position
lookup :: Fin n -> Vec n a -> a
lookup = flip (!)

-- | Calculate length as a singleton value
vlength :: Vec n a -> SNat n
vlength VNil = SZ
vlength (_ ::: v) = withSNat (vlength v) SS


-- >>> all (\x -> x > 3) (4 ::: 5 ::: VNil)
-- True

-- | Ensure that a binary predicate holds for 
-- corresponding elements in two vectors
all2 :: (a -> b -> Bool) -> Vec n a -> Vec n b -> Bool
all2 f (x ::: xs) (y ::: ys) = f x y && all2 f xs ys
all2 f VNil VNil = True
