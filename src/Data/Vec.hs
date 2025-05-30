{-# LANGUAGE PatternSynonyms #-} 
module Data.Vec(
    Vec, Vec_(..), vec_, (|>), unCons, 
    empty,
    setAt, 
    Data.Vec.lookup,
    (!),
    append,
    vlength,
    veq,
    Data.Vec.iterateN,
    Data.Vec.tabulate,
    Data.Vec.induction
 ) where

-- Library for length-indexed lists
-- Should be imported qualified as it includes operations that
-- conflict with list operations in the Prelude

import GHC.Num.Natural
import Data.Type.Equality
import Data.Sequence (Seq, fromList)
import Data.Sequence qualified as Seq
import Test.QuickCheck
import Prelude hiding (lookup, repeat, zipWith)
import Data.SNat
import Data.Fin as Fin

import Unsafe.Coerce(unsafeCoerce)

-----------------------------------------------------
-- Vectors 
-----------------------------------------------------


newtype Vec (n :: Nat) a = UnsafeVec (Seq a)
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)
-- no semigroup, monoid b/c length changes
-- do we want Applicative, Monad?

empty :: Vec Z a
empty = UnsafeVec Seq.empty

cons :: a -> Vec n a -> Vec (S n) a
cons a (UnsafeVec s) = UnsafeVec (a Seq.:<| s)

(|>) :: a -> Vec n a -> Vec (S n) a
(|>) = cons

toSeq :: Vec n a -> Seq a
toSeq (UnsafeVec v) = v

data Vec_ (n :: Nat) a where
  VNil_ :: Vec_ Z a
  VCons_ :: a -> Vec n a -> Vec_ (S n) a 

vec_ :: Vec n a -> Vec_ n a 
vec_ (UnsafeVec s) = case Seq.viewl s of 
                        Seq.EmptyL -> unsafeCoerce VNil_
                        h Seq.:< tSeq -> unsafeCoerce VCons_ h tSeq

-- Helper function for matching the cons-pattern (:::)
-- This function explicitly handles the deconstruction and wrapping.
unCons :: Vec ('S n) a -> (a, Vec n a)
unCons (UnsafeVec s) =
  case Seq.viewl s of
    Seq.EmptyL    -> error "BUG: impossible case"
    h Seq.:< tSeq -> (h, UnsafeVec tSeq)


setAt :: Fin n -> Vec n a -> a -> Vec n a
setAt f (UnsafeVec v) x = UnsafeVec (Seq.update (toInt f) x v)

lookup :: Fin n -> Vec n a -> a
lookup n (UnsafeVec v) = v `Seq.index` (toInt n) 

-- Vectors are Representable. 
(!) :: Vec n a -> Fin n -> a
(UnsafeVec v) ! f = Seq.index v (toInt f) 

tabulate :: forall m a. SNatI m => (Fin m -> a) -> Vec m a
tabulate f = UnsafeVec (Seq.fromList v) where
    v = [ f x | x <- Fin.universe :: [Fin m] ]

append :: forall n m a. Vec n a -> Vec m a -> Vec (n + m) a
append (UnsafeVec v1) (UnsafeVec v2) = UnsafeVec (v1 <> v2)

vlength :: Vec n a -> SNat n
vlength (UnsafeVec v) = UnsafeSNat n where
    n :: Natural
    n = fromInteger (toInteger (Seq.length v))

-- | knowing that two vectors are equal means that their 
-- lengths are equal
veq :: Eq a => Vec n1 a -> Vec n2 a -> Maybe (n1 :~: n2)
veq (UnsafeVec v1) (UnsafeVec v2) = 
    if v1 == v2 then unsafeCoerce (Just Refl) else Nothing

-- 𝑂(𝑛)
-- Constructs a sequence by repeated application of a function to a seed value.
iterateN :: SNat n -> (a -> a) -> a -> Vec n a
iterateN n f x = 
    UnsafeVec (fromList (Prelude.take (toInt n) (Prelude.iterate f x)))



---------------------------------------------------------
-- Induction
---------------------------------------------------------


induction :: Vec n a -> v Z  -> (forall n. a -> v n -> v (S n)) -> v n
induction (UnsafeVec v) zero succ = undefined

