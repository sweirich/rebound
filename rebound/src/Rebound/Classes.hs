-- |
-- Module      : Rebound.Classes
-- Description : Type class definitions
-- Stability   : experimental
{-# LANGUAGE DefaultSignatures #-}
module Rebound.Classes where

import Rebound.Lib
import Data.LocalName
import Data.Scoped.List(List, pattern Nil, pattern (:<))
import Data.Scoped.List qualified as List

import Data.Foldable
import Data.Vec qualified as Vec
import Data.Fin qualified as Fin
import Data.Set (Set)
import Data.Set qualified as Set

import GHC.Generics (Generic1(..))

----------------------------------------------------------
-- Indices/variables shifting
----------------------------------------------------------
class Shiftable t where
  shift :: SNat k -> t n -> t (k + n)
  -- a good default implementation of this is `shiftFromApply`. But the 
  -- `Subst` class is not yet in scope.  
  
----------------------------------------------------------
-- Free variables
----------------------------------------------------------

class FV (t :: Nat -> Type) where
  -- | Does a particular variable appear free?
  appearsFree :: Fin n -> t n -> Bool
  default appearsFree :: (Generic1 t, GFV (Rep1 t)) => Fin n -> t n -> Bool
  appearsFree x e = gappearsFree x (from1 e)
  {-# INLINE appearsFree #-}

  -- | Calculate all of the free variables in a term
  freeVars :: t n -> Set (Fin n)
  default freeVars :: (Generic1 t, GFV (Rep1 t)) => t n -> Set (Fin n)
  freeVars e = gfreeVars (from1 e)
  {-# INLINE freeVars #-}

class GFV (t :: Nat -> Type) where
  gappearsFree :: Fin n -> t n -> Bool
  gfreeVars :: t n -> Set (Fin n)

----------------------------------------------------------
-- * Strengthening
----------------------------------------------------------

-- Strengthening cannot be implemented through substitution because it
-- must fail if the term uses invalid variables. Therefore, we make a
-- class of scoped types that can be strengthened.

-- entry point for eliminating the most recently bound variable from the scope (if unused)
strengthen :: forall n t. (Strengthen t, SNatI n) => t (S n) -> Maybe (t n)
strengthen = strengthenRec s0 s1 (snat :: SNat n)

-- n-ary version of strengthen
strengthenN :: forall m n t. (Strengthen t, SNatI n) => SNat m -> t (m + n) -> Maybe (t n)
strengthenN m = strengthenRec s0 m (snat :: SNat n)

class Strengthen t where
  -- generalize strengthening -- remove m variables from the middle of the scope
  strengthenRec :: SNat k -> SNat m -> SNat n -> t (k + (m + n)) -> Maybe (t (k + n))
  default strengthenRec :: (Generic1 t, GStrengthen (Rep1 t)) =>
     SNat k -> SNat m -> SNat n -> t (k + (m + n)) -> Maybe (t (k + n))
  strengthenRec k m n t = to1 <$> gstrengthenRec k m n (from1 t)

  -- Remove a single variable from the middle of the scope
  strengthenOneRec :: forall k n. SNat k -> SNat n -> t (k + S n) -> Maybe (t (k + n))
  strengthenOneRec k = strengthenRec k s1

class GStrengthen (t :: Nat -> Type) where
  gstrengthenRec :: SNat k -> SNat m -> SNat n -> t (k + (m + n)) -> Maybe (t (k + n))

----------------------------------------------------------
-- FV and Strengthen instances for Data.Scoped.List
---------------------------------------------------------

instance FV t => FV (List t) where
  appearsFree :: Fin n -> List t n -> Bool
  appearsFree x = List.any (appearsFree x)

  freeVars :: List t n -> Set (Fin n)
  freeVars = List.foldr (\x s -> freeVars x `Set.union` s) Set.empty

instance Strengthen t => Strengthen (List t) where
  strengthenRec :: SNat k -> SNat m -> SNat n -> List t (k + (m + n)) -> Maybe (List t (k + n))
  strengthenRec k m n Nil = Just Nil
  strengthenRec k m n (x :< xs) = (:<) <$> strengthenRec k m n x <*> strengthenRec k m n xs

----------------------------------------------------------
-- FV and Strengthen instances for Fin
---------------------------------------------------------

instance FV Fin where
  appearsFree = (==)
  freeVars = Set.singleton

instance Strengthen Fin where
  strengthenRec :: SNat k -> SNat m -> SNat n-> Fin (k + (m + n)) -> Maybe (Fin (k + n))
  strengthenRec = Fin.strengthenRecFin

-- | Update a set of free variables to a new scope through strengthening
rescope :: forall n k. SNat k -> Set (Fin (k + n)) -> Set (Fin n)
rescope k = foldMap g where
   g :: Fin (k + n) -> Set (Fin n)
   g x = maybe
     Set.empty Set.singleton
     (Fin.strengthenRecFin s0 k (undefined :: SNat n) x)

----------------------------------------------------------
-- Type classes for patterns
----------------------------------------------------------

-- | Calculate the number of binding variables in the pattern
-- This number does not need to be an explicit parameter of the type
-- so that we have flexibility about what types we can use as
-- patterns.
class Sized (t :: Type) where
  -- Retrieve size from the type (number of variables bound by the pattern)
  type Size t :: Nat
  -- Access size as a term
  size :: t -> SNat (Size t)

-- | Pairs of types that can be compared with each other as patterns
class PatEq (t1 :: Type) (t2 :: Type) where
    patEq :: t1 -> t2 -> Maybe (Size t1 :~: Size t2)

-- | Class of patterns that are indexed by a natural number
-- where the size is that index directly
class (Sized (t p), Size (t p) ~ p) => SizeIndex t p


---------------------------------------------------------
-- Pattern Class Instances for Prelude and Lib Types
---------------------------------------------------------

-- ** LocalNames

instance Sized LocalName where
  type Size LocalName = N1
  size _ = s1

instance PatEq LocalName LocalName where
  patEq p1 p2 = Just Refl

-- ** SNats
instance Sized (SNat n) where
  type Size (SNat n) = n
  size n = n

instance PatEq (SNat n1) (SNat n2) where
  patEq = testEquality


-- ** Vectors

instance Sized (Vec n a) where
  type Size (Vec n a) = n
  size = Vec.vlength

instance Eq a => PatEq (Vec n1 a) (Vec n2 a) where
  patEq :: Eq a => Vec n1 a -> Vec n2 a -> Maybe (Size (Vec n1 a) :~: Size (Vec n2 a))
  patEq = Vec.veq

-- ** Unit (trivial)

instance Sized () where { type Size () = N0 ;  size _ = SZ }

instance PatEq () () where patEq _ _ = Just Refl

-- ** Pairs

instance (Sized a, Sized b) => Sized (a,b) where
   type Size (a,b) = Size a + Size b
   size (x,y) = sPlus (size x) (size y)

instance (PatEq a1 a2, PatEq b1 b2) => PatEq (a1, b1) (a2, b2) where
   patEq (x1,y1) (x2,y2)
     | Just Refl <- patEq x1 x2
     , Just Refl <- patEq y1 y2
     = Just Refl
   patEq _ _ = Nothing

------------------------------------------


