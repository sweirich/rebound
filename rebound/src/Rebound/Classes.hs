-- |
-- Module      : Rebound.Classes
-- Description : Type class definitions
-- Stability   : experimental
{-# LANGUAGE DefaultSignatures #-}
module Rebound.Classes where

import Rebound.Lib
import Data.Fin
import Data.Foldable
import Data.Vec qualified as Vec
import Data.Fin
import Data.Set (Set)
import qualified Data.Set as Set

import GHC.Generics hiding (S)

----------------------------------------------------------
-- Indices/variables shifting
----------------------------------------------------------
class Shiftable t where
  shift :: SNat k -> t n -> t (k + n)
  -- default shift :: forall v k n. (SubstVar v, Subst v t) => SNat k -> t n -> t (k + n)
  -- shift = shiftFromApplyE @v

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

----------------------------------------------------------
-- Fin and Strengthen instances for Fin
---------------------------------------------------------

instance FV Fin where
  appearsFree = (==)
  freeVars = Set.singleton

instance Strengthen Fin where
  strengthenRec :: SNat k -> SNat m -> SNat n-> Fin (k + (m + n)) -> Maybe (Fin (k + n))
  strengthenRec = strengthenRecFin

-- | Update a set of free variables to a new scope through strengthening
rescope :: forall n k. SNat k -> Set (Fin (k + n)) -> Set (Fin n)
rescope k s = foldMap g s where
   g :: Fin (k + n) -> Set (Fin n)
   g x = case strengthenRecFin s0 k (undefined :: SNat n) x of
           Nothing -> Set.empty
           Just f -> Set.singleton f

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
  patEq VNil VNil = Just Refl
  patEq (x ::: xs) (y ::: ys) | x == y,
    Just Refl <- patEq xs ys
    = Just Refl
  patEq _ _ = Nothing

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






--------------------------------------------
-- Generic implementation of FV class
--------------------------------------------

class GFV (t :: Nat -> Type) where
  gappearsFree :: Fin n -> t n -> Bool
  gfreeVars :: t n -> Set (Fin n)

instance (FV t) => GFV (Rec1 t) where
  gappearsFree s (Rec1 f) = appearsFree s f
  {-# INLINE gappearsFree #-}
  gfreeVars (Rec1 f) = freeVars f
  {-# INLINE gfreeVars #-}

-- Constant types
instance GFV (K1 i c) where
  gappearsFree s (K1 c) = False
  {-# INLINE gappearsFree #-}
  gfreeVars (K1 c) = Set.empty
  {-# INLINE gfreeVars #-}

instance GFV U1 where
  gappearsFree _s U1 = False
  {-# INLINE gappearsFree #-}
  gfreeVars U1 = Set.empty

instance GFV f => GFV (M1 i c f) where
  gappearsFree s = gappearsFree s . unM1
  {-# INLINE gappearsFree #-}
  gfreeVars = gfreeVars . unM1
  {-# INLINE gfreeVars #-}

instance GFV V1 where
  gappearsFree _s = error "BUG: void type"
  {-# INLINE gappearsFree #-}
  gfreeVars v = error "BUG: void type"
  {-# INLINE gfreeVars #-}

instance (GFV f, GFV g) => GFV (f :*: g) where
  gappearsFree s (f :*: g) = gappearsFree s f && gappearsFree s g
  {-# INLINE gappearsFree #-}
  gfreeVars (f :*: g) = gfreeVars f <> gfreeVars g
  {-# INLINE gfreeVars #-}

instance (GFV f, GFV g) => GFV (f :+: g) where
  gappearsFree s (L1 f) = gappearsFree s f
  gappearsFree s (R1 g) = gappearsFree s g
  {-# INLINE gappearsFree #-}

  gfreeVars (L1 f) = gfreeVars f
  gfreeVars (R1 g) = gfreeVars g
  {-# INLINE gfreeVars #-}

------------------------------------------------
-- Generic implementation of Strengthening class
------------------------------------------------

class GStrengthen (t :: Nat -> Type) where
  gstrengthenRec :: SNat k -> SNat m -> SNat n -> t (k + (m + n)) -> Maybe (t (k + n))

instance GStrengthen (K1 i c) where
  gstrengthenRec m n k (K1 c) = pure (K1 c)
  {-# INLINE gstrengthenRec #-}

instance GStrengthen U1 where
  gstrengthenRec m n k U1 = pure U1
  {-# INLINE gstrengthenRec #-}

instance GStrengthen f => GStrengthen (M1 i c f) where
  gstrengthenRec m n k x = M1 <$> gstrengthenRec m n k (unM1 x)
  {-# INLINE gstrengthenRec #-}

instance GStrengthen V1 where
  gstrengthenRec m n k = error "BUG: void type"
  {-# INLINE gstrengthenRec #-}

instance (GStrengthen f, GStrengthen g) => GStrengthen (f :*: g) where
  gstrengthenRec m n k (f :*: g) = (:*:) <$> gstrengthenRec m n k f <*> gstrengthenRec m n k g
  {-# INLINE gstrengthenRec #-}

instance (GStrengthen f, GStrengthen g) => GStrengthen (f :+: g) where
  gstrengthenRec m n k (L1 f) = L1 <$> gstrengthenRec m n k f
  gstrengthenRec m n k (R1 g) = R1 <$> gstrengthenRec m n k g
  {-# INLINE gstrengthenRec #-}

instance Strengthen t => GStrengthen (Rec1 t) where
  gstrengthenRec k m n (Rec1 t) = Rec1 <$> strengthenRec k m n t