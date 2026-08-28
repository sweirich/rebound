{-# OPTIONS --erasure #-}

-- |
-- Module      : Data.Singleton
-- Description : Runtime copies of erased values
--
-- This module replaces rebound's @Data.SNat@.
--
-- In Haskell, a number that appears in a type is erased before
-- execution, so getting one back at runtime needs a bespoke singleton
-- /type/ that mirrors the structure of the thing being reflected:
--
-- @
-- data SNat (n :: Nat) where
--   SZ :: SNat Z
--   SS :: SNat n -> SNat (S n)
-- @
--
-- plus a class (@SNatI@) to pass one implicitly, a @withSNat@ to
-- introduce one, and a fresh copy of all three for every other index
-- type you care about.
--
-- In Agda erasure is a modality on ordinary values rather than a
-- separation between two levels, so none of that duplication is needed.
-- A runtime copy of an erased @x@ is just a runtime value together with
-- an erased proof that it /is/ @x@ -- one four-line record, generic in
-- the type, and the singleton constructors disappear because @Nat@
-- already has the ones we want.
--
-- (This is the @Singleton@ of Danielsson's "Logical properties of a
-- modality for erasure"; @∃ λ y → Erased (y ≡ x)@ written as a record.)
module Data.Singleton where

open import Data.Nat public
open import Data.Prelude
open import Data.Type.Equality

------------------------------------------------------------------------
-- * Singletons
------------------------------------------------------------------------

record Singleton {A : Set} (@0 x : A) : Set where
  constructor ⟨_,_⟩
  field
    value    : A
    @0 proof : value ≡ x
open Singleton public

-- | When the value is still in hand, the proof is free.  (Haskell's
-- @snat@, which must recurse to build the singleton.)
sing : {A : Set} (x : A) → Singleton x
sing x = ⟨ x , Refl ⟩

-- Pattern matching a singleton as @⟨ k , Refl ⟩@ binds the runtime copy
-- @k@ /and/ rewrites the erased index to it, so the rest of a definition
-- can just compute with @k@.  That is the whole interface.

------------------------------------------------------------------------
-- * Naturals
------------------------------------------------------------------------

s0 : Singleton N0
s0 = sing N0

s1 : Singleton N1
s1 = sing N1

s2 : Singleton N2
s2 = sing N2

s3 : Singleton N3
s3 = sing N3

ssuc : ∀ {@0 n} → Singleton n → Singleton (S n)
ssuc ⟨ k , Refl ⟩ = sing (S k)

-- | Haskell's @sPlus@ recurses on the singleton structure; here the
-- addition is the one from 'Data.Nat'.
sPlus : ∀ {@0 m n} → Singleton m → Singleton n → Singleton (m + n)
sPlus ⟨ j , Refl ⟩ ⟨ k , Refl ⟩ = sing (j + k)

-- | Compare two singletons, producing evidence about their (erased)
-- indices.  (Haskell: @testEquality \@SNat@.)
singEq : ∀ {@0 m n : Nat} → Singleton m → Singleton n → Maybe (Erased (m ≡ n))
singEq ⟨ j , Refl ⟩ ⟨ k , Refl ⟩ = natEq j k

------------------------------------------------------------------------
-- * Implicit singletons
------------------------------------------------------------------------

-- Haskell needs a separate class, @SNatI@, to pass a singleton
-- implicitly.  A 'Singleton' is already a record, so it can serve as an
-- instance argument directly -- see @Rebound.Env._++_@.

instance
  SingletonZ : Singleton Z
  SingletonZ = sing Z

  SingletonS : ∀ {@0 n} {{_ : Singleton n}} → Singleton (S n)
  SingletonS {{s}} = ssuc s

-- | Supply a singleton where an implicit one is expected.
-- (Haskell's @withSNat@, which here is just instance application.)
withSingleton : ∀ {A B : Set} {@0 x : A} → Singleton x → ({{_ : Singleton x}} → B) → B
withSingleton s f = f {{s}}
