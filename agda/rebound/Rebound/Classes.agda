{-# OPTIONS --erasure #-}

-- |
-- Module      : Rebound.Classes
-- Description : Type class definitions
--
-- The main type classes used by the library, as Agda records used
-- through instance arguments.
module Rebound.Classes where

open import Rebound.Lib
open import Data.Fin using (strengthenRecFin)

------------------------------------------------------------------------
-- * Type classes for patterns
------------------------------------------------------------------------

-- | Calculate the number of binding variables in a pattern.
--
-- In Haskell this is
--
-- @
-- class Sized t where
--   type Size t :: Nat
--   size :: t -> SNat (Size t)
-- @
--
-- ERASURE: this is the sharpest illustration in the port.  @Size@ is a
-- number we only ever need in types, so it is @\@0@ -- and that makes it
-- unreadable at runtime, so @size@ is needed to reconstruct it, and
-- @size@ must return a 'Singleton' to tie the reconstruction back to the
-- erased index.
--
-- That is Haskell's class, field for field, but reached from the erasure
-- annotation rather than from a language restriction.  Leaving @theSize@
-- un-erased would make @size@ unnecessary and collapse the class to a
-- single number, at the price of every pattern value carrying its size
-- at runtime.  The annotation is what buys the Haskell shape.
record Sized (A : Set) : Set where
  field
    @0 theSize : Nat
    size       : A → Singleton theSize

-- | Written @Size t@ in Haskell.  Erased: it may be used in types, never
-- run.  The type argument is explicit so that Agda can find the instance.
@0 Size : (A : Set) {{s : Sized A}} → Nat
Size A {{s}} = Sized.theSize s

-- | The runtime witness for 'Size'.
size : {A : Set} {{s : Sized A}} → A → Singleton (Size A)
size {{s}} = Sized.size s

instance
  -- A singleton is its own size witness.
  SizedSingleton : ∀ {@0 n} → Sized (Singleton n)
  SizedSingleton {n} = record { theSize = n ; size = λ s → s }

  Sized⊤ : Sized ⊤
  Sized⊤ = record { theSize = N0 ; size = λ _ → s0 }

  SizedΣ : ∀ {A B : Set} {{_ : Sized A}} {{_ : Sized B}} → Sized (A × B)
  SizedΣ {A} {B} =
    record { theSize = Size A + Size B
           ; size    = λ p → sPlus (size (fst p)) (size (snd p)) }

------------------------------------------------------------------------
-- * Comparing patterns
------------------------------------------------------------------------

-- | Compare two nat-indexed values, even when we do not statically know
-- that their indices agree.  Haskell's @Data.Type.Equality.TestEquality@.
--
-- The result is @Maybe (Erased _)@: whether the comparison succeeded is
-- real data, the equality proof is not.  This is the case the talk singles out as
-- the good one -- evidence produced for free by a comparison we had to
-- do anyway, and free to pass around afterwards.
record TestEquality (t : @0 Nat → Set) : Set where
  field
    testEquality : ∀ {@0 a b} → t a → t b → Maybe (Erased (a ≡ b))
open TestEquality {{...}} public

instance
  TestEqualitySingleton : TestEquality (Singleton {Nat})
  TestEquality.testEquality TestEqualitySingleton = singEq

-- | Pairs of types that can be compared with each other as patterns.
record PatEq (A B : Set) {{_ : Sized A}} {{_ : Sized B}} : Set where
  field
    patEq : A → B → Maybe (Erased (Size A ≡ Size B))

------------------------------------------------------------------------
-- * Strengthening
------------------------------------------------------------------------

-- Strengthening cannot be implemented through substitution, because it
-- must fail if the term uses a variable that is going away.  So it gets
-- its own class.
--
-- Haskell passes three @SNat@s; here @k@ and @m@ are ordinary numbers we
-- recurse on, and @n@ appears only in the types, so it stays erased.
record Strengthen (t : @0 Nat → Set) : Set where
  field
    strengthenRec : ∀ {@0 n} (k m : Nat) → t (k + (m + n)) → Maybe (t (k + n))
open Strengthen {{...}} public

-- | Eliminate the @m@ most recently bound variables, if unused.
strengthenN : ∀ {t} {{_ : Strengthen t}} {@0 n} (m : Nat) → t (m + n) → Maybe (t n)
strengthenN m = strengthenRec 0 m

-- | Eliminate the most recently bound variable, if unused.
strengthen : ∀ {t} {{_ : Strengthen t}} {@0 n} → t (S n) → Maybe (t n)
strengthen = strengthenRec 0 1

instance
  StrengthenFin : Strengthen Fin
  Strengthen.strengthenRec StrengthenFin = strengthenRecFin

------------------------------------------------------------------------
-- * Free variables
------------------------------------------------------------------------

-- Haskell's class also has @freeVars :: t n -> Set (Fin n)@.  The port
-- has no set type, so only the membership test is provided; it is the
-- half the examples actually use.
record FV (t : @0 Nat → Set) : Set where
  field
    appearsFree : ∀ {@0 n} → Fin n → t n → Bool
open FV {{...}} public

instance
  FVFin : FV Fin
  FV.appearsFree FVFin = eqFin
