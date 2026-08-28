{-# OPTIONS --erasure #-}

-- |
-- Module      : Data.Fin
-- Description : Bounded natural numbers
--
-- @Fin n@ is the type of de Bruijn indices in scope @n@: the finite set
-- @{0, 1, ..., n-1}@.
--
-- ERASURE: the scope @n@ is marked @\@0@ throughout.  It is a typing
-- invariant and nothing more -- exactly the status it has in Haskell,
-- where it lives at the type level and is erased before execution.  A
-- @Fin@ value is therefore just a unary number at runtime.
module Data.Fin where

open import Data.Prelude
open import Data.Nat public
open import Data.Type.Equality

data Fin : @0 Nat → Set where
  FZ : ∀ {@0 n} → Fin (S n)
  FS : ∀ {@0 n} → Fin n → Fin (S n)

------------------------------------------------------------------------
-- * Aliases
------------------------------------------------------------------------

-- Convenient names for fin values.  These have polymorphic types so
-- they will work in any scope.

f0 : ∀ {@0 n} → Fin (S n)
f0 = FZ

f1 : ∀ {@0 n} → Fin (S (S n))
f1 = FS f0

f2 : ∀ {@0 n} → Fin (S (S (S n)))
f2 = FS f1

f3 : ∀ {@0 n} → Fin (S (S (S (S n))))
f3 = FS f2

------------------------------------------------------------------------
-- * Elimination
------------------------------------------------------------------------

-- | There are no indices in the empty scope.  Haskell writes this as
-- the empty case expression @case x of {}@.
absurd : {A : Set} → Fin Z → A
absurd ()

------------------------------------------------------------------------
-- * Shifting
------------------------------------------------------------------------

-- "Weakening" means: adding a new binding to the front of the typing
-- context without changing existing indices.  "Shifting" means:
-- adjusting the indices of free variables within a term to reflect a
-- new binding added to the end of the context.

-- | Increment by a fixed amount (on the left).
--
-- Haskell needs an @SNat n@ here because @n@ is a type-level number.
-- Here @n@ is an ordinary, un-erased @Nat@ argument: we recurse on it,
-- so we ask for one that survives to runtime and no singleton is
-- needed.  The scope @m@, which we never inspect, stays erased.
shiftN : ∀ {@0 m} (n : Nat) → Fin m → Fin (n + m)
shiftN Z     i = i
shiftN (S n) i = FS (shiftN n i)

-- | Increment by one.
shift1 : ∀ {@0 m} → Fin m → Fin (S m)
shift1 = shiftN 1

------------------------------------------------------------------------
-- * Weakening
------------------------------------------------------------------------

-- | Weakening changes the bound of a nat-indexed type without changing
-- its value.  Rebound implements these with 'unsafeCoerce' (they are
-- identity functions); here they are real, if boring, recursions.

-- | Raise the bound on the left.
weakenFin : ∀ {@0 n} (m : Nat) → Fin n → Fin (m + n)
weakenFin {S k} m FZ     = subst Fin (axiomPlusS {m} {k}) FZ
weakenFin {S k} m (FS i) = subst Fin (axiomPlusS {m} {k}) (FS (weakenFin m i))

-- | Raise the bound on the right.
weakenFinRight : ∀ {@0 n} (m : Nat) → Fin n → Fin (n + m)
weakenFinRight m FZ     = FZ
weakenFinRight m (FS i) = FS (weakenFinRight m i)

weaken1Fin : ∀ {@0 n} → Fin n → Fin (S n)
weaken1Fin = weakenFin 1

------------------------------------------------------------------------
-- * Conversions and comparison
------------------------------------------------------------------------

toNat : ∀ {@0 n} → Fin n → Nat
toNat FZ     = Z
toNat (FS i) = S (toNat i)

-- | Haskell derives this; Agda spells it out.
eqFin : ∀ {@0 n} → Fin n → Fin n → Bool
eqFin FZ     FZ     = true
eqFin (FS i) (FS j) = eqFin i j
eqFin _      _      = false

------------------------------------------------------------------------
-- * Strengthening
------------------------------------------------------------------------

-- | Check that index @0@ is unused and decrement everything else.
strengthen1Fin : ∀ {@0 n} → Fin (S n) → Maybe (Fin n)
strengthen1Fin FZ     = Nothing
strengthen1Fin (FS i) = Just i

-- | Generalized strengthening: remove @m@ variables from the middle of
-- the scope @k + (m + n)@.  Indices below @k@ are unchanged, indices in
-- the @m@ range make it fail, and indices above are decremented.
strengthenRecFin : ∀ {@0 n} (k m : Nat) → Fin (k + (m + n)) → Maybe (Fin (k + n))
strengthenRecFin Z     Z     x      = Just x
strengthenRecFin Z     (S m) FZ     = Nothing
strengthenRecFin Z     (S m) (FS x) = strengthenRecFin Z m x
strengthenRecFin (S k) m     FZ     = Just FZ
strengthenRecFin (S k) m     (FS x) = FS <$> strengthenRecFin k m x
