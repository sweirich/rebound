{-# OPTIONS --erasure #-}

-- | Substitution for the lambda calculus, with a real termination
-- proof.  There is no pragma anywhere in this file.
--
-- Every other example in this directory asserts termination of its
-- `applyE`.  The reason is always the same one call:
--
-- @
--   comp (Cons t s1) s2 = Cons (applyE s2 t) (comp s1 s2)
-- @
--
-- `t` is stored *inside* an environment, so it is a subterm of neither
-- argument and no structural order can see it.  A *size* order can:
-- `t` is strictly smaller than the environment holding it.  This file
-- carries that measure through, so Agda accepts the definitions
-- outright.
--
-- It is deliberately self-contained -- its own miniature `Exp`/`Env`
-- rather than "Rebound.Env" -- because threading the measure through the
-- real library would mean making it a method of `Subst`, and every
-- instance would then owe both a measure and its decrease proofs.  The
-- point here is to show that the proof exists and what it costs, not to
-- pay that cost everywhere.
--
-- Note what falls out: because substitution is *proved* terminating,
-- Agda is willing to reduce it, so the checks at the bottom are `Refl`
-- proofs run by the type checker rather than runtime tests.
module LCWF where

open import Data.Prelude
open import Data.Nat
open import Data.Fin
open import Data.Type.Equality

------------------------------------------------------------------------
-- * Order and well-foundedness
------------------------------------------------------------------------

-- The port depends on no standard library, so this is the scaffolding
-- the proof needs.  It would move to `Data.Nat` if the technique were
-- adopted for the library proper.

infix 4 _≤_ _<_
data _≤_ : Nat → Nat → Set where
  z≤n : ∀ {n}           → Z ≤ n
  s≤s : ∀ {m n} → m ≤ n → S m ≤ S n

_<_ : Nat → Nat → Set
m < n = S m ≤ n

≤-trans : ∀ {l m n} → l ≤ m → m ≤ n → l ≤ n
≤-trans z≤n     q       = z≤n
≤-trans (s≤s p) (s≤s q) = s≤s (≤-trans p q)

≤-refl : ∀ {n} → n ≤ n
≤-refl {Z}   = z≤n
≤-refl {S n} = s≤s ≤-refl

≤-step : ∀ {m n} → m ≤ n → m ≤ S n
≤-step z≤n     = z≤n
≤-step (s≤s p) = s≤s (≤-step p)

m≤m+n : ∀ m n → m ≤ m + n
m≤m+n Z     n = z≤n
m≤m+n (S m) n = s≤s (m≤m+n m n)

n≤m+n : ∀ m n → n ≤ m + n
n≤m+n Z     n = ≤-refl
n≤m+n (S m) n = ≤-step (n≤m+n m n)

-- | The only monotonicity lemma the proof needs.
+-monoʳ-< : ∀ k {m n} → m < n → k + m < k + n
+-monoʳ-< Z     p = p
+-monoʳ-< (S k) p = s≤s (+-monoʳ-< k p)

data Acc (n : Nat) : Set where
  acc : (∀ {m} → m < n → Acc m) → Acc n

<-wf : ∀ n → Acc n
<-wf n = acc (go n)
  where
    go : ∀ n {m} → m < n → Acc m
    go (S n) (s≤s p) = acc (λ q → go n (≤-trans q p))

------------------------------------------------------------------------
-- * Syntax
------------------------------------------------------------------------

-- As in the library, a binder suspends an environment rather than
-- pushing the substitution through eagerly.  That suspension is what
-- creates the knot.

data Exp : @0 Nat → Set
data Env : @0 Nat → @0 Nat → Set

data Exp where
  Var : ∀ {@0 n}   → Fin n → Exp n
  App : ∀ {@0 n}   → Exp n → Exp n → Exp n
  Lam : ∀ {@0 m n} → Env m n → Exp (S m) → Exp n

data Env where
  Id   : ∀ {@0 n}   → Env n n
  Cons : ∀ {@0 m n} → Exp n → Env m n → Env (S m) n

------------------------------------------------------------------------
-- * The measure
------------------------------------------------------------------------

size  : ∀ {@0 n}   → Exp n → Nat
sizeE : ∀ {@0 m n} → Env m n → Nat

size (Var x)      = 1
size (App a b)    = S (size a + size b)
size (Lam e body) = S (sizeE e + size body)

sizeE Id         = 1
sizeE (Cons t s) = S (size t + sizeE s)

-- Variable lookup is structural already, and needs no help.
lookupE : ∀ {@0 n m} → Env n m → Fin n → Exp m
lookupE Id         x      = Var x
lookupE (Cons t s) FZ     = t
lookupE (Cons t s) (FS x) = lookupE s x

------------------------------------------------------------------------
-- * Substitution, by recursion on the measure
------------------------------------------------------------------------

-- `applyA` is measured by  sizeE r  + size t
-- `compA`  is measured by  sizeE s2 + sizeE s1
--
-- Note the argument order in `compA`'s measure: the *second* environment
-- first.  That is not cosmetic.  With this ordering every obligation is
-- monotonicity in the right summand, so the whole proof needs the single
-- lemma `+-monoʳ-<`.  Measured the other way round, each of the five
-- sites additionally needs commutativity and a `subst`.

applyA : ∀ {@0 n m}   (r  : Env n m) (t  : Exp n)
       → Acc (sizeE r + size t) → Exp m
compA  : ∀ {@0 m n p} (s1 : Env m n) (s2 : Env n p)
       → Acc (sizeE s2 + sizeE s1) → Env m p

applyA r (Var x) _ = lookupE r x

applyA r (App a b) (acc rec) =
  App (applyA r a (rec (+-monoʳ-< (sizeE r) (s≤s (m≤m+n (size a) (size b))))))
      (applyA r b (rec (+-monoʳ-< (sizeE r) (s≤s (n≤m+n (size a) (size b))))))

applyA r (Lam e body) (acc rec) =
  Lam (compA e r (rec (+-monoʳ-< (sizeE r) (s≤s (m≤m+n (sizeE e) (size body))))))
      body

compA Id s2 _ = s2

-- The interesting clause.  `applyA s2 t` is the call with no structural
-- order -- `t` sits inside the environment -- and `size t < sizeE (Cons
-- t s1)` is exactly what licenses it.
compA (Cons t s1) s2 (acc rec) =
  Cons (applyA s2 t (rec (+-monoʳ-< (sizeE s2) (s≤s (m≤m+n (size t) (sizeE s1))))))
       (compA s1 s2 (rec (+-monoʳ-< (sizeE s2) (s≤s (n≤m+n (size t) (sizeE s1))))))

------------------------------------------------------------------------
-- * The interface: accessibility supplied once, then hidden
------------------------------------------------------------------------

applyE : ∀ {@0 n m} → Env n m → Exp n → Exp m
applyE r t = applyA r t (<-wf (sizeE r + size t))

comp : ∀ {@0 m n p} → Env m n → Env n p → Env m p
comp s1 s2 = compA s1 s2 (<-wf (sizeE s2 + sizeE s1))

------------------------------------------------------------------------
-- * It computes
------------------------------------------------------------------------

-- These are `Refl` proofs, so type-checking this file runs them.  None
-- of the other examples can state their substitution results this way:
-- their `applyE` is asserted rather than proved, so it is either
-- unfoldable-but-untrusted or (under NON_TERMINATING) not unfoldable at
-- all.

idExp : Exp Z
idExp = Lam Id (Var FZ)

-- [λ.0 / x] (x x)  =  (λ.0) (λ.0)
_ : applyE (Cons idExp (Id {Z})) (App (Var FZ) (Var FZ))
  ≡ App idExp idExp
_ = Refl

-- substitution under a binder suspends the environment there
_ : applyE (Cons idExp (Id {Z})) (Lam (Id {S Z}) (Var (FS FZ)))
  ≡ Lam (comp (Id {S Z}) (Cons idExp (Id {Z}))) (Var (FS FZ))
_ = Refl

-- and the suspension is forced on lookup
_ : lookupE (comp (Id {S Z}) (Cons idExp (Id {Z}))) FZ ≡ idExp
_ = Refl
