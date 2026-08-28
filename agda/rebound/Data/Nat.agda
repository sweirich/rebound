{-# OPTIONS --erasure #-}

-- |
-- Module      : Data.Nat
-- Description : Unary natural numbers and their (few) laws
module Data.Nat where

open import Data.Prelude using (Bool; true; false; Maybe; Just; Nothing; _<$>_;
                                Erased; [_]; emap; ⊤)
open import Agda.Builtin.FromNat public using (Number; fromNat)
import Agda.Builtin.Nat as Builtin
open import Data.Type.Equality

------------------------------------------------------------------------
-- * Unary natural (Peano) numbers
------------------------------------------------------------------------

data Nat : Set where
  Z : Nat
  S : Nat → Nat

-- Agda's @NATURAL@ builtin is already bound to 'Agda.Builtin.Nat.Nat'
-- (pulled in by 'Agda.Builtin.String'), so numeric literals are given
-- for this type by the overloaded-literal class instead.  @3@ still
-- means @S (S (S Z))@.
fromBuiltin : Builtin.Nat → Nat
fromBuiltin Builtin.zero    = Z
fromBuiltin (Builtin.suc n) = S (fromBuiltin n)

instance
  NumberNat : Number Nat
  NumberNat .Number.Constraint _ = ⊤
  NumberNat .Number.fromNat    n = fromBuiltin n

------------------------------------------------------------------------
-- * Addition
------------------------------------------------------------------------

-- In Haskell this is a closed type family @(+)@ /and/ a value-level
-- function; the two are connected only through the singleton type
-- @SNat@.  In Agda there is just one definition, used at both levels --
-- the @\@0@ annotations below decide, per occurrence, which one we mean.
infixl 6 _+_
_+_ : Nat → Nat → Nat
Z   + n = n
S m + n = S (m + n)

------------------------------------------------------------------------
-- * Aliases
------------------------------------------------------------------------

N0 : Nat
N0 = Z

N1 : Nat
N1 = S N0

N2 : Nat
N2 = S N1

N3 : Nat
N3 = S N2

------------------------------------------------------------------------
-- * Laws
------------------------------------------------------------------------

-- Nat-indexed scopes are degenerate lists (i.e. typing contexts), so we
-- only ever need the monoid properties of @+@:
--
--       Z + n ≡ n                   -- true by definition
--       n + Z ≡ n                   -- axiomPlusZ
--       p + (m + n) ≡ (p + m) + n   -- axiomAssoc
--
-- Rebound calls these "axioms" because in Haskell they are implemented
-- with 'unsafeCoerce': GHC's coercion language has no induction, and a
-- real inductive proof would have to be /run/ at runtime (and would need
-- an 'SNat' witness to recurse on).
--
-- ERASURE: here each one is an @\@0@ definition.  That is the precise
-- statement of what rebound wanted and could not have -- a proof that
-- really is erased, so nothing is run, yet really is a proof, so nothing
-- is assumed.  Because they are erased they may also recurse on erased
-- indices, which is why no 'SNat' has to be threaded through.

-- | @Z@ is the right identity of @+@.
@0 axiomPlusZ : ∀ {@0 m} → m + Z ≡ m
axiomPlusZ {Z}   = Refl
axiomPlusZ {S m} = cong S (axiomPlusZ {m})

-- | @+@ is associative.
@0 axiomAssoc : ∀ {@0 p m n} → p + (m + n) ≡ (p + m) + n
axiomAssoc {Z}   = Refl
axiomAssoc {S p} = cong S (axiomAssoc {p})

-- | @S@ commutes with @+@ on the right.  (Not needed in the Haskell:
-- there, @Inc@ is taken apart by @unsafeCoerce@-backed axioms.)
@0 axiomPlusS : ∀ {@0 m n} → S (m + n) ≡ m + S n
axiomPlusS {Z}   = Refl
axiomPlusS {S m} = cong S (axiomPlusS {m})

-- | The same statement with the argument explicit, matching the shape
-- of @lemmaAssoc@ in the Haskell talk.
@0 lemmaAssoc : ∀ (@0 p : Nat) {@0 m n} → p + (m + n) ≡ (p + m) + n
lemmaAssoc Z     = Refl
lemmaAssoc (S p) = cong S (lemmaAssoc p)

------------------------------------------------------------------------
-- * Comparison
------------------------------------------------------------------------

-- | Haskell derives this.
eqNat : Nat → Nat → Bool
eqNat Z     Z     = true
eqNat (S m) (S n) = eqNat m n
eqNat _     _     = false

-- | Decide equality, producing evidence.  The 'Erased' says that the
-- answer is real data but the proof is not.
natEq : (j k : Nat) → Maybe (Erased (j ≡ k))
natEq Z     Z     = Just [ Refl ]
natEq (S j) (S k) = emap (cong S) <$> natEq j k
natEq _     _     = Nothing

leNat : Nat → Nat → Bool
leNat Z     n     = true
leNat (S m) Z     = false
leNat (S m) (S n) = leNat m n
