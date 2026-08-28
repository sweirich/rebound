{-# OPTIONS --erasure #-}
{-

  Part II: Another "Pearl" -- dependently-typed environments
    via ShiftLists

  ---------------------------------------------------------------------
  Agda transcription of Talks.Hs26.Talk2.  This is the part of the talk
  where Haskell and Agda diverge the most, because the whole section is
  about the two things Agda does not have to worry about:

    * singleton types (SNat), needed only because GHC erases type-level
      numbers before execution; and

    * arithmetic "axioms" proved by unsafeCoerce, needed only because
      GHC's coercion language has no induction.

  Marking the erasable parts with "@0" makes the comparison exact.  The
  scopes of `Tm` and `Env` are erased, just as they are in GHC.  The
  shift amount stored in a `Shift` node is deliberately *not*: we recurse
  on it, so we ask for a number that survives to runtime.  Haskell cannot
  make that request -- a type-level `k` is always erased -- which is why
  rebound has to store an `SNat k` next to it.

  Look for the "AGDA:" notes.
  ---------------------------------------------------------------------

-}

module Talk2 where

-- Use library definitions for Nat, Fin, etc.
open import Data.Fin
open import Rebound.Lib hiding (sym; cong; subst)
--                          the equality machinery is spelled out below

------------------------------------------------------------
-- * Recap of Part I: Well-scoped AST + interpreter
------------------------------------------------------------

data Tm : @0 Nat → Set where
  Var : ∀ {@0 n} → Fin n → Tm n
  App : ∀ {@0 n} → Tm n → Tm n → Tm n
  Lam : ∀ {@0 n} → Tm (S n) → Tm n

data Val : Set where
  VLam : Tm (S Z) → Val

------------------------------------------------------------
-- * Need environments with rich interface
------------------------------------------------------------

-- lookup a variable (total operation!)
--   _!_    : Env m n → Fin m → Tm n

-- identity substitution, does not modify scope
--   idE    : Env n n

-- extend with new definition (cons)
--   _∷_    : Tm n → Env m n → Env (S m) n

-- lift under binder: new variable maps to itself;
-- all others are shifted to the extended scope
--   up     : Env m n → Env (S m) (S n)
--   up s = Var FZ ∷ shiftE s

-- shift to a larger scope
--   shiftE : Env m n → Env m (S n)


------------------------------------------------------------------------
-- * Many implementations
------------------------------------------------------------------------

-- Functions (e.g. Fin m → Tm n, from Part I)
-- Length-indexed lists (e.g. Vec m (T n))
-- Defunctionalized interface (cf. Agda)
-- Shift-Skewed binary tree (cf. Rocq)

-- OR: non-dependent implementation using phantom types

-- NOTE: Claude is very good at ornamentation


------------------------------------------------------------
-- * ShiftLists
------------------------------------------------------------

-- Recall:
--    up env = Var FZ ∷ shiftE env
--
--    shiftE env = applyE (Var ∘ FS) ∘ env
--
-- "applyE" weakens each term in the range of env
-- But, *every* binder shifts---this is expensive!
-- Can we fuse multiple traversals?


-- **Key idea**: represent env as a length-indexed list, with
-- interspersed, **delayed** n-ary shifting

-- (This is a *very* simplified version of Rocq's implementation.
-- adapted from https://mathisbd.github.io/blog/esubstitutions.html
-- and ornamented with scope indices.)

------------------------------------------------------------
-- * ShiftList implementation
------------------------------------------------------------

-- AGDA: the Haskell writes `Shift :: SNat k -> Env m n -> Env m (k + n)`
-- -- two copies of the same number, one in the type (erased) and one in
-- the term (not).  Here there is one `Nat`, left un-erased because we
-- compute with it, and it *is* the index in the type.  The scopes `m`
-- and `n`, which we never inspect, are erased.
data Env : @0 Nat → @0 Nat → Set where
  Id    : ∀ {@0 m}     → Env m m
  Cons  : ∀ {@0 m n}   → Tm n → Env m n → Env (S m) n
  Shift : ∀ {@0 m n} (k : Nat) → Env m n → Env m (k + n)

idE : ∀ {@0 n} → Env n n
idE = Id

infixr 5 _∷_
_∷_ : ∀ {@0 m n} → Tm n → Env m n → Env (S m) n
_∷_ = Cons

-- smart "shift" operation, fuses multiple shifts
shiftE : ∀ {@0 m n} → Env m n → Env m (S n)
shiftE (Shift k e) = Shift (S k) e
shiftE e           = Shift 1 e

------------------------------------------------------------
-- * ASIDE: SNat, and when you still need it
------------------------------------------------------------

-- The Haskell talk needs a detour here:
--
--   The type `SNat` provides *runtime* access to type-level natural
--   numbers.  This is because, in Haskell, numbers that appear in
--   types are erased before execution.
--
--     >>> :t s0
--     >>> :t sPlus
--     >>> toInt (sPlus s2 s3)
--     5
--
-- AGDA: the detour is empty *here*, because we chose not to erase `k`.
-- One un-annotated `Nat` is both the index in the type and the number
-- the code adds up.  `shiftN` takes it directly:


------------------------------------------------------------
-- * SNat - in action
------------------------------------------------------------

-- Can use SNat to shift `Fin` indices to new scopes.

-- >>> shiftN 2 (f1 {N3})
_ : Fin (2 + 3)
_ = shiftN 2 (f1 {1})

-- The detour is *not* empty in general.  Erase a number and you need a
-- runtime witness to get it back -- see `Rebound.Classes.Sized`, where
-- the size of a pattern is `@0` and the class therefore grows exactly
-- the `size :: t -> SNat (Size t)` method that Haskell has.
--
-- The witness itself is where the languages differ.  Haskell needs a
-- purpose-built singleton *datatype* mirroring `Nat`, plus a class
-- (`SNatI`) to pass it implicitly and a `withSNat` to introduce it --
-- and a fresh copy of all three for every other index type.  Agda needs
-- one generic record (`Data.Singleton`):
--
--     record Singleton {A : Set} (@0 x : A) : Set where
--       constructor ⟨_,_⟩
--       field
--         value    : A
--         @0 proof : value ≡ x
--
-- a runtime value together with an erased proof that it is the erased
-- one.  Matching `⟨ k , Refl ⟩` names the runtime copy and rewrites the
-- index to it, so the code afterwards computes with an ordinary `Nat`.
-- Haskell has to pay the singleton price everywhere; here it is charged
-- per binding, and the currency is cheaper.

------------------------------------------------------------
-- * ASIDE: coercions
------------------------------------------------------------

-- The lookup function below has to retype its result, and the proof it
-- needs is built by induction.  So we need the three operations that
-- build and consume an equality proof.  They are short, and this is the
-- section of the talk that is about them, so here they are in full
-- rather than imported from the library.

-- Symmetry.
@0 sym : ∀ {A : Set} {@0 x y : A} → x ≡ y → y ≡ x
sym Refl = Refl

-- Congruence: equals give equals under any function.
@0 cong : ∀ {A B : Set} (f : A → B) {@0 x y : A} → x ≡ y → f x ≡ f y
cong f Refl = Refl

-- Transport: rewrite the type of a value along an equation.
subst : ∀ {A : Set} (P : @0 A → Set) {@0 x y : A} → @0 x ≡ y → P x → P y
subst P Refl px = px

-- This is what GHC's coercions do silently.  Where Haskell writes
--
--     | Refl <- axiomAssoc @k @j @p -> e
--
-- -- bring the equation into scope, and every type in the branch is
-- quietly adjusted -- Agda makes both steps explicit: name the motive
-- `P`, and say where the rewrite happens.
--
-- Note the `@0`s, which say the parts that are free:
--
--   * `sym` and `cong` are erased definitions.  They may be used in
--     types; they can never be run.
--
--   * `subst`'s proof argument is erased, so -- exactly like a GHC
--     coercion -- it is consumed by the type checker and contributes
--     nothing at runtime.  Only `P x` survives, and `subst` compiles to
--     the identity function.
--
-- So the Haskell and the Agda agree on the cost.  They disagree on
-- where the proof came from: see the associativity section below.

------------------------------------------------------------
-- * Implementation of (_!_) with embedded shifts
------------------------------------------------------------

-- AGDA: applyE / _!_ / lookupRec are mutually recursive.  The recursion
-- is well founded -- terms and environments are both finite -- but the
-- measure is a nested one that Agda's structural checker cannot
-- reconstruct: `lookupRec` calls `applyE` on a term stored *inside* the
-- environment, which is not a subterm of the term being traversed.  So
-- we assert termination.
--
-- Agda would accept a version that gives weakening its own traversal,
-- since the environment applied there (`Shift k Id`) is a pure renaming.
-- We keep the Haskell's definition: the point of this part of the talk
-- is the shape of the shift list, not the termination argument.
--
-- Note that `up` does *not* call `applyE` -- that is the whole point of
-- the shift list -- so `applyE` on its own is a plain structural
-- recursion over the term.
{-# TERMINATING #-}
applyE : ∀ {@0 m n} → Env m n → Tm m → Tm n

infixl 9 _!_
_!_ : ∀ {@0 m n} → Env m n → Fin m → Tm n

-- | As we traverse the list, accumulate amount to shift and
-- apply it all at once, fusing multiple traversals
lookupRec : ∀ {@0 m n} (k : Nat) → Env m n → Fin m → Tm (k + n)

up : ∀ {@0 m n} → Env m n → Env (S m) (S n)
up s = Var FZ ∷ shiftE s

applyE env (Var x)     = env ! x
applyE env (App t1 t2) = App (applyE env t1) (applyE env t2)
applyE env (Lam t)     = Lam (applyE (up env) t)

env ! x = lookupRec 0 env x

lookupRec k Id  i = Var (shiftN k i)
--                       ^^^^^^ shift index by k

lookupRec k (Cons t ss) FZ     = applyE (Shift k Id) t
--                               ^^^^^^^^^^^^^^^^^^^  increment all vars in t by k
lookupRec k (Cons t ss) (FS j) = lookupRec k ss j

lookupRec {n = n} k (Shift {n = p} j ss) i =
--                                  ^^  n ≡ j + p
  subst Tm (sym (lemmaAssoc k {j} {p})) (lookupRec (k + j) ss i)
--          ^^^^^^^^^^^^^^^^^^^^^^^^^   (k + j) + p ≡ k + (j + p)

------------------------------------------------------------
-- * The evaluator, as in Part I
------------------------------------------------------------

-- As in Part I, this evaluator really does diverge on (λx. x x) (λx. x x).
-- NON_TERMINATING says so, and stops Agda from unfolding it while type
-- checking; results are observed by running the program (talks/Test.agda).
{-# NON_TERMINATING #-}
eval : Tm Z → Val
eval (Var ())                    -- impossible case
eval (Lam b)   = VLam b
eval (App m n) = eval (instantiate (eval m) n)
  where
    instantiate : Val → Tm Z → Tm Z
    instantiate (VLam b) t = applyE (t ∷ idE) b


------------------------------------------------------------------
-- * Associativity: axiom (Haskell) vs. lemma (Agda)
------------------------------------------------------------------

-- The Haskell talk has to introduce a type-equality witness here:
--
--     >>> :i Refl
--     >>> :t axiomAssoc
--     axiomAssoc :: forall p m n. p + (m + n) :~: (p + m) + n
--
-- and `axiomAssoc` is implemented with `unsafeCoerce`.  A real proof
-- is also possible:
--
--     lemmaAssoc :: forall m n p. SNat p -> p + (m + n) :~: (p + m) + n
--     lemmaAssoc p = case snat_ p of
--                 SZ_ -> Refl
--                 SS_ p1 | Refl <- lemmaAssoc @m @n p1
--                        -> Refl
--
-- ... but the talk explains why you would rather not use it:
--
--   * Haskell has to *run* the proof to make sure that it is real
--   * SNat p is not available where we need the lemma, so we would
--     need to pass it around.
--
-- AGDA: neither objection applies.  `lemmaAssoc` (see Data.Nat) is the
-- only version there is.  It is an `@0` definition, so it is erased --
-- nothing is run -- yet it is a real proof, so nothing is assumed.  And
-- because erased code may recurse on erased arguments, `p` needs no
-- `SNat` witness even though it is erased.  The whole "axiom vs. lemma"
-- tension is a Haskell-specific tax.

-- Here it is again, spelled out locally:
-- The `@0` says it: this really is a proof, and it really is erased.
@0 assoc : ∀ (@0 p : Nat) {@0 m n} → p + (m + n) ≡ (p + m) + n
assoc Z     = Refl
assoc (S p) = cong S (assoc p)


------------------------------------------------------------------
-- * How many axioms do we need?
------------------------------------------------------------------

--
-- Nat-indexed scopes are degenerate lists (i.e. typing contexts)
-- Only need monoid properties:
--       Z + n ≡ n                   -- true by definition
--       n + Z ≡ n                   -- axiomPlusZ
--       p + (m + n) ≡ (p + m) + n   -- axiomAssoc
--
-- In Agda all three are ordinary `@0` theorems (Data.Nat), not axioms.


------------------------------------------------------------------
-- * Could Haskell do better?
------------------------------------------------------------------

-- Coercion evidence (i.e. equality proof) is eraseable, so must be
-- expressed in a consistent language.

-- For more expressiveness: extend GHC's coercion language to include
-- induction. Blueprint in:
--
--    Yiyun Liu and Stephanie Weirich. "Dependently-Typed Programming
--    with Logical Equality Reflection", ICFP 2023.
