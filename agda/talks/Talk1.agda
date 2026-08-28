{-# OPTIONS --erasure #-}
{-


             What have we learned about
            Dependently Typed Programming
                 from Haskell?

                Stephanie Weirich
                sweirich@upenn.edu

              University of Pennsylvania

                 Haskell Symposium
                   August 2026

  ---------------------------------------------------------------------
  This is the Agda transcription of Talks.Hs26.Talk1.  The Haskell is
  reproduced as closely as Agda allows; every place the two languages
  part company is flagged with an "AGDA:" note.

  Scope indices carry an "@0" annotation, Agda's marker for data that is
  erased before execution.  It is the same status those numbers have in
  Haskell, where they live at the type level -- the difference is that
  in Agda it is a choice made per binding rather than by the language.
  ---------------------------------------------------------------------
-}


------------------------------------------------------------------------
--  Talk Plan
------------------------------------------------------------------------

{-

    Examples of dependently-typed programming (DTP) in Haskell, inspired
    by rebound library

    Part I: A DTP Pearl: Well-scoped de Bruijn indices
    Part II: A DTP "Pearl": Substitutions via shift lists
    Part III: Reflecting on DTP in Haskell, using rebound

 -}


------------------------------------------------------------------------
--  Rebound library: Well-scoped de Bruijn indices in Haskell
------------------------------------------------------------------------

{-

    Noé De Santo, Stephanie Weirich, "Rebound: Efficient,
    Expressive, and Well-Scoped Binding"
    Haskell Symposium 2025

    - Efficient: supports working with delayed and reified substitutions
    - Expressive: reimplemented pi-forall
    - Well-Scoped: type system maintains domain-specific invariant

    https://github.com/sweirich/rebound

    NOTE: the github repository includes the rebound library,
          examples, tutorial, exercises, pi-forall demo, and this talk.

 -}



------------------------------------------------------------------------
-- * Part I: A Dependently-Typed Pearl
------------------------------------------------------------------------

module Talk1 where

-- Haskell needs no imports in this part; Agda has no Prelude, so we
-- borrow Bool for the equality functions at the bottom and nothing else.
open import Data.Prelude using (Bool; true; false; _∘_)


------------------------------------------------------------------------
-- * Internal verification - GADT based
------------------------------------------------------------------------

-- | Peano natural numbers
data Nat : Set where
  Z : Nat
  S : Nat → Nat

-- | `Fin n` is the type of de Bruijn indices in scope n:
-- the finite set `{0, 1, ..., n-1}`.
data Fin : @0 Nat → Set where
  FZ : ∀ {@0 n} → Fin (S n)
  FS : ∀ {@0 n} → Fin n → Fin (S n)

f1 : ∀ {@0 n} → Fin (S (S n))   -- Any scope >= 2
f1 = FS FZ


-- Requisite Vec example: Fin delimits the domain of the function
Vec : @0 Nat → Set → Set
Vec n a = Fin n → a

vnil : ∀ {a} → Vec Z a
vnil ()
-- AGDA: Haskell writes `\x -> case x of {}`; Agda writes an absurd
-- pattern.  Both say "there is nothing to return because there is
-- nothing to match on".

infixr 5 _∷_
_∷_ : ∀ {@0 n} {a} → a → Vec n a → Vec (S n) a
(x ∷ xs) FZ     = x
(x ∷ xs) (FS f) = xs f

infixl 9 _!_
_!_ : ∀ {@0 n} {a} → Vec n a → Fin n → a
v ! x = v x

-- Out-of-domain access is compile-time failure
-- >>> ("a" ∷ vnil) ! f1
--
-- Uncomment to see the error:
-- bad : Nat
-- bad = (Z ∷ vnil) ! f1

------------------------------------------------------------------------
-- * Internal vs. External verification
------------------------------------------------------------------------

{-

Internal verification is more common in Agda
External verification is more common in Lean/Rocq

External verification is more general.
But, when internal verification works, it is beautiful.

We should treasure and display these pearls
     ... but not be surprised by their rarity.

-}


------------------------------------------------------------------------
-- * Well-scoped lambda calculus terms
------------------------------------------------------------------------

data Tm : @0 Nat → Set where
  Var : ∀ {@0 n} → Fin n → Tm n
  Lam : ∀ {@0 n} → Tm (S n) → Tm n
  App : ∀ {@0 n} → Tm n → Tm n → Tm n


-- | Identity function: λx. x  or  λ.0
ex-id : Tm Z
ex-id = Lam (Var FZ)

-- | Constant function: λx. λy. x or λ.λ.1
ex-const : Tm Z
ex-const = Lam (Lam (Var (FS FZ)))


------------------------------------------------------------------------
-- * Substitution
------------------------------------------------------------------------

-- | A substitution environment maps `m` variables to terms in scope `n`.
Env : @0 Nat → @0 Nat → Set
Env m n = Vec m (Tm n)

-- Identity environment, another terminator for a Vec
idE : ∀ {@0 n} → Env n n
idE = Var

-- | Apply a substitution environment to a term, replacing every free
-- variable
--
-- AGDA: this trio terminates, but not for a reason the termination
-- checker can find.  `applyE` recurses on the term, which is fine; but
-- `shiftE` calls `applyE` on `env x`, a term pulled out of the
-- environment and so unrelated to the term we started with.  Agda sees a
-- cycle with nothing decreasing, so we assert termination.
--
-- Agda would accept a version that defines *renaming* separately and
-- builds `shiftE` from that, since `Var . FS` maps variables to
-- variables.  We keep the definitions the Haskell has instead: the whole
-- point of Part I is what this code looks like, and "non-termination by
-- default" is on the talk's list of things Haskell gets right.
{-# TERMINATING #-}
applyE : ∀ {@0 m n} → Env m n → Tm m → Tm n

-- | Lift under one binder
-- New variable maps to itself; all others are shifted
-- to the extended scope.
up : ∀ {@0 m n} → Env m n → Env (S m) (S n)

-- | Shift an environment to a new scope
shiftE : ∀ {@0 n m} → Env n m → Env n (S m)

applyE env (Var x)   = env x
applyE env (Lam b)   = Lam (applyE (up env) b)
applyE env (App f a) = App (applyE env f) (applyE env a)

up env = Var FZ ∷ shiftE env

shiftE env = applyE (Var ∘ FS) ∘ env

------------------------------------------------------------------------
-- * Evaluator: Internal verification for well-scoped terms
------------------------------------------------------------------------

-- Only one kind of value in pure lambda calculus
data Val : Set where
  VLam : Tm (S Z) → Val

-- | Open a single-variable binder by substituting `t` for the bound
-- variable.
instantiate : Val → Tm Z → Tm Z
instantiate (VLam body) t = applyE (t ∷ idE) body

-- | (big-step) cbn evaluation function
-- Haskell's type system ensures no *runtime* errors
--
-- AGDA: ... but it does not ensure termination, and this evaluator
-- really does diverge on (λx. x x) (λx. x x).  In Haskell that is a
-- feature; in Agda it has to be an explicit escape hatch.  This is the
-- single biggest difference the talk is about.
--
-- NON_TERMINATING, rather than TERMINATING, is the honest marker: it
-- says the function may diverge, and Agda will therefore refuse to
-- unfold it while type checking.  Type checking stays decidable, and the
-- price is that results can only be observed by running the program --
-- see talks/Test.agda.
{-# NON_TERMINATING #-}
eval : Tm Z → Val
eval (Var ())                    -- impossible case
eval (Lam b)   = VLam b
eval (App m n) = eval (instantiate (eval m) n)

-- >>> eval (App ex-id ex-id)
_ : Val
_ = eval (App ex-id ex-id)


-- End of Part I ---


------------------------------------------------------------------------
-- * Extra definitions
------------------------------------------------------------------------

-- Haskell derives (or hand-writes) Eq/Show/Num instances here.  Agda
-- has no deriving, so we spell out the two we actually use.

eqNat : Nat → Nat → Bool
eqNat Z     Z     = true
eqNat (S m) (S n) = eqNat m n
eqNat _     _     = false

eqFin : ∀ {@0 n} → Fin n → Fin n → Bool
eqFin FZ     FZ     = true
eqFin (FS i) (FS j) = eqFin i j
eqFin _      _      = false

toNat : ∀ {@0 n} → Fin n → Nat
toNat FZ     = Z
toNat (FS n) = S (toNat n)
