{-# OPTIONS --erasure #-}

-- |
-- Module       : Rebound.Bind.Pat
-- Description  : Bind variables according to a pattern
--
-- Bind variables according to a user-defined pattern.
--
-- ERASURE: @Size pat@ is erased, so it may appear in the types below but
-- never in the code.  Every operation that has to /act/ on the size
-- recovers it from the pattern with @size@, which is precisely what the
-- Haskell does.
module Rebound.Bind.Pat where

open import Rebound.Lib
open import Rebound.Classes public
open import Rebound.Env     public

------------------------------------------------------------------------
-- * Bind type
------------------------------------------------------------------------

-- | Binds @Size pat@ variables.  The data structure includes a delayed
-- substitution for the variables in the body of the binder.
data Bind (v c : @0 Nat → Set) (pat : Set) {{_ : Sized pat}}
          (@0 n : Nat) : Set where
  mkBind : ∀ {@0 m} → pat → Env v m n → c (Size pat + m) → Bind v c pat n

-- | Bind a pattern, using the identity substitution.
bind : ∀ {v c : @0 Nat → Set} {pat : Set} {@0 n} {{_ : Sized pat}}
     → pat → c (Size pat + n) → Bind v c pat n
bind p t = mkBind p idE t

-- | Bind a pattern, while suspending the provided substitution.
bindWith : ∀ {v c : @0 Nat → Set} {pat : Set} {@0 m n} {{_ : Sized pat}}
         → pat → Env v m n → c (Size pat + m) → Bind v c pat n
bindWith = mkBind

-- | Retrieve the pattern of the binding.
getPat : ∀ {v c : @0 Nat → Set} {pat : Set} {@0 n} {{_ : Sized pat}}
       → Bind v c pat n → pat
getPat (mkBind p e t) = p

-- | Retrieve the body of the binding, applying the delayed substitution.
--
-- Note @size p@: the number of bound variables is erased from the type,
-- so it has to be recomputed from the pattern before 'upN' can use it.
getBody : ∀ {v c : @0 Nat → Set} {pat : Set} {@0 n} {{_ : Sized pat}}
            {{_ : SubstVar v}} {{_ : Subst v v}} {{_ : Subst v c}}
        → Bind v c pat n → c (Size pat + n)
getBody (mkBind p e t) = applyOpt (upN (size p) e) t

-- | Retrieve the body, as well as the bound pattern.
unbindl : ∀ {v c : @0 Nat → Set} {pat : Set} {@0 n} {{_ : Sized pat}}
             {{_ : SubstVar v}} {{_ : Subst v v}} {{_ : Subst v c}}
        → Bind v c pat n → pat × c (Size pat + n)
unbindl bnd = getPat bnd , getBody bnd

-- | Run a function on the body.  The delayed substitution is __not__
-- applied, but is passed to the function instead.
unbindWith : ∀ {v c : @0 Nat → Set} {pat d : Set} {@0 n} {{_ : Sized pat}}
           → Bind v c pat n
           → (∀ {@0 m} → pat → Env v m n → c (Size pat + m) → d)
           → d
unbindWith (mkBind p r t) f = f p r t

-- | Instantiate the body (i.e. replace the bound variables) with the
-- provided terms.
instantiate : ∀ {v c : @0 Nat → Set} {pat : Set} {@0 n} {{_ : Sized pat}}
                 {{_ : SubstVar v}} {{_ : Subst v v}} {{_ : Subst v c}}
            → Bind v c pat n → Env v (Size pat) n → c n
instantiate (mkBind p r t) e = applyOpt (appendE (size p) e r) t

-- | Instantiate the body, keeping the delayed substitution delayed.
instantiateWith : ∀ {v c : @0 Nat → Set} {pat : Set} {@0 n} {{_ : Sized pat}}
                     {{_ : SubstVar v}} {{_ : Subst v v}}
                → Bind v c pat n
                → Env v (Size pat) n
                → (∀ {@0 m} → Env v m n → c m → c n)
                → c n
instantiateWith b e f =
  unbindWith b (λ p r t → f (appendE (size p) e r) t)

------------------------------------------------------------------------
-- * Instances for Bind
------------------------------------------------------------------------

-- | The substitution operation composes the explicit substitution with
-- the one stored at the binder.  Note that nothing is traversed.
instance
  SubstBind : ∀ {v c : @0 Nat → Set} {pat : Set} {{_ : Sized pat}}
                {{_ : SubstVar v}} {{_ : Subst v v}}
            → Subst v (Bind v c pat)
  Subst.applyE SubstBind env1 (mkBind p env2 m) = mkBind p (env2 >>> env1) m

------------------------------------------------------------------------
-- * Strengthening under a binder
------------------------------------------------------------------------

-- The pattern's size has to be added to `k` before recursing under the
-- binder, so it must be recovered at runtime with `size`.  Because
-- `Size pat` is an opaque projection rather than a variable, the two
-- rescopings are done with explicit (erased) equations rather than by
-- matching the singleton.
strengthenBind :
  ∀ {v c : @0 Nat → Set} {pat : Set} {{_ : Sized pat}}
    {{_ : SubstVar v}} {{_ : Subst v v}} {{_ : Subst v c}} {{_ : Strengthen c}}
  → ∀ {@0 n} (k m : Nat)
  → Bind v c pat (k + (m + n)) → Maybe (Bind v c pat (k + n))
strengthenBind {v} {c} {pat} {n = n} k m bnd =
  helper (value (size (getPat bnd))) (proof (size (getPat bnd)))
  where
    helper : (sp : Nat) → @0 (sp ≡ Size pat) → Maybe (Bind v c pat (k + n))
    helper sp eq =
      (λ r → bind (getPat bnd) (subst c eq2 r))
        <$> strengthenRec (sp + k) m (subst c eq1 (getBody bnd))
      where
        @0 eq' : Size pat ≡ sp
        eq' = sym eq

        @0 eq1 : Size pat + (k + (m + n)) ≡ (sp + k) + (m + n)
        eq1 = trans (axiomAssoc {Size pat} {k} {m + n})
                    (cong (λ q → q + (m + n)) (cong (λ q → q + k) eq'))

        @0 eq2 : (sp + k) + n ≡ Size pat + (k + n)
        eq2 = trans (cong (λ q → q + n) (cong (λ q → q + k) eq))
                    (sym (axiomAssoc {Size pat} {k} {n}))

instance
  StrengthenBind :
    ∀ {v c : @0 Nat → Set} {pat : Set} {{_ : Sized pat}}
      {{_ : SubstVar v}} {{_ : Subst v v}} {{_ : Subst v c}} {{_ : Strengthen c}}
    → Strengthen (Bind v c pat)
  Strengthen.strengthenRec StrengthenBind = strengthenBind

------------------------------------------------------------------------
-- * Free variables under a binder
------------------------------------------------------------------------

appearsFreeBind :
  ∀ {v c : @0 Nat → Set} {pat : Set} {{_ : Sized pat}}
    {{_ : SubstVar v}} {{_ : Subst v v}} {{_ : Subst v c}} {{_ : FV c}}
  → ∀ {@0 n} → Fin n → Bind v c pat n → Bool
appearsFreeBind {pat = pat} {n = n} x b =
  helper (value (size (getPat b))) (proof (size (getPat b)))
  where
    helper : (sp : Nat) → @0 (sp ≡ Size pat) → Bool
    helper sp eq =
      appearsFree (subst Fin (cong (λ q → q + n) eq) (shiftN sp x)) (getBody b)

instance
  FVBind :
    ∀ {v c : @0 Nat → Set} {pat : Set} {{_ : Sized pat}}
      {{_ : SubstVar v}} {{_ : Subst v v}} {{_ : Subst v c}} {{_ : FV c}}
    → FV (Bind v c pat)
  FV.appearsFree FVBind = appearsFreeBind
