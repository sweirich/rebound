{-# OPTIONS --erasure #-}

-- |
-- Module      : Rebound.Bind.PatN
-- Description : Bind a fixed number of variables
--
-- A binder for exactly one variable, built on 'Rebound.Bind.Pat.Bind'
-- with a singleton as its (trivial) pattern.
module Rebound.Bind.PatN where

open import Rebound.Lib
open import Rebound.Classes
open import Rebound.Env
open import Data.Vec using (Vec)
import Rebound.Bind.Pat as Pat

-- Eta-reduced on purpose: written as @Bind1 v c n = ... n@, the partial
-- application @Bind1 Exp Exp@ would be a lambda and instance search
-- could not see the @Pat.Bind@ head.
-- | Haskell's @PatN p@ is a newtype around @SNat p@: a pattern carrying
-- nothing but the number of variables it binds.  Here 'Singleton' is
-- already exactly that, so @PatN@ is an alias rather than a new type.
PatN : @0 Nat → Set
PatN p = Singleton p

------------------------------------------------------------------------
-- * N-ary binder
------------------------------------------------------------------------

BindN : (v c : @0 Nat → Set) (@0 m : Nat) → @0 Nat → Set
BindN v c m = Pat.Bind v c (Singleton m)

bindN : ∀ {v c : @0 Nat → Set} {@0 m n} → Singleton m → c (m + n) → BindN v c m n
bindN = Pat.bind

bindWithN : ∀ {v c : @0 Nat → Set} {@0 p m n}
          → Singleton p → Env v m n → c (p + m) → BindN v c p n
bindWithN = Pat.bindWith

getBodyN : ∀ {v c : @0 Nat → Set} {@0 m n}
             {{_ : SubstVar v}} {{_ : Subst v v}} {{_ : Subst v c}}
         → BindN v c m n → c (m + n)
getBodyN = Pat.getBody

unbindlN : ∀ {v c : @0 Nat → Set} {@0 m n}
             {{_ : SubstVar v}} {{_ : Subst v v}} {{_ : Subst v c}}
         → BindN v c m n → c (m + n)
unbindlN = Pat.getBody

instantiateN : ∀ {v c : @0 Nat → Set} {@0 m n}
                 {{_ : SubstVar v}} {{_ : Subst v v}} {{_ : Subst v c}}
             → BindN v c m n → Vec (v n) m → c n
instantiateN b vs = Pat.instantiate b (fromVec vs)

------------------------------------------------------------------------
-- * Single binder
------------------------------------------------------------------------

-- Eta-reduced on purpose: written as @Bind1 v c n = ... n@, the partial
-- application @Bind1 Exp Exp@ would be a lambda and instance search
-- could not see the @Pat.Bind@ head.
Bind1 : (v c : @0 Nat → Set) → @0 Nat → Set
Bind1 v c = Pat.Bind v c (Singleton N1)

bind1 : ∀ {v c : @0 Nat → Set} {@0 n} → c (S n) → Bind1 v c n
bind1 = Pat.bind s1

getBody1 : ∀ {v c : @0 Nat → Set} {@0 n}
             {{_ : SubstVar v}} {{_ : Subst v v}} {{_ : Subst v c}}
         → Bind1 v c n → c (S n)
getBody1 = Pat.getBody

instantiate1 : ∀ {v c : @0 Nat → Set} {@0 n}
                 {{_ : SubstVar v}} {{_ : Subst v v}} {{_ : Subst v c}}
             → Bind1 v c n → v n → c n
instantiate1 b v1 = Pat.instantiate b (v1 ∷ zeroE)

-- | Substitute into a binder.
--
-- @Bind1 v c@ is a *definition*, so when Agda infers the `c` of `applyE`
-- from a constructor's type it gets the eta-expansion
-- @λ n → Bind1 v c n@, whose head instance search cannot see.  Naming
-- the instance here saves every client from working around it.
applyBind1 : ∀ {v c : @0 Nat → Set} {@0 n m} {{_ : SubstVar v}} {{_ : Subst v v}}
           → Env v n m → Bind1 v c n → Bind1 v c m
applyBind1 = Subst.applyE Pat.SubstBind

applyBindN : ∀ {v c : @0 Nat → Set} {@0 k n m} {{_ : SubstVar v}} {{_ : Subst v v}}
           → Env v n m → BindN v c k n → BindN v c k m
applyBindN = Subst.applyE Pat.SubstBind

-- Strengthening needs the same treatment, for the same reason.
strengthenBind1 : ∀ {v c : @0 Nat → Set} {{_ : SubstVar v}} {{_ : Subst v v}}
                    {{_ : Subst v c}} {{_ : Strengthen c}} {@0 n} (k m : Nat)
                → Bind1 v c (k + (m + n)) → Maybe (Bind1 v c (k + n))
strengthenBind1 = Pat.strengthenBind

strengthenBindN : ∀ {v c : @0 Nat → Set} {{_ : SubstVar v}} {{_ : Subst v v}}
                    {{_ : Subst v c}} {{_ : Strengthen c}} {@0 p n} (k m : Nat)
                → BindN v c p (k + (m + n)) → Maybe (BindN v c p (k + n))
strengthenBindN = Pat.strengthenBind

bindWith1 : ∀ {v c : @0 Nat → Set} {@0 m n} → Env v m n → c (S m) → Bind1 v c n
bindWith1 = Pat.bindWith s1

unbindWith1 : ∀ {v c : @0 Nat → Set} {d : Set} {@0 n}
            → Bind1 v c n → (∀ {@0 m} → Env v m n → c (S m) → d) → d
unbindWith1 b f = Pat.unbindWith b (λ _ → f)

instantiateWith1 : ∀ {v c d : @0 Nat → Set} {@0 n} {{_ : SubstVar v}}
                 → Bind1 v c n → v n → (∀ {@0 m} → Env v m n → c m → d n) → d n
instantiateWith1 b v1 f = unbindWith1 b (λ r e → f (v1 ∷ r) e)

------------------------------------------------------------------------
-- * Double binder
------------------------------------------------------------------------

Bind2 : (v c : @0 Nat → Set) → @0 Nat → Set
Bind2 v c = Pat.Bind v c (Singleton N2)

bind2 : ∀ {v c : @0 Nat → Set} {@0 n} → c (S (S n)) → Bind2 v c n
bind2 = Pat.bind s2

getBody2 : ∀ {v c : @0 Nat → Set} {@0 n}
             {{_ : SubstVar v}} {{_ : Subst v v}} {{_ : Subst v c}}
         → Bind2 v c n → c (S (S n))
getBody2 = Pat.getBody

unbindWith2 : ∀ {v c : @0 Nat → Set} {d : Set} {@0 n}
            → Bind2 v c n → (∀ {@0 m} → Env v m n → c (S (S m)) → d) → d
unbindWith2 b f = Pat.unbindWith b (λ _ → f)

instantiate2 : ∀ {v c : @0 Nat → Set} {@0 n}
                 {{_ : SubstVar v}} {{_ : Subst v v}} {{_ : Subst v c}}
             → Bind2 v c n → v n → v n → c n
instantiate2 b v1 v2 = Pat.instantiate b (v1 ∷ v2 ∷ zeroE)
