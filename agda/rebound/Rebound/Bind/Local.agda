{-# OPTIONS --erasure #-}

-- |
-- Module      : Rebound.Bind.Local
-- Description : Bind a single variable, remembering its name
--
-- "Rebound.Bind.Pat" specialized to a `LocalName` pattern: binds one
-- variable, and keeps the name the user wrote for printing.
module Rebound.Bind.Local where

open import Rebound.Lib     public
open import Rebound.Classes public
open import Rebound.Env     public
open import Data.LocalName  public
import Rebound.Bind.Pat as Pat

Bind : (v c : @0 Nat → Set) → @0 Nat → Set
Bind v c = Pat.Bind v c LocalName

bind : ∀ {v c : @0 Nat → Set} {@0 n} → LocalName → c (S n) → Bind v c n
bind = Pat.bind

getPat : ∀ {v c : @0 Nat → Set} {@0 n} → Bind v c n → LocalName
getPat = Pat.getPat

getBody : ∀ {v c : @0 Nat → Set} {@0 n}
            {{_ : SubstVar v}} {{_ : Subst v v}} {{_ : Subst v c}}
        → Bind v c n → c (S n)
getBody = Pat.getBody

unbindl : ∀ {v c : @0 Nat → Set} {@0 n}
            {{_ : SubstVar v}} {{_ : Subst v v}} {{_ : Subst v c}}
        → Bind v c n → LocalName × c (S n)
unbindl b = getPat b , getBody b

instantiate : ∀ {v c : @0 Nat → Set} {@0 n}
                {{_ : SubstVar v}} {{_ : Subst v v}} {{_ : Subst v c}}
            → Bind v c n → v n → c n
instantiate b v1 = Pat.instantiate b (v1 ∷ zeroE)

-- | As in "Rebound.Bind.PatN": name the instance, because instance
-- search cannot see the `Pat.Bind` head through the alias.
applyBind : ∀ {v c : @0 Nat → Set} {@0 n m} {{_ : SubstVar v}} {{_ : Subst v v}}
          → Env v n m → Bind v c n → Bind v c m
applyBind = Subst.applyE Pat.SubstBind

strengthenBind : ∀ {v c : @0 Nat → Set} {{_ : SubstVar v}} {{_ : Subst v v}}
                   {{_ : Subst v c}} {{_ : Strengthen c}} {@0 n} (k m : Nat)
               → Bind v c (k + (m + n)) → Maybe (Bind v c (k + n))
strengthenBind = Pat.strengthenBind
