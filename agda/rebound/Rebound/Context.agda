{-# OPTIONS --erasure #-}

-- |
-- Module      : Rebound.Context
-- Description : Typing contexts
module Rebound.Context where

open import Rebound.Lib
open import Rebound.Env

-- | A typing context maps indices to types in the same scope.
Ctx : (@0 Nat → Set) → @0 Nat → Set
Ctx v n = Env v n n

-- | An empty context, that includes no variable assumptions.
emptyC : ∀ {v} {{_ : SubstVar v}} → Ctx v N0
emptyC = zeroE

-- | "Snoc" a new definition onto the end of the context.  All existing
-- types in the context need to be shifted (lazily).
infixl 5 _+++_
_+++_ : ∀ {v} {@0 n} {{_ : SubstVar v}} {{_ : Subst v v}}
      → Ctx v n → v n → Ctx v (S n)
g +++ a = applyE shift1E a ∷ (g >>> shift1E)
