{-# OPTIONS --erasure #-}

-- |
-- Module       : Rebound.Bind.Single
-- Description  : Bind a single variable
--
-- The unsuffixed names of "Rebound.Bind.PatN", specialized to a binder
-- for exactly one variable.  This is the interface most of the examples
-- use.
module Rebound.Bind.Single where

open import Rebound.Lib     public
open import Rebound.Classes public
open import Rebound.Env     public

open import Rebound.Bind.PatN public
  renaming ( Bind1            to Bind
           ; bindWith1        to bindWith
           ; unbindWith1      to unbindWith
           ; instantiateWith1 to instantiateWith
           ; bind1            to bind
           ; getBody1         to getBody
           ; instantiate1     to instantiate
           ; applyBind1       to applyBind
           )

-- For this kind of binding, `unbindl` is `getBody`.
unbindl : ∀ {v c : @0 Nat → Set} {@0 n}
            {{_ : SubstVar v}} {{_ : Subst v v}} {{_ : Subst v c}}
        → Bind v c n → c (S n)
unbindl = getBody
