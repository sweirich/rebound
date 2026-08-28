{-# OPTIONS --erasure #-}

-- |
-- Module      : Data.Scoped.List
-- Description : Scoped lists
--
-- Lists where every element has type @a n@.  Note: the @n@ is /not/ the
-- length of the list, it is a common scope for all its elements.
module Data.Scoped.List where

open import Rebound.Lib
open import Rebound.Env

infixr 5 _:<_
data List (a : @0 Nat → Set) (@0 n : Nat) : Set where
  Nil  : List a n
  _:<_ : a n → List a n → List a n

map : ∀ {a b : @0 Nat → Set} {@0 n} → (a n → b n) → List a n → List b n
map f Nil       = Nil
map f (x :< xs) = f x :< map f xs

applyList : ∀ {v t : @0 Nat → Set} {{_ : Subst v t}} {@0 n m}
          → Env v n m → List t n → List t m
applyList r Nil       = Nil
applyList r (x :< xs) = applyE r x :< applyList r xs

instance
  SubstList : ∀ {v t : @0 Nat → Set} {{_ : Subst v t}} → Subst v (List t)
  Subst.applyE SubstList = applyList
