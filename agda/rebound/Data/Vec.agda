{-# OPTIONS --erasure #-}

-- |
-- Module      : Data.Vec
-- Description : Length-indexed lists
--
-- Note the argument order: Haskell writes @Vec n a@ (size first, so
-- that @Vec n@ is a functor); Agda prefers the element type to be a
-- parameter, so we write @Vec a n@.
module Data.Vec where

open import Data.Nat
open import Data.Fin
open import Data.Singleton
open import Data.Prelude using (_∘_; Bool; true; _&&_)

infixr 5 _:::_

data Vec (A : Set) : @0 Nat → Set where
  VNil  : Vec A Z
  _:::_ : ∀ {@0 n} → A → Vec A n → Vec A (S n)

-- | The length of a vector.  The index is erased, so the length has to
-- be recomputed and returned as a runtime copy of it -- the same
-- situation Haskell is in, where @Data.Vec.vlength@ returns an @SNat@.
vlength : ∀ {A} {@0 n} → Vec A n → Singleton n
vlength VNil       = s0
vlength (x ::: xs) = ssuc (vlength xs)

vlookup : ∀ {A} {@0 n} → Vec A n → Fin n → A
vlookup (x ::: xs) FZ     = x
vlookup (x ::: xs) (FS i) = vlookup xs i

tabulate : ∀ {A} (n : Nat) → (Fin n → A) → Vec A n
tabulate Z     f = VNil
tabulate (S n) f = f FZ ::: tabulate n (f ∘ FS)

map : ∀ {A B} {@0 n} → (A → B) → Vec A n → Vec B n
map f VNil       = VNil
map f (x ::: xs) = f x ::: map f xs

all2 : ∀ {A B} {@0 n} → (A → B → Bool) → Vec A n → Vec B n → Bool
all2 p VNil       VNil       = true
all2 p (x ::: xs) (y ::: ys) = p x y && all2 p xs ys

vtail : ∀ {A} {@0 n} → Vec A (S n) → Vec A n
vtail (x ::: xs) = xs

foldr : ∀ {A B : Set} {@0 n} → (A → B → B) → B → Vec A n → B
foldr f z VNil       = z
foldr f z (x ::: xs) = f x (foldr f z xs)
