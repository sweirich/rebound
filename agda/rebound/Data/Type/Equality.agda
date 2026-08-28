{-# OPTIONS --erasure #-}

-- |
-- Module      : Data.Type.Equality
-- Description : Propositional equality
--
-- Haskell's @Data.Type.Equality@ provides
--
-- @
-- data (:~:) a b where
--    Refl :: a :~: a
-- @
--
-- In Agda this is the ordinary propositional equality type.  The
-- constructor is named 'Refl' (rather than the usual Agda @refl@) so
-- that the ported code reads like the Haskell it came from.
--
-- ERASURE: GHC treats @Refl@ as a "0-bit value" -- a coercion is erased
-- before runtime, and so are the types it relates.  Agda can say the
-- same thing out loud: the two sides of @_≡_@ are marked @\@0@, and
-- every function that only rearranges proofs is itself an @\@0@
-- definition, so it may be used in types but never run.
module Data.Type.Equality where

infix 4 _≡_

data _≡_ {A : Set} (@0 x : A) : @0 A → Set where
  Refl : x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}

@0 sym : {A : Set} {@0 x y : A} → x ≡ y → y ≡ x
sym Refl = Refl

@0 trans : {A : Set} {@0 x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans Refl Refl = Refl

@0 cong : {A B : Set} (f : A → B) {@0 x y : A} → x ≡ y → f x ≡ f y
cong f Refl = Refl

@0 cong₂ : {A B C : Set} (f : A → B → C) {@0 x y : A} {@0 u v : B}
         → x ≡ y → u ≡ v → f x u ≡ f y v
cong₂ f Refl Refl = Refl

-- | Transport along an equality.  This is what GHC's coercions do
-- silently once a @Refl@ has been brought into scope by a pattern match.
--
-- Note that the proof argument is @\@0@: like a GHC coercion, it is
-- consumed by the type checker and contributes nothing at runtime.  The
-- motive @P@ takes an erased index, which is the shape every scoped
-- type in this library has.
subst : {A : Set} (P : @0 A → Set) {@0 x y : A} → @0 x ≡ y → P x → P y
subst P Refl px = px
