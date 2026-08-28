{-# OPTIONS --erasure #-}

-- |
-- Module      : Data.Prelude
-- Description : The bits of Haskell's Prelude that we need
--
-- Agda has no Prelude and we deliberately do not depend on the Agda
-- standard library, so this module defines the handful of Haskell types
-- (Bool, Maybe, pairs, ...) used by the rest of the port.
module Data.Prelude where

------------------------------------------------------------------------
-- * Bool
------------------------------------------------------------------------

open import Agda.Builtin.Bool public using (Bool; true; false)

infixr 3 _&&_
_&&_ : Bool → Bool → Bool
true  && b = b
false && _ = false

infixr 2 _||_
_||_ : Bool → Bool → Bool
true  || _ = true
false || b = b

not : Bool → Bool
not true  = false
not false = true

------------------------------------------------------------------------
-- * Maybe
------------------------------------------------------------------------

data Maybe (A : Set) : Set where
  Nothing : Maybe A
  Just    : A → Maybe A

-- Agda's @do@ notation desugars to whatever @_>>=_@ / @_>>_@ are in
-- scope, so these definitions give us Haskell's @Maybe@ monad.

infixl 1 _>>=_ _>>_
_>>=_ : {A B : Set} → Maybe A → (A → Maybe B) → Maybe B
Nothing >>= _ = Nothing
Just x  >>= f = f x

_>>_ : {A B : Set} → Maybe A → Maybe B → Maybe B
m >> k = m >>= λ _ → k

return : {A : Set} → A → Maybe A
return = Just

infixl 4 _<$>_
_<$>_ : {A B : Set} → (A → B) → Maybe A → Maybe B
f <$> m = m >>= λ x → Just (f x)

------------------------------------------------------------------------
-- * The erasure modality as a type
------------------------------------------------------------------------

-- Whether a computation succeeded is runtime information; /why/ it
-- succeeded need not be.  Haskell's @Maybe (a :~: b)@ already works this
-- way -- GHC treats @Refl@ as a "0-bit" value -- and 'Erased' says so in
-- the type, without needing a second copy of @Maybe@: an @Erased@ proof
-- travels inside the ordinary one.
record Erased (@0 A : Set) : Set where
  constructor [_]
  field @0 erased : A
open Erased public

-- | Map under the modality.  The function is itself erased, so erased
-- definitions (such as 'Data.Type.Equality.cong') may be used here.
emap : {@0 A B : Set} → (@0 f : A → B) → Erased A → Erased B
emap f [ x ] = [ f x ]

------------------------------------------------------------------------
-- * Either
------------------------------------------------------------------------

data Either (E A : Set) : Set where
  Left  : E → Either E A
  Right : A → Either E A

------------------------------------------------------------------------
-- * Empty, unit and pairs
------------------------------------------------------------------------

data ⊥ : Set where

-- | Haskell writes this as an empty @case@: @case x of {}@
exfalso : {A : Set} → @0 ⊥ → A
exfalso ()

record ⊤ : Set where
  instance constructor tt

infixr 4 _,_
record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B fst
open Σ public

infixr 2 _×_
_×_ : Set → Set → Set
A × B = Σ A (λ _ → B)

------------------------------------------------------------------------
-- * Functions
------------------------------------------------------------------------

infixr 9 _∘_
_∘_ : {A B C : Set} → (B → C) → (A → B) → A → C
(f ∘ g) x = f (g x)

id : {A : Set} → A → A
id x = x

const : {A B : Set} → A → B → A
const x _ = x

------------------------------------------------------------------------
-- * Strings (only used for examples)
------------------------------------------------------------------------

-- Agda ships these, so there is no need to postulate our own; unlike a
-- hand-rolled postulate they are accepted by @--safe@.

open import Agda.Builtin.String public using (String)

-- Structural equality on strings, from Agda's builtins.
open import Agda.Builtin.String public using () renaming (primStringEquality to eqString; primStringAppend to _<>ˢ_)
