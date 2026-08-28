{-# OPTIONS --erasure #-}

-- | Convert a named representation into a well-scoped one.
--
-- Agda transcription of @rebound/examples/ScopeCheck.hs@.
module ScopeCheck where

open import Rebound
open import Rebound.Bind.Single
import LC

------------------------------------------------------------------------
-- * Named syntax
------------------------------------------------------------------------

data Exp (A : Set) : Set where
  Var : A → Exp A
  Lam : A → Exp A → Exp A
  App : Exp A → Exp A → Exp A

------------------------------------------------------------------------
-- * Scope checking
------------------------------------------------------------------------

-- A plain (unscoped) association list from names to indices.
data AList (A : Set) (@0 n : Nat) : Set where
  []  : AList A n
  _∷'_ : (A × Fin n) → AList A n → AList A n

mapFS : ∀ {A} {@0 n} → AList A n → AList A (S n)
mapFS []            = []
mapFS ((v , x) ∷' vs) = (v , FS x) ∷' mapFS vs

-- Haskell uses an `Eq a` constraint; here the equality test is an
-- explicit argument, since the port has no class for it.
lookupA : ∀ {A} {@0 n} → (A → A → Bool) → A → AList A n → Maybe (Fin n)
lookupA eq v []              = Nothing
lookupA eq v ((w , x) ∷' vs) with eq v w
... | true  = Just x
... | false = lookupA eq v vs

to : ∀ {A} {@0 n} → (A → A → Bool) → AList A n → Exp A → Maybe (LC.Exp n)
to eq vs (Var v) = lookupA eq v vs >>= λ x → return (LC.Var x)
to eq vs (Lam v b) =
  to eq ((v , FZ) ∷' mapFS vs) b >>= λ b' → return (LC.Lam (bind b'))
to eq vs (App f a) =
  to eq vs f >>= λ f' →
  to eq vs a >>= λ a' →
  return (LC.App f' a')

scopeCheck : ∀ {A} → (A → A → Bool) → Exp A → Maybe (LC.Exp Z)
scopeCheck eq = to eq []

------------------------------------------------------------------------
-- * Examples
------------------------------------------------------------------------

-- Haskell uses `String`; strings have no structural equality in the
-- port's prelude, so the examples use a small enumeration of names.
data Name : Set where
  x y : Name

eqName : Name → Name → Bool
eqName x x = true
eqName y y = true
eqName _ _ = false

idExp : Exp Name
idExp = Lam x (Var x)

trueExp : Exp Name
trueExp = Lam x (Lam y (Var x))

illScoped : Exp Name
illScoped = Lam x (Var y)

-- >>> scopeCheck eqName idExp      -- Just (λ. 0)
-- >>> scopeCheck eqName illScoped  -- Nothing
