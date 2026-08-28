{-# OPTIONS --erasure #-}

-- | The untyped lambda calculus, with several evaluation strategies.
--
-- Agda transcription of @rebound/examples/LC.hs@.
module LC where

open import Rebound
open import Rebound.Bind.Single

------------------------------------------------------------------------
-- * Syntax
------------------------------------------------------------------------

data Exp : @0 Nat → Set where
  Var : ∀ {@0 n} → Fin n → Exp n
  Lam : ∀ {@0 n} → Bind Exp Exp n → Exp n
  App : ∀ {@0 n} → Exp n → Exp n → Exp n

instance
  SubstVarExp : SubstVar Exp
  SubstVar.var SubstVarExp = Var

-- Haskell derives this from `isVar` via GHC.Generics; Agda has no such
-- mechanism, so the traversal is written out.
{-# TERMINATING #-}
applyExp : ∀ {@0 n m} → Env Exp n m → Exp n → Exp m

instance
  SubstExpExp : Subst Exp Exp
  Subst.applyE SubstExpExp = applyExp

applyExp r (Var x)     = applyEnv r x
applyExp r (Lam b)     = Lam (applyBind r b)
applyExp r (App e1 e2) = App (applyExp r e1) (applyExp r e2)

------------------------------------------------------------------------
-- * Smart constructors and examples
------------------------------------------------------------------------

lam : ∀ {@0 n} → Exp (S n) → Exp n
lam b = Lam (bind b)

-- Haskell writes this `@@`; `@` may not appear in an Agda identifier.
infixl 9 _$$_
_$$_ : ∀ {@0 n} → Exp n → Exp n → Exp n
_$$_ = App

v0 : ∀ {@0 n} → Exp (S n)
v0 = Var f0

v1 : ∀ {@0 n} → Exp (S (S n))
v1 = Var f1

t0 : Exp Z
t0 = lam v0

t : Exp Z
t = lam ((v0 $$ (lam v0 $$ v0)) $$ lam v0)

t2 : Exp Z
t2 = App (Lam (bind (Lam (bind (Var f1)))))
         (App (Lam (bind (Var f0))) (Lam (bind (Var f0))))

-- Alpha-equivalence.  Haskell derives it.
{-# TERMINATING #-}
eqExp : ∀ {@0 n} → Exp n → Exp n → Bool
eqExp (Var x)     (Var y)     = eqFin x y
eqExp (Lam b1)    (Lam b2)    = eqExp (getBody b1) (getBody b2)
eqExp (App a1 b1) (App a2 b2) = eqExp a1 a2 && eqExp b1 b2
eqExp _           _           = false

------------------------------------------------------------------------
-- * Evaluation
------------------------------------------------------------------------

{-# NON_TERMINATING #-}
eval : Exp Z → Exp Z
eval (Var ())
eval (Lam b) = Lam b
eval (App e1 e2) = apply (eval e1) (eval e2)
  where
    apply : Exp Z → Exp Z → Exp Z
    apply (Lam b) v = eval (instantiate b v)
    apply t       v = App t v

{-# TERMINATING #-}
step : ∀ {@0 n} → Exp n → Maybe (Exp n)
step (Var x) = Nothing
step (Lam b) = Nothing
step (App (Lam b) e2) = Just (instantiate b e2)
step (App e1 e2) with step e1
... | Just e1' = Just (App e1' e2)
... | Nothing with step e2
...   | Just e2' = Just (App e1 e2')
...   | Nothing  = Nothing

eval' : ∀ {@0 n} → Nat → Exp n → Maybe (Exp n)
eval' Z     e = Nothing
eval' (S k) e with step e
... | Just e' = eval' k e'
... | Nothing = Just e

------------------------------------------------------------------------
-- * Normalization
------------------------------------------------------------------------

{-# NON_TERMINATING #-}
nf : ∀ {@0 n} → Exp n → Exp n
nf (Var x) = Var x
nf (Lam b) = Lam (bind (nf (getBody b)))
nf (App e1 e2) = apply (nf e1) e2
  where
    apply : ∀ {@0 n} → Exp n → Exp n → Exp n
    apply (Lam b) e2 = nf (instantiate b e2)
    apply t       e2 = App t (nf e2)

{-# NON_TERMINATING #-}
whnf : ∀ {@0 n} → Exp n → Exp n
whnf (Var x) = Var x
whnf (Lam b) = Lam b
whnf (App e1 e2) = apply (nf e1) e2
  where
    apply : ∀ {@0 n} → Exp n → Exp n → Exp n
    apply (Lam b) e2 = nf (instantiate b (whnf e2))
    apply t       e2 = App t (nf e2)

{-# NON_TERMINATING #-}
nf1 : ∀ {@0 n} → Exp n → Exp n
nf1 (Var x) = Var x
nf1 (Lam b) = Lam (bind (nf1 (getBody b)))
nf1 (App e1 e2) = apply (whnf e1) e2
  where
    apply : ∀ {@0 n} → Exp n → Exp n → Exp n
    apply (Lam b) e2 = nf1 (instantiate b (whnf e2))
    apply t       e2 = App t (nf e2)

------------------------------------------------------------------------
-- * Normalization with an explicit environment
------------------------------------------------------------------------

-- This is the version that benefits from rebound's delayed
-- substitutions: `instantiateWith` hands the suspended environment to
-- the continuation rather than applying it.
{-# NON_TERMINATING #-}
whnfEnv : ∀ {@0 m n} → Env Exp m n → Exp m → Exp n
whnfEnv r (Var x) = applyEnv r x
whnfEnv r (Lam b) = applyExp r (Lam b)
whnfEnv {n = n} r (App f a) = apply (whnfEnv r f)
  where
    apply : Exp n → Exp n
    apply (Lam b) = instantiateWith {d = Exp} b (whnfEnv r a) whnfEnv
    apply f'      = App f' (applyExp r a)

{-# NON_TERMINATING #-}
nfEnv : ∀ {@0 n} → Exp n → Exp n
nfEnv (Var x) = Var x
nfEnv (Lam b) = Lam (bind (nfEnv (getBody b)))
nfEnv {n} (App f a) = apply (whnfEnv idE f)
  where
    apply : Exp n → Exp n
    apply (Lam b) = nfEnv (instantiate b (whnfEnv idE a))
    apply f'      = App (nfEnv f') (nfEnv a)
