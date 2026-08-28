{-# OPTIONS --erasure #-}

-- | A pure type system with Pi and Sigma types, and a @split@
-- eliminator for pairs.
--
-- Agda transcription of @rebound/examples/PTS.hs@.
module PTS where

open import Rebound
open import Rebound.Context
open import Rebound.Bind.PatN
  using ( Bind1; bind1; getBody1; instantiate1; unbindWith1
        ; Bind2; bind2; getBody2; instantiate2
        ; applyBind1; strengthenBind1; strengthenBindN )
import Rebound.Bind.PatN as PatN

------------------------------------------------------------------------
-- * Syntax
------------------------------------------------------------------------

data Exp : @0 Nat → Set where
  Star  : ∀ {@0 n} → Exp n
  Pi    : ∀ {@0 n} → Exp n → Bind1 Exp Exp n → Exp n
  Var   : ∀ {@0 n} → Fin n → Exp n
  Lam   : ∀ {@0 n} → Exp n → Bind1 Exp Exp n → Exp n
  App   : ∀ {@0 n} → Exp n → Exp n → Exp n
  Sigma : ∀ {@0 n} → Exp n → Bind1 Exp Exp n → Exp n
  Pair  : ∀ {@0 n} → Exp n → Exp n → Exp n → Exp n
  Split : ∀ {@0 n} → Exp n → Bind2 Exp Exp n → Exp n

instance
  SubstVarExp : SubstVar Exp
  SubstVar.var SubstVarExp = Var

-- Haskell derives this via GHC.Generics from a one-line `isVar`.
{-# TERMINATING #-}
applyExp : ∀ {@0 n m} → Env Exp n m → Exp n → Exp m

instance
  SubstExpExp : Subst Exp Exp
  Subst.applyE SubstExpExp = applyExp

applyExp r Star          = Star
applyExp r (Pi a b)      = Pi (applyExp r a) (applyBind1 r b)
applyExp r (Var x)       = applyEnv r x
applyExp r (Lam a b)     = Lam (applyExp r a) (applyBind1 r b)
applyExp r (App e1 e2)   = App (applyExp r e1) (applyExp r e2)
applyExp r (Sigma a b)   = Sigma (applyExp r a) (applyBind1 r b)
applyExp r (Pair a b t)  = Pair (applyExp r a) (applyExp r b) (applyExp r t)
applyExp r (Split a b)   = Split (applyExp r a) (PatN.applyBindN r b)

-- Also derived in Haskell.
{-# TERMINATING #-}
strengthenExp : ∀ {@0 n} (k m : Nat) → Exp (k + (m + n)) → Maybe (Exp (k + n))

instance
  StrengthenExp : Strengthen Exp
  Strengthen.strengthenRec StrengthenExp = strengthenExp

strengthenExp k m Star     = Just Star
strengthenExp k m (Var x)  = Var <$> strengthenRecFin k m x
  where open import Data.Fin using (strengthenRecFin)
strengthenExp k m (Pi a b) =
  strengthenExp k m a >>= λ a' → strengthenBind1 k m b >>= λ b' → Just (Pi a' b')
strengthenExp k m (Lam a b) =
  strengthenExp k m a >>= λ a' → strengthenBind1 k m b >>= λ b' → Just (Lam a' b')
strengthenExp k m (Sigma a b) =
  strengthenExp k m a >>= λ a' → strengthenBind1 k m b >>= λ b' → Just (Sigma a' b')
strengthenExp k m (App a b) =
  strengthenExp k m a >>= λ a' → strengthenExp k m b >>= λ b' → Just (App a' b')
strengthenExp k m (Pair a b t) =
  strengthenExp k m a >>= λ a' → strengthenExp k m b >>= λ b' →
  strengthenExp k m t >>= λ t' → Just (Pair a' b' t')
strengthenExp k m (Split a b) =
  strengthenExp k m a >>= λ a' → strengthenBindN k m b >>= λ b' → Just (Split a' b')

------------------------------------------------------------------------
-- * Examples
------------------------------------------------------------------------

t00 : Exp N2
t00 = App (Var f0) (Var f0)

t01 : Exp N2
t01 = App (Var f0) (Var f1)

t0 : Exp Z
t0 = Lam Star (bind1 (Var f0))

t1 : Exp Z
t1 = Lam Star (bind1 (Lam Star (bind1
       (App (Var f1) (App (Lam Star (bind1 (Var f0))) (Var f0))))))

tyid : ∀ {@0 n} → Exp n
tyid = Pi Star (bind1 (Pi (Var f0) (bind1 (Var f1))))

tmid : ∀ {@0 n} → Exp n
tmid = Lam Star (bind1 (Lam (Var f0) (bind1 (Var f0))))

------------------------------------------------------------------------
-- * Evaluation
------------------------------------------------------------------------

{-# NON_TERMINATING #-}
eval : ∀ {@0 n} → Exp n → Exp n
eval (Var x)      = Var x
eval (Lam a b)    = Lam a b
eval (App e1 e2)  = apply (eval e1) (eval e2)
  where
    apply : ∀ {@0 n} → Exp n → Exp n → Exp n
    apply (Lam a b) v = eval (instantiate1 b v)
    apply t         v = App t v
eval Star         = Star
eval (Pi a b)     = Pi a b
eval (Sigma a b)  = Sigma a b
eval (Pair a b t) = Pair a b t
eval {n} (Split a b)  = split (eval a)
  where
    split : Exp n → Exp n
    split (Pair a1 a2 _) = eval (instantiate2 b (eval a1) (eval a2))
    split t              = Split t b

{-# TERMINATING #-}
step : ∀ {@0 n} → Exp n → Maybe (Exp n)
step (Var x)              = Nothing
step (Lam a b)            = Nothing
step (App (Lam a b) e2)   = Just (instantiate1 b e2)
step (App e1 e2) with step e1
... | Just e1' = Just (App e1' e2)
... | Nothing with step e2
...   | Just e2' = Just (App e1 e2')
...   | Nothing  = Nothing
step Star                     = Nothing
step (Pi a b)                 = Nothing
step (Sigma a b)              = Nothing
step (Pair a b _)             = Nothing
step (Split (Pair a1 a2 _) b) = Just (instantiate2 b a1 a2)
step (Split a b) with step a
... | Just a' = Just (Split a' b)
... | Nothing = Nothing

{-# NON_TERMINATING #-}
eval' : ∀ {@0 n} → Exp n → Exp n
eval' e with step e
... | Just e' = eval' e'
... | Nothing = e

{-# NON_TERMINATING #-}
nf : ∀ {@0 n} → Exp n → Exp n
nf (Var x)      = Var x
nf (Lam a b)    = Lam a (bind1 (nf (getBody1 b)))
nf Star         = Star
nf (Pi a b)     = Pi (nf a) (bind1 (nf (getBody1 b)))
nf (Sigma a b)  = Sigma (nf a) (bind1 (nf (getBody1 b)))
nf (Pair a b t) = Pair (nf a) (nf b) (nf t)
nf {n} (App e1 e2)  = apply (nf e1)
  where
    apply : Exp n → Exp n
    apply (Lam a b) = nf (instantiate1 b e2)
    apply t         = App t (nf e2)
nf {n} (Split a b) = split (nf a)
  where
    split : Exp n → Exp n
    split (Pair a1 a2 _) = nf (instantiate2 b a1 a2)
    split t              = Split t (bind2 (nf (getBody2 b)))

{-# NON_TERMINATING #-}
whnf : ∀ {@0 n} → Exp n → Exp n
whnf {n} (App a1 a2) = apply (whnf a1)
  where
    apply : Exp n → Exp n
    apply (Lam a b) = whnf (instantiate1 b a1)
    apply t         = App t a2
whnf {n} (Split a b) = split (whnf a)
  where
    split : Exp n → Exp n
    split (Pair a1 a2 _) = whnf (instantiate2 b a1 a2)
    split t              = Split t b
whnf a = a

{-# NON_TERMINATING #-}
norm : ∀ {@0 n} → Exp n → Exp n
norm a = go (whnf a)
  where
    go : ∀ {@0 n} → Exp n → Exp n
    go (Lam a b)    = Lam (norm a) (bind1 (norm (getBody1 b)))
    go (Pi a b)     = Pi (norm a) (bind1 (norm (getBody1 b)))
    go (Sigma a b)  = Sigma (norm a) (bind1 (norm (getBody1 b)))
    go (Pair a b t) = Pair (norm a) (norm b) (norm t)
    go Star         = Star
    go (App a b)    = App a (norm b)
    go (Split a b)  = Split a (bind2 (norm (getBody2 b)))
    go (Var x)      = Var x

------------------------------------------------------------------------
-- * Evaluation with an explicit environment
------------------------------------------------------------------------

{-# NON_TERMINATING #-}
evalEnv : ∀ {@0 m n} → Env Exp m n → Exp m → Exp n
evalEnv r (Var x)      = applyEnv r x
evalEnv r (Lam a b)    = applyExp r (Lam a b)
evalEnv r Star         = Star
evalEnv r (Pi a b)     = applyExp r (Pi a b)
evalEnv r (Sigma a b)  = applyExp r (Sigma a b)
evalEnv r (Pair a b t) = applyExp r (Pair a b t)
evalEnv {n = n} r (App e1 e2) = apply (evalEnv r e1) (evalEnv r e2)
  where
    apply : Exp n → Exp n → Exp n
    apply (Lam a b) v = unbindWith1 b (λ r' e' → evalEnv (v ∷ r') e')
    apply t         v = App t v
evalEnv {n = n} r (Split a b) = split (evalEnv r a)
  where
    split : Exp n → Exp n
    split (Pair a1 a2 _) =
      PatN.unbindWith2 b (λ r' e' → evalEnv (a1 ∷ (a2 ∷ (r' >>> r))) e')
    split t = Split t (PatN.applyBindN r b)

------------------------------------------------------------------------
-- * Type checking
------------------------------------------------------------------------

data Err : Set where
  Equate        : ∀ {@0 n} → Exp n → Exp n → Err
  PiExpected    : ∀ {@0 n} → Exp n → Err
  SigmaExpected : ∀ {@0 n} → Exp n → Err
  VarEscapes    : ∀ {@0 n} → Exp n → Err

data Result (A : Set) : Set where
  ok  : A → Result A
  err : Err → Result A

infixl 1 _>>=ᵣ_
_>>=ᵣ_ : {A B : Set} → Result A → (A → Result B) → Result B
ok x  >>=ᵣ f = f x
err e >>=ᵣ _ = err e

{-# NON_TERMINATING #-}
equate     : ∀ {@0 n} → Exp n → Exp n → Result ⊤
equateWHNF : ∀ {@0 n} → Exp n → Exp n → Result ⊤

equate t1 t2 = equateWHNF (whnf t1) (whnf t2)

equateWHNF Star Star = ok tt
equateWHNF (Var x) (Var y) with eqFin x y
... | true  = ok tt
... | false = err (Equate (Var x) (Var y))
equateWHNF (Lam _ b1) (Lam _ b2) = equate (getBody1 b1) (getBody1 b2)
equateWHNF (App a1 a2) (App b1 b2) =
  equateWHNF a1 b1 >>=ᵣ λ _ → equate a2 b2
equateWHNF (Pi tyA1 b1) (Pi tyA2 b2) =
  equate tyA1 tyA2 >>=ᵣ λ _ → equate (getBody1 b1) (getBody1 b2)
equateWHNF (Sigma tyA1 b1) (Sigma tyA2 b2) =
  equate tyA1 tyA2 >>=ᵣ λ _ → equate (getBody1 b1) (getBody1 b2)
equateWHNF (Pair a1 a2 _) (Pair b1 b2 _) =
  equate a1 b1 >>=ᵣ λ _ → equate a2 b2
equateWHNF (Split a1 b1) (Split a2 b2) =
  equateWHNF a1 a2 >>=ᵣ λ _ → equate (getBody2 b1) (getBody2 b2)
equateWHNF n1 n2 = err (Equate n1 n2)

{-# NON_TERMINATING #-}
inferType  : ∀ {@0 n} → Ctx Exp n → Exp n → Result (Exp n)
checkType  : ∀ {@0 n} → Ctx Exp n → Exp n → Exp n → Result ⊤
inferApp   : ∀ {@0 n} → Ctx Exp n → Exp n → Exp n → Result (Exp n)
checkPair  : ∀ {@0 n} → Ctx Exp n → Exp n → Exp n → Exp n → Result (Exp n)
inferSplit : ∀ {@0 n} → Ctx Exp n → Bind2 Exp Exp n → Exp n → Result (Exp n)

checkType g e t1 = inferType g e >>=ᵣ λ t2 → equate (whnf t2) t1

inferType g (Var x) = ok (applyEnv g x)
inferType g Star    = ok Star
inferType g (Pi a b) =
  checkType g a Star >>=ᵣ λ _ →
  checkType (g +++ a) (getBody1 b) Star >>=ᵣ λ _ → ok Star
inferType g (Sigma a b) =
  checkType g a Star >>=ᵣ λ _ →
  checkType (g +++ a) (getBody1 b) Star >>=ᵣ λ _ → ok Star
inferType g (Lam tyA b) =
  checkType g tyA Star >>=ᵣ λ _ →
  inferType (g +++ tyA) (getBody1 b) >>=ᵣ λ tyB → ok (Pi tyA (bind1 tyB))
inferType g (App a b) = inferType g a >>=ᵣ λ tyA → inferApp g b (whnf tyA)
inferType g (Pair a b ty) =
  inferType g a >>=ᵣ λ _ → inferType g b >>=ᵣ λ _ → checkPair g a b ty
inferType g (Split a b) = inferType g a >>=ᵣ λ tyA → inferSplit g b (whnf tyA)

inferApp g b (Pi tyA1 tyB1) =
  checkType g b tyA1 >>=ᵣ λ _ → ok (instantiate1 tyB1 b)
inferApp g b t = err (PiExpected t)

checkPair g a b (Sigma tyA tyB) =
  checkType g a tyA >>=ᵣ λ _ →
  checkType g b (instantiate1 tyB a) >>=ᵣ λ _ → ok (Sigma tyA tyB)
checkPair g a b ty = err (SigmaExpected ty)

-- The body of a `split` is checked in a scope extended by two
-- variables, so its type must then be strengthened back -- and that is
-- allowed to fail, which is what `VarEscapes` reports.
inferSplit {n} g b (Sigma tyA' tyB') =
  inferType ((g +++ tyA') +++ getBody1 tyB') (getBody2 b) >>=ᵣ λ ty →
  chk ty (strengthenN 2 (whnf ty))
  where
    chk : Exp (S (S n)) → Maybe (Exp n) → Result (Exp n)
    chk ty (Just ty'') = ok ty''
    chk ty Nothing     = err (VarEscapes ty)
inferSplit g b t = err (SigmaExpected t)
