{-# OPTIONS --erasure #-}

-- | Lambda calculus extended with several forms of @let@: simple,
-- recursive, telescopic, and mutually recursive.
--
-- Agda transcription of @rebound/examples/LCLet.hs@.
module LCLet where

open import Rebound
open import Rebound.Bind.Single
open import Rebound.Bind.PatN using (BindN; bindN; getBodyN; instantiateN; applyBindN)
open import Data.Vec using (Vec; VNil; _:::_; map; all2)
import Rebound.Bind.Pat as Pat

------------------------------------------------------------------------
-- * Syntax
------------------------------------------------------------------------

data Exp    : @0 Nat → Set
data Rec    : @0 Nat → Set
data MutRec : @0 Nat → Set
data Tele   : @0 Nat → Set

data Exp where
  Var       : ∀ {@0 n} → Fin n → Exp n
  Lam       : ∀ {@0 n} → Bind Exp Exp n → Exp n
  App       : ∀ {@0 n} → Exp n → Exp n → Exp n
  Let       : ∀ {@0 n} → Exp n → Bind Exp Exp n → Exp n
  LetRec    : ∀ {@0 n} → Rec n → Exp n
  LetTele   : ∀ {@0 n} → Tele n → Exp n
  LetMutRec : ∀ {@0 n} → MutRec n → Exp n

data Rec where
  mkRec : ∀ {@0 n}
        → Bind Exp Exp n    -- single RHS
        → Bind Exp Exp n    -- body of let
        → Rec n

rec-rhs : ∀ {@0 n} → Rec n → Bind Exp Exp n
rec-rhs (mkRec r b) = r

rec-body : ∀ {@0 n} → Rec n → Bind Exp Exp n
rec-body (mkRec r b) = b

-- Haskell writes the existential as @forall m. SNatI m => ...@; the
-- `SNatI m` constraint becomes a `Singleton m` field, since with `m`
-- erased that is the only way to compare two `MutRec`s.
data MutRec where
  mkMutRec : ∀ {@0 m n}
           → Singleton m
           → Vec (BindN Exp Exp m n) m   -- vector of RHSs
           → BindN Exp Exp m n           -- body of let
           → MutRec n

data Tele where
  LetStar : ∀ {@0 n} → Exp n → Bind Exp Tele n → Tele n
  Body    : ∀ {@0 n} → Exp n → Tele n

------------------------------------------------------------------------
-- * Substitution
------------------------------------------------------------------------

instance
  SubstVarExp : SubstVar Exp
  SubstVar.var SubstVarExp = Var

{-# TERMINATING #-}
applyExp    : ∀ {@0 n m} → Env Exp n m → Exp n → Exp m
applyRec    : ∀ {@0 n m} → Env Exp n m → Rec n → Rec m
applyMutRec : ∀ {@0 n m} → Env Exp n m → MutRec n → MutRec m
applyTele   : ∀ {@0 n m} → Env Exp n m → Tele n → Tele m

instance
  SubstExpExp : Subst Exp Exp
  Subst.applyE SubstExpExp = applyExp

  SubstExpRec : Subst Exp Rec
  Subst.applyE SubstExpRec = applyRec

  SubstExpMutRec : Subst Exp MutRec
  Subst.applyE SubstExpMutRec = applyMutRec

  SubstExpTele : Subst Exp Tele
  Subst.applyE SubstExpTele = applyTele

applyExp r (Var x)        = applyEnv r x
applyExp r (Lam b)        = Lam (applyBind r b)
applyExp r (App e1 e2)    = App (applyExp r e1) (applyExp r e2)
applyExp r (Let e1 e2)    = Let (applyExp r e1) (applyBind r e2)
applyExp r (LetRec e)     = LetRec (applyRec r e)
applyExp r (LetTele e)    = LetTele (applyTele r e)
applyExp r (LetMutRec e)  = LetMutRec (applyMutRec r e)

applyRec r (mkRec rhs body) = mkRec (applyBind r rhs) (applyBind r body)

applyMutRec r (mkMutRec m rhss body) =
  mkMutRec m (map (applyBindN r) rhss) (applyBindN r body)

applyTele r (Body e)         = Body (applyExp r e)
applyTele r (LetStar e1 e2)  = LetStar (applyExp r e1) (applyBind r e2)

------------------------------------------------------------------------
-- * Smart constructors and examples
------------------------------------------------------------------------

v0 : ∀ {@0 n} → Exp (S n)
v0 = Var f0

v1 : ∀ {@0 n} → Exp (S (S n))
v1 = Var f1

v2 : ∀ {@0 n} → Exp (S (S (S n)))
v2 = Var f2

infixl 9 _$$_
_$$_ : ∀ {@0 n} → Exp n → Exp n → Exp n
_$$_ = App

lam : ∀ {@0 n} → Exp (S n) → Exp n
lam b = Lam (bind b)

letrec : ∀ {@0 n} → Exp (S n) → Exp (S n) → Exp n
letrec e1 e2 = LetRec (mkRec (bind e1) (bind e2))

letstar : ∀ {@0 n} → Exp n → Tele (S n) → Tele n
letstar e t = LetStar e (bind t)

t0 : ∀ {@0 n} → Exp n
t0 = lam v0

t1 : Exp Z
t1 = lam (lam (v1 $$ (lam v0 $$ v0)))

t2 : Exp Z
t2 = Let t0 (bind (App v0 v0))

t3 : Exp Z
t3 = letrec (lam (v0 $$ (v1 $$ v0))) v0

t4 : Exp Z
t4 = LetTele
       (letstar t0
         (letstar (v0 $$ v0)
            (letstar (v0 $$ v1)
              (Body ((v0 $$ v1) $$ v2)))))

------------------------------------------------------------------------
-- * Evaluation
------------------------------------------------------------------------

-- AGDA: `LetRec` and `LetMutRec` tie a knot -- in Haskell they read
--
--     let v  = instantiate (rec_rhs e) v            in ...
--     let vs = fmap (\b -> instantiateN b vs) rhss  in ...
--
-- which only makes sense because Haskell is lazy: `v` is a cyclic value,
-- not a computation that runs forever.  Agda has no recursive `let`, so
-- the knot becomes a recursive `where` definition, asserted terminating.
-- It computes for the same reason the Haskell does: the GHC backend the
-- program is compiled with is lazy.
{-# NON_TERMINATING #-}
eval     : ∀ {@0 n} → Exp n → Exp n
evalTele : ∀ {@0 n} → Tele n → Exp n

eval (Var x) = Var x
eval (Lam b) = Lam b
eval (App e1 e2) = apply (eval e1) (eval e2)
  where
    apply : ∀ {@0 n} → Exp n → Exp n → Exp n
    apply (Lam b) v = eval (instantiate b v)
    apply t       v = App t v
eval (Let e1 e2) = eval (instantiate e2 (eval e1))
eval {n} (LetRec e) = eval (instantiate (rec-body e) v)
  where
    v : Exp n
    v = instantiate (rec-rhs e) v
eval (LetTele e) = evalTele e
eval {n} (LetMutRec (mkMutRec m rhss body)) = eval (instantiateN body vs)
  where
    vs : Vec (Exp n) _
    vs = map (λ b → instantiateN b vs) rhss

evalTele (Body e)      = eval e
evalTele (LetStar e t) = evalTele (instantiate t (eval e))
