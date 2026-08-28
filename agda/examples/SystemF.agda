{-# OPTIONS --erasure #-}

-- | System F, with separate scopes for type and term variables.
--
-- Agda transcription of @rebound/examples/SystemF.hs@.
--
-- One issue with this example is that we only store one sort of
-- environment at each binder.  However, terms are subject to two
-- different forms of substitution -- either for terms or types.  So
-- applying the "wrong" sort through a binder means that we don't gain
-- any advantage from the caching: we need to bind and unbind to
-- propagate.
module SystemF where

open import Rebound
open import Rebound.Bind.Single

------------------------------------------------------------------------
-- * Syntax
------------------------------------------------------------------------

data Ty : @0 Nat → Set where
  TVar : ∀ {@0 n} → Fin n → Ty n
  TAll : ∀ {@0 n} → Bind Ty Ty n → Ty n
  TArr : ∀ {@0 n} → Ty n → Ty n → Ty n

data Exp : @0 Nat → @0 Nat → Set

-- Haskell uses a newtype to flip the two indices, so that @TyExp n@ is
-- the thing a type-substitution acts on.  A record does the same here --
-- and unlike a type synonym it gives a real head for instance search.
record TyExp (@0 n : Nat) (@0 m : Nat) : Set where
  inductive
  constructor mkTyExp
  field unTyExp : Exp m n
open TyExp public

data Exp where
  EVar  : ∀ {@0 m n} → Fin n → Exp m n
  ELam  : ∀ {@0 m n} → Ty m → Bind (Exp m) (Exp m) n → Exp m n
  EApp  : ∀ {@0 m n} → Exp m n → Exp m n → Exp m n
  ETLam : ∀ {@0 m n} → Bind Ty (TyExp n) m → Exp m n
  ETApp : ∀ {@0 m n} → Exp m n → Ty m → Exp m n

------------------------------------------------------------------------
-- * Substitution
------------------------------------------------------------------------

instance
  SubstVarTy : SubstVar Ty
  SubstVar.var SubstVarTy = TVar

  SubstVarExp : ∀ {@0 m} → SubstVar (Exp m)
  SubstVar.var SubstVarExp = EVar

{-# TERMINATING #-}
applyTy    : ∀ {@0 n m} → Env Ty n m → Ty n → Ty m
applyTyExp : ∀ {@0 n m1 m2} → Env Ty m1 m2 → TyExp n m1 → TyExp n m2
applyExp   : ∀ {@0 m n1 n2} → Env (Exp m) n1 n2 → Exp m n1 → Exp m n2

instance
  SubstTyTy : Subst Ty Ty
  Subst.applyE SubstTyTy = applyTy

  SubstTyTyExp : ∀ {@0 n} → Subst Ty (TyExp n)
  Subst.applyE SubstTyTyExp = applyTyExp

  SubstExpExp : ∀ {@0 m} → Subst (Exp m) (Exp m)
  Subst.applyE SubstExpExp = applyExp

applyTy r (TVar x)     = applyEnv r x
applyTy r (TAll b)     = TAll (applyBind r b)
applyTy r (TArr t1 t2) = TArr (applyTy r t1) (applyTy r t2)

-- | Substitute types throughout a term.
substTy : ∀ {@0 m1 m2 n} → Env Ty m1 m2 → Exp m1 n → Exp m2 n
substTy r e = unTyExp (applyTyExp r (mkTyExp e))

applyTyExp r (mkTyExp (EVar x))     = mkTyExp (EVar x)
applyTyExp r (mkTyExp (ELam ty b))  = mkTyExp (ELam (applyTy r ty) (bind (substTy r (getBody b))))
applyTyExp r (mkTyExp (EApp e1 e2)) = mkTyExp (EApp (substTy r e1) (substTy r e2))
applyTyExp r (mkTyExp (ETLam b))    = mkTyExp (ETLam (bind (applyTyExp (up r) (getBody b))))
applyTyExp r (mkTyExp (ETApp e1 t2)) = mkTyExp (ETApp (substTy r e1) (applyTy r t2))

-- | Move a term environment into a larger type scope.
upTyScope : ∀ {@0 m n1 n2} → Env (Exp m) n1 n2 → Env (Exp (S m)) n1 n2
upTyScope = transform (substTy shift1E)

applyExp r (EVar x)     = applyEnv r x
applyExp r (ELam ty b)  = ELam ty (applyBind r b)
applyExp r (EApp t1 t2) = EApp (applyExp r t1) (applyExp r t2)
applyExp r (ETLam b)    = ETLam (bind (mkTyExp (applyExp (upTyScope r) (unTyExp (getBody b)))))
applyExp r (ETApp e t)  = ETApp (applyExp r e) t

------------------------------------------------------------------------
-- * Type checking
------------------------------------------------------------------------

data FCtx : @0 Nat → @0 Nat → Set where
  Empty     : FCtx Z Z
  ConsTmVar : ∀ {@0 m n} → Ty m → FCtx m n → FCtx m (S n)
  ConsTyVar : ∀ {@0 m n} → FCtx m n → FCtx (S m) n

lookup : ∀ {@0 m n} → Fin n → FCtx m n → Ty m
lookup FZ     (ConsTmVar ty _) = ty
lookup FZ     (ConsTyVar g)    = applyTy shift1E (lookup FZ g)
lookup (FS x) (ConsTmVar _ g)  = lookup x g
lookup (FS x) (ConsTyVar g)    = applyTy shift1E (lookup (FS x) g)

-- Haskell derives this; Agda spells it out.  (It is alpha-equivalence.)
{-# TERMINATING #-}
eqTy : ∀ {@0 n} → Ty n → Ty n → Bool
eqTy (TVar x)     (TVar y)     = eqFin x y
eqTy (TAll b1)    (TAll b2)    = eqTy (getBody b1) (getBody b2)
eqTy (TArr a1 b1) (TArr a2 b2) = eqTy a1 a2 && eqTy b1 b2
eqTy _            _            = false

{-# TERMINATING #-}
tc : ∀ {@0 m n} → FCtx m n → Exp m n → Maybe (Ty m)
tc g (EVar x)    = return (lookup x g)
tc g (ELam ty b) = tc (ConsTmVar ty g) (getBody b)
tc g (EApp a b)  = tc g a >>= λ t1 → tc g b >>= λ t2 → tcApp t1 t2
  where
    tcApp : ∀ {@0 m} → Ty m → Ty m → Maybe (Ty m)
    tcApp (TArr t11 t12) t2 with eqTy (TArr t11 t12) t2
    ... | true  = Just t12
    ... | false = Nothing
    tcApp _ _ = Nothing
tc g (ETLam b)   = tc (ConsTyVar g) (unTyExp (getBody b)) >>= λ t1 → return (TAll (bind t1))
tc g (ETApp a ty) = tc g a >>= λ t1 → tcTApp ty t1
  where
    tcTApp : ∀ {@0 m} → Ty m → Ty m → Maybe (Ty m)
    tcTApp ty (TAll tb) = Just (instantiate tb ty)
    tcTApp ty _         = Nothing
