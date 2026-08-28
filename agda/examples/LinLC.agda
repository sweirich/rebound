{-# OPTIONS --erasure #-}

-- | A *linear* lambda calculus: every variable must be used exactly
-- once.  The type checker tracks usage in a scope-indexed state monad,
-- and `rescope` is what carries that state under a binder and back.
--
-- Agda transcription of @rebound/examples/LinLC.hs@.
module LinLC where

open import Rebound
open import Rebound.Bind.Single
open import Rebound.MonadScoped
open import Data.Vec using (Vec; VNil; _:::_; vlookup; vtail; vlength; tabulate; foldr)

------------------------------------------------------------------------
-- * Syntax
------------------------------------------------------------------------

data Usage : Set where
  Unused : Usage
  Used   : Usage

eqUsage : Usage → Usage → Bool
eqUsage Unused Unused = true
eqUsage Used   Used   = true
eqUsage _      _      = false

data Ty : Set where
  TyUnit  : Ty
  TyArrow : Ty → Ty → Ty

infixr 8 _~>_
_~>_ : Ty → Ty → Ty
_~>_ = TyArrow

eqTy : Ty → Ty → Bool
eqTy TyUnit          TyUnit          = true
eqTy (TyArrow a b)   (TyArrow c d)   = eqTy a c && eqTy b d
eqTy _               _               = false

data Exp : @0 Nat → Set where
  Var   : ∀ {@0 n} → Fin n → Exp n
  CUnit : ∀ {@0 n} → Exp n
  Lam   : ∀ {@0 n} → Bind Exp Exp n → Exp n
  App   : ∀ {@0 n} → Exp n → Exp n → Exp n

instance
  SubstVarExp : SubstVar Exp
  SubstVar.var SubstVarExp = Var

{-# TERMINATING #-}
applyExp : ∀ {@0 n m} → Env Exp n m → Exp n → Exp m

instance
  SubstExpExp : Subst Exp Exp
  Subst.applyE SubstExpExp = applyExp

applyExp r (Var x)     = applyEnv r x
applyExp r CUnit       = CUnit
applyExp r (Lam b)     = Lam (applyBind r b)
applyExp r (App e1 e2) = App (applyExp r e1) (applyExp r e2)

lam : ∀ {@0 n} → Exp (S n) → Exp n
lam b = Lam (bind b)

infixl 9 _$$_
_$$_ : ∀ {@0 n} → Exp n → Exp n → Exp n
_$$_ = App

v0 : ∀ {@0 n} → Exp (S n)
v0 = Var f0

v1 : ∀ {@0 n} → Exp (S (S n))
v1 = Var f1

------------------------------------------------------------------------
-- * The checking monad
------------------------------------------------------------------------

record TCEnv (@0 n : Nat) : Set where
  constructor mkTCEnv
  field
    types  : Vec Ty    n
    usages : Vec Usage n
open TCEnv public

TC : @0 Nat → Set → Set
TC n a = ScopedStateT TCEnv String n a

open State {TCEnv} {String}

-- Haskell's `l << r`: run both, keep the first result.
infixl 1 _<<_
_<<_ : ∀ {@0 n} {a b : Set} → TC n a → TC n b → TC n a
l << r = l >>=S λ vl → r >>S returnS vl

------------------------------------------------------------------------
-- * Usage tracking
------------------------------------------------------------------------

-- | Replace the entry at an index, returning the old one.
set : ∀ {A} {@0 n} → Fin n → A → Vec A n → Vec A n × A
set FZ     v (h ::: t) = (v ::: t) , h
set (FS i) v (h ::: t) with set i v t
... | (t' , v') = (h ::: t') , v'

consumeVar : ∀ {@0 n} → Fin n → TC n Ty
consumeVar i = setUsage >>S getsS (λ e → vlookup (types e) i)
  where
    setUsage : TC _ ⊤
    setUsage =
      getsS usages >>=S λ current →
      chk (set i Used current)
      where
        chk : Vec Usage _ × Usage → TC _ ⊤
        chk (new , old) with eqUsage old Unused
        ... | true  = modifyS (λ e → mkTCEnv (types e) new)
        ... | false = throwErrorS "Variable has already been used."

-- | Check the current scope's variable 0 was consumed.
checkUsed : ∀ {@0 n} → TC (S n) ⊤
checkUsed =
  getsS (λ e → vlookup (usages e) f0) >>=S λ u →
  chk u
  where
    chk : Usage → TC _ ⊤
    chk Used   = returnS tt
    chk Unused = throwErrorS "Variable was not used."

-- | Run a computation one binder deeper.  `rescope` pushes the new
-- binding onto the state going in and pops it coming back out.
addBinder : ∀ {@0 n} {a : Set} → Ty → TC (S n) a → TC n a
addBinder ty m = rescope enter leave (m << checkUsed)
  where
    enter : TCEnv _ → TCEnv _
    enter e = mkTCEnv (ty ::: types e) (Unused ::: usages e)
    leave : TCEnv _ → TCEnv _
    leave e = mkTCEnv (vtail (types e)) (vtail (usages e))

------------------------------------------------------------------------
-- * Type checking
------------------------------------------------------------------------

inferType : ∀ {@0 n} → Exp n → TC n Ty
inferType (Var i) = consumeVar i
inferType CUnit   = returnS TyUnit
inferType _       = throwErrorS "Cannot infer type of this construct."

{-# TERMINATING #-}
checkType : ∀ {@0 n} → Exp n → Ty → TC n ⊤
checkType (Lam bnd) ty = ensureArrow ty
  where
    ensureArrow : Ty → TC _ ⊤
    ensureArrow (TyArrow l r) = addBinder l (checkType (unbindl bnd) r)
    ensureArrow _             = throwErrorS "Type is not arrow."
checkType (App f a) rTy =
  inferType a >>=S λ aTy → checkType f (TyArrow aTy rTy)
checkType t ty =
  inferType t >>=S λ ty' → chk (eqTy ty ty')
  where
    chk : Bool → TC _ ⊤
    chk true  = returnS tt
    chk false = throwErrorS "Inferred type does not match expected type."

-- Haskell needs an `SNatI n` constraint here, to build the initial
-- all-`Unused` vector.  With `n` erased Agda needs the same witness --
-- but the vector of types already carries one, so `vlength` recovers it
-- and no constraint appears in the signature.
runTC : ∀ {@0 n} {a : Set} → Vec Ty n → TC n a → Either String a
runTC {n} {a} ts c = run (vlength ts)
  where
    checkAllUsed : TC n ⊤
    checkAllUsed =
      getsS usages >>=S λ us →
      chk (foldr (λ u acc → eqUsage u Used && acc) true us)
      where
        chk : Bool → TC n ⊤
        chk true  = returnS tt
        chk false = throwErrorS "Some variables in the initial scope were not used."

    run : Singleton n → Either String a
    run ⟨ m , Refl ⟩ =
      evalScopedStateT (c << checkAllUsed) (mkTCEnv ts (tabulate m (λ _ → Unused)))

------------------------------------------------------------------------
-- * Examples
------------------------------------------------------------------------

-- λx. x   :   Unit ⊸ Unit          (linear: x is used exactly once)
idExp : Exp Z
idExp = lam v0

-- λx. λy. x   :   drops y, so it is *not* linear
dropExp : Exp Z
dropExp = lam (lam v1)
