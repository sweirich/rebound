{-# OPTIONS --erasure #-}

-- | System F with types and terms in a *single* scope, distinguished by
-- a tag index.  Type and term variables are therefore substituted by the
-- same machinery, with `AnyExp` as the common variable type.
--
-- The type checker runs in a scope-indexed reader monad, and the pretty
-- printer in another one — `localS` is what carries an environment under
-- a binder.
--
-- Agda transcription of @rebound/examples/TaggedSystemF.hs@.
module TaggedSystemF where

open import Rebound
open import Rebound.Context
open import Rebound.Bind.Local
open import Rebound.MonadScoped
open import Data.Vec using (Vec; VNil; _:::_; vlookup; map)
import Rebound.Bind.Pat as BindPat

------------------------------------------------------------------------
-- * Syntax
------------------------------------------------------------------------

data Tag : Set where
  TTy : Tag
  TTm : Tag

data Exp    : Tag → @0 Nat → Set
record AnyExp (@0 n : Nat) : Set

Ty : @0 Nat → Set
Ty = Exp TTy

Tm : @0 Nat → Set
Tm = Exp TTm

-- The variable type for the combined substitution: a bare index, which
-- can stand for either a type or a term variable.
record AnyExp n where
  constructor mkAnyExp
  field anyExpVar : Fin n
open AnyExp public

data Exp where
  Var  : ∀ {tag} {@0 n} → Fin n → Exp tag n
  Kind : ∀ {@0 n} → Ty n
  TAll : ∀ {@0 n} → Bind Ty Ty n → Ty n
  TArr : ∀ {@0 n} → Ty n → Ty n → Ty n
  Abs  : ∀ {@0 n} → Ty n → Bind AnyExp Tm n → Tm n
  App  : ∀ {@0 n} → Tm n → Tm n → Tm n
  TAbs : ∀ {@0 n} → Bind AnyExp Tm n → Tm n
  TApp : ∀ {@0 n} → Tm n → Ty n → Tm n

unAnyExp : ∀ {tag} {@0 n} → AnyExp n → Exp tag n
unAnyExp (mkAnyExp x) = Var x

------------------------------------------------------------------------
-- * Substitution
------------------------------------------------------------------------

instance
  SubstVarAny : SubstVar AnyExp
  SubstVar.var SubstVarAny = mkAnyExp

  SubstVarTy : SubstVar Ty
  SubstVar.var SubstVarTy = Var

{-# TERMINATING #-}
applyAny : ∀ {@0 n m} → Env AnyExp n m → AnyExp n → AnyExp m
applyAnyE : ∀ {tag} {@0 n m} → Env AnyExp n m → Exp tag n → Exp tag m
applyTy  : ∀ {@0 n m} → Env Ty n m → Ty n → Ty m

instance
  SubstAnyAny : Subst AnyExp AnyExp
  Subst.applyE SubstAnyAny = applyAny

  SubstAnyExp : ∀ {tag} → Subst AnyExp (Exp tag)
  Subst.applyE SubstAnyExp = applyAnyE

  SubstTyTy : Subst Ty Ty
  Subst.applyE SubstTyTy = applyTy

applyAny env a = applyEnv env (anyExpVar a)

applyAnyE env (Var x)      = unAnyExp (applyEnv env x)
applyAnyE env Kind         = Kind
applyAnyE env (TAll bnd)   = TAll (bind (getPat bnd) (applyAnyE (up env) (getBody bnd)))
applyAnyE env (TArr t1 t2) = TArr (applyAnyE env t1) (applyAnyE env t2)
applyAnyE env (Abs ty bnd) = Abs (applyAnyE env ty) (applyBind env bnd)
applyAnyE env (App t1 t2)  = App (applyAnyE env t1) (applyAnyE env t2)
applyAnyE env (TAbs bnd)   = TAbs (applyBind env bnd)
applyAnyE env (TApp t1 t2) = TApp (applyAnyE env t1) (applyAnyE env t2)

applyTy env (Var x)      = applyEnv env x
applyTy env Kind         = Kind
applyTy env (TAll bnd)   = TAll (applyBind env bnd)
applyTy env (TArr t1 t2) = TArr (applyTy env t1) (applyTy env t2)

------------------------------------------------------------------------
-- * Strengthening
------------------------------------------------------------------------

{-# TERMINATING #-}
strengthenExp : ∀ {tag} {@0 n} (k m : Nat)
              → Exp tag (k + (m + n)) → Maybe (Exp tag (k + n))

instance
  StrengthenAny : Strengthen AnyExp
  Strengthen.strengthenRec StrengthenAny k m a =
    mkAnyExp <$> strengthenRecFin k m (anyExpVar a)
    where open import Data.Fin using (strengthenRecFin)

  StrengthenExp : ∀ {tag} → Strengthen (Exp tag)
  Strengthen.strengthenRec StrengthenExp = strengthenExp

strengthenExp k m (Var x) = Var <$> strengthenRecFin k m x
  where open import Data.Fin using (strengthenRecFin)
strengthenExp k m Kind = Just Kind
strengthenExp k m (TAll bnd) = TAll <$> strengthenBind k m bnd
strengthenExp k m (TArr t1 t2) =
  strengthenExp k m t1 >>= λ a → strengthenExp k m t2 >>= λ b → Just (TArr a b)
strengthenExp k m (Abs ty bnd) =
  strengthenExp k m ty >>= λ a → strengthenBind k m bnd >>= λ b → Just (Abs a b)
strengthenExp k m (App t1 t2) =
  strengthenExp k m t1 >>= λ a → strengthenExp k m t2 >>= λ b → Just (App a b)
strengthenExp k m (TAbs bnd) = TAbs <$> strengthenBind k m bnd
strengthenExp k m (TApp t1 t2) =
  strengthenExp k m t1 >>= λ a → strengthenExp k m t2 >>= λ b → Just (TApp a b)

------------------------------------------------------------------------
-- * Alpha-equivalence
------------------------------------------------------------------------

{-# TERMINATING #-}
eqExp : ∀ {tag} {@0 n} → Exp tag n → Exp tag n → Bool
eqExp (Var x)      (Var y)      = eqFin x y
eqExp Kind         Kind         = true
eqExp (TAll b1)    (TAll b2)    = eqExp (getBody b1) (getBody b2)
eqExp (TArr a1 b1) (TArr a2 b2) = eqExp a1 a2 && eqExp b1 b2
eqExp (Abs t1 b1)  (Abs t2 b2)  = eqExp t1 t2 && eqExp (getBody b1) (getBody b2)
eqExp (App a1 b1)  (App a2 b2)  = eqExp a1 a2 && eqExp b1 b2
eqExp (TAbs b1)    (TAbs b2)    = eqExp (getBody b1) (getBody b2)
eqExp (TApp a1 b1) (TApp a2 b2) = eqExp a1 a2 && eqExp b1 b2
eqExp _            _            = false

------------------------------------------------------------------------
-- * The checking monad
------------------------------------------------------------------------

record TcEnv (@0 n : Nat) : Set where
  constructor mkTcEnv
  field
    names : Vec LocalName n
    types : Ctx Ty n
open TcEnv public

emptyEnv : TcEnv Z
emptyEnv = mkTcEnv VNil zeroE

extendE : ∀ {@0 n} → LocalName → Ty n → TcEnv n → TcEnv (S n)
extendE nm t (mkTcEnv ns ts) = mkTcEnv (nm ::: ns) (ts +++ t)

lookupE : ∀ {@0 n} → TcEnv n → Fin n → LocalName × Ty n
lookupE (mkTcEnv ns ts) i = vlookup ns i , applyEnv ts i

Error : Set
Error = String

TC : @0 Nat → Set → Set
TC n a = ScopedReaderT TcEnv Error n a

open Reader {TcEnv} {Error}

runTC : ∀ {@0 n} {a : Set} → TcEnv n → TC n a → Either Error a
runTC env m = runScopedReaderT m env

-- | Go under a binder, extending the environment.  This is `localS`.
push : ∀ {@0 n} {a : Set} → LocalName → Ty n → TC (S n) a → TC n a
push nm t = localS (extendE nm t)

get : ∀ {@0 n} → Fin n → TC n (LocalName × Ty n)
get i = asksS (λ e → lookupE e i)

------------------------------------------------------------------------
-- * Type checking
------------------------------------------------------------------------

{-# TERMINATING #-}
ensureType : ∀ {@0 n} → Ty n → TC n ⊤
inferType  : ∀ {tag} {@0 n} → Exp tag n → TC n (Ty n)

ensureType Kind = returnR tt
ensureType ty =
  inferType ty >>=R λ k → chk (eqExp k Kind)
  where
    chk : Bool → TC _ ⊤
    chk true  = returnR tt
    chk false = throwErrorR "Not a type"

inferType (Var x) =
  get x >>=R λ p → ensureType (snd p) >>R returnR (snd p)
inferType Kind = throwErrorR "Cannot type 'Kind'"
inferType (TAll bnd) =
  push (getPat bnd) Kind (ensureType (getBody bnd)) >>R returnR Kind
inferType (TArr l r) =
  ensureType l >>R ensureType r >>R returnR Kind
inferType (Abs xTy bnd) =
  ensureType xTy >>R
  push (getPat bnd) xTy (inferType (getBody bnd)) >>=R λ tTy →
  chk (strengthenN 1 tTy)
  where
    chk : Maybe (Ty _) → TC _ (Ty _)
    chk (Just tTy') = returnR (TArr xTy tTy')
    chk Nothing     = throwErrorR "Term variable occurs in type"
inferType (App l r) =
  inferType l >>=R λ lTy → inferType r >>=R λ rTy → chk lTy rTy
  where
    chk : ∀ {@0 n} → Ty n → Ty n → TC n (Ty n)
    chk (TArr rTy' retTy) rTy with eqExp rTy rTy'
    ... | true  = returnR retTy
    ... | false = throwErrorR "Argument mismatch"
    chk _ _ = throwErrorR "Left hand-side of application is not an arrow"
inferType (TAbs bnd) =
  push (getPat bnd) Kind (inferType (getBody bnd)) >>=R λ tTy →
  returnR (TAll (bind (getPat bnd) tTy))
inferType (TApp l r) =
  inferType l >>=R λ lTy → ensureType r >>R chk r lTy
  where
    chk : ∀ {@0 n} → Ty n → Ty n → TC n (Ty n)
    chk r (TAll bnd) = returnR (instantiate bnd r)
    chk r _          = throwErrorR "Left hand-side is not a forall"

------------------------------------------------------------------------
-- * Examples
------------------------------------------------------------------------

nA : LocalName
nA = mkLocalName "A"

nx : LocalName
nx = mkLocalName "x"

-- ΛA. λx:A. x
polyId : Tm Z
polyId = TAbs (bind nA (Abs (Var f0) (bind nx (Var f0))))

-- ∀A. A → A
polyIdTy : Ty Z
polyIdTy = TAll (bind nA (TArr (Var f0) (Var f0)))

-- ΛA. λx:A. x x   -- ill-typed: x is not a function
bad : Tm Z
bad = TAbs (bind nA (Abs (Var f0) (bind nx (App (Var f0) (Var f0)))))
