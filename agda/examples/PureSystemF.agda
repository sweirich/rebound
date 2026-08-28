{-# OPTIONS --erasure #-}

-- | System F with types and terms in a single syntactic category and a
-- single scope — the untagged counterpart of "TaggedSystemF".
--
-- Both the type checker and the pretty printer run in scope-indexed
-- reader monads.  The printer is the clearer demonstration: `localP`
-- carries the name environment under a binder, and the same combinator
-- also threads the precedence level.
--
-- Agda transcription of @rebound/examples/PureSystemF.hs@.
module PureSystemF where

open import Rebound
open import Rebound.Context
open import Rebound.Bind.Local
open import Rebound.MonadScoped
open import Data.Vec using (Vec; VNil; _:::_; vlookup; map)

------------------------------------------------------------------------
-- * Syntax
------------------------------------------------------------------------

data Exp : @0 Nat → Set where
  Var  : ∀ {@0 n} → Fin n → Exp n
  Kind : ∀ {@0 n} → Exp n
  TAll : ∀ {@0 n} → Bind Exp Exp n → Exp n
  TArr : ∀ {@0 n} → Exp n → Exp n → Exp n
  Abs  : ∀ {@0 n} → Exp n → Bind Exp Exp n → Exp n
  App  : ∀ {@0 n} → Exp n → Exp n → Exp n
  TAbs : ∀ {@0 n} → Bind Exp Exp n → Exp n
  TApp : ∀ {@0 n} → Exp n → Exp n → Exp n

-- Types and terms are the same thing here.
Ty : @0 Nat → Set
Ty = Exp

instance
  SubstVarExp : SubstVar Exp
  SubstVar.var SubstVarExp = Var

{-# TERMINATING #-}
applyExp : ∀ {@0 n m} → Env Exp n m → Exp n → Exp m

instance
  SubstExpExp : Subst Exp Exp
  Subst.applyE SubstExpExp = applyExp

applyExp env (Var x)      = applyEnv env x
applyExp env Kind         = Kind
applyExp env (TAll bnd)   = TAll (applyBind env bnd)
applyExp env (TArr t1 t2) = TArr (applyExp env t1) (applyExp env t2)
applyExp env (Abs ty bnd) = Abs (applyExp env ty) (applyBind env bnd)
applyExp env (App t1 t2)  = App (applyExp env t1) (applyExp env t2)
applyExp env (TAbs bnd)   = TAbs (applyBind env bnd)
applyExp env (TApp t1 t2) = TApp (applyExp env t1) (applyExp env t2)

{-# TERMINATING #-}
strengthenExp : ∀ {@0 n} (k m : Nat) → Exp (k + (m + n)) → Maybe (Exp (k + n))

instance
  StrengthenExp : Strengthen Exp
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

{-# TERMINATING #-}
eqExp : ∀ {@0 n} → Exp n → Exp n → Bool
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
    types : Ctx Exp n
open TcEnv public

emptyEnv : TcEnv Z
emptyEnv = mkTcEnv VNil zeroE

extendE : ∀ {@0 n} → LocalName → Exp n → TcEnv n → TcEnv (S n)
extendE nm t (mkTcEnv ns ts) = mkTcEnv (nm ::: ns) (ts +++ t)

lookupE : ∀ {@0 n} → TcEnv n → Fin n → LocalName × Exp n
lookupE (mkTcEnv ns ts) i = vlookup ns i , applyEnv ts i

Error : Set
Error = String

TC : @0 Nat → Set → Set
TC n a = ScopedReaderT TcEnv Error n a

open Reader {TcEnv} {Error}

runTC : ∀ {@0 n} {a : Set} → TcEnv n → TC n a → Either Error a
runTC env m = runScopedReaderT m env

push : ∀ {@0 n} {a : Set} → LocalName → Exp n → TC (S n) a → TC n a
push nm t = localS (extendE nm t)

get : ∀ {@0 n} → Fin n → TC n (LocalName × Exp n)
get i = asksS (λ e → lookupE e i)

------------------------------------------------------------------------
-- * Type checking
------------------------------------------------------------------------

{-# TERMINATING #-}
ensureType : ∀ {@0 n} → Ty n → TC n ⊤
inferType  : ∀ {@0 n} → Exp n → TC n (Ty n)

ensureType Kind = returnR tt
ensureType ty =
  inferType ty >>=R λ k → chk (eqExp k Kind)
  where
    chk : Bool → TC _ ⊤
    chk true  = returnR tt
    chk false = throwErrorR "Not a type"

inferType (Var x) = get x >>=R λ p → ensureType (snd p) >>R returnR (snd p)
inferType Kind    = throwErrorR "Cannot type 'Kind'"
inferType (TAll bnd) =
  push (getPat bnd) Kind (ensureType (getBody bnd)) >>R returnR Kind
inferType (TArr l r) = ensureType l >>R ensureType r >>R returnR Kind
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
-- * Pretty printing
------------------------------------------------------------------------

-- The printer is the cleanest use of the scope-indexed reader: the name
-- environment grows under a binder, which is exactly `localP`.

record PpEnv (@0 n : Nat) : Set where
  constructor mkPpEnv
  field
    ppnames : Vec String n
    pplevel : Nat
open PpEnv public

open PureReader {PpEnv}

setLevel : ∀ {@0 n} → Nat → ScopedReader PpEnv n String → ScopedReader PpEnv n String
setLevel l = localP (λ e → mkPpEnv (ppnames e) l)

atLevel : ∀ {@0 n} → Nat → ScopedReader PpEnv n String → ScopedReader PpEnv n String
atLevel l m = asksP pplevel >>=P λ lvl → setLevel l (choose (leNat lvl l))
  where
    choose : Bool → ScopedReader PpEnv _ String
    choose true  = m
    choose false = λ e → "(" <>ˢ (m e <>ˢ ")")

pushName : ∀ {@0 n} → String → ScopedReader PpEnv (S n) String
         → ScopedReader PpEnv n String
pushName x = localP (λ e → mkPpEnv (x ::: ppnames e) (pplevel e))

{-# TERMINATING #-}
pp' : ∀ {@0 n} → Exp n → ScopedReader PpEnv n String
pp' (Var f) = asksP (λ e → vlookup (ppnames e) f)
pp' Kind    = returnP "Kind"
pp' (TAll bnd) = atLevel 0
  (pushName (name (getPat bnd)) (pp' (getBody bnd)) >>=P λ b' →
   returnP ("∀" <>ˢ (name (getPat bnd) <>ˢ (". " <>ˢ b'))))
pp' (TArr l r) = atLevel 1
  (atLevel 2 (pp' l) >>=P λ l' → pp' r >>=P λ r' →
   returnP (l' <>ˢ (" -> " <>ˢ r')))
pp' (Abs ty bnd) = atLevel 0
  (pushName (name (getPat bnd)) (pp' (getBody bnd)) >>=P λ b' →
   returnP ("λ" <>ˢ (name (getPat bnd) <>ˢ (". " <>ˢ b'))))
pp' (App l r) = atLevel 2
  (pp' l >>=P λ l' → atLevel 3 (pp' r) >>=P λ r' →
   returnP (l' <>ˢ (" " <>ˢ r')))
pp' (TAbs bnd) = atLevel 0
  (pushName (name (getPat bnd)) (pp' (getBody bnd)) >>=P λ b' →
   returnP ("Λ" <>ˢ (name (getPat bnd) <>ˢ (". " <>ˢ b'))))
pp' (TApp l r) = atLevel 2
  (pp' l >>=P λ l' → setLevel 0 (pp' r) >>=P λ r' →
   returnP (l' <>ˢ (" [" <>ˢ (r' <>ˢ "]"))))

pp : ∀ {@0 n} → Vec LocalName n → Exp n → String
pp s e = runScopedReader (pp' e) (mkPpEnv (map name s) 0)

------------------------------------------------------------------------
-- * Examples
------------------------------------------------------------------------

nX : LocalName
nX = mkLocalName "X"

nY : LocalName
nY = mkLocalName "Y"

nx : LocalName
nx = mkLocalName "x"

nf : LocalName
nf = mkLocalName "f"

-- ΛX. λx:X. x
t0 : Exp Z
t0 = TAbs (bind nX (Abs (Var f0) (bind nx (Var f0))))

-- ΛX. λf:(∀Y. Y → Y). λx:X. (f [X]) x
t1 : Exp Z
t1 = TAbs (bind nX
       (Abs (TAll (bind nY (TArr (Var f0) (Var f0))))
         (bind nf
           (Abs (Var f1)
             (bind nx (App (TApp (Var f1) (Var f2)) (Var f0)))))))

-- λX:Kind. λx:X. x   -- a term-level abstraction over a type
t2 : Exp Z
t2 = Abs Kind (bind nX (Abs (Var f0) (bind nx (Var f0))))
