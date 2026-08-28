{-# OPTIONS --erasure #-}

-- | The same language as "Pat", but in Haskell its `Subst`, `FV` and
-- `Strengthen` instances are all derived through @GHC.Generics@ from a
-- one-line `isVar` definition.  That is the entire point of the file.
--
-- AGDA: there is no comparable deriving mechanism, so every one of those
-- traversals has to be written out.  This port is therefore "Pat.agda
-- plus the two traversals that Haskell got for free" -- which is the
-- honest measure of what generic programming buys.
--
-- Agda transcription of @rebound/examples/PatGen.hs@.
module PatGen where

open import Rebound
open import Rebound.Bind.PatN using (Bind1; bind1; getBody1; instantiate1; applyBind1)
open import Data.Scoped.List  using (List; Nil; _:<_)
import Rebound.Bind.Pat as BindPat
import Data.Scoped.List  as L

------------------------------------------------------------------------
-- * Syntax
------------------------------------------------------------------------

data Exp    : @0 Nat → Set
data Branch (pat : @0 Nat → Set) : @0 Nat → Set

-- | Patterns.  @m@ is the number of variables the pattern binds.
data Pat     : @0 Nat → Set
data ConApp  : @0 Nat → Set
data PairPat : @0 Nat → Set

patSize     : ∀ {@0 m} → Pat m     → Singleton m
conAppSize  : ∀ {@0 m} → ConApp m  → Singleton m
pairPatSize : ∀ {@0 m} → PairPat m → Singleton m

-- These are deliberately *not* declared as instances.  A `Branch` stores
-- the `Sized` dictionary it was built with, and if a global instance were
-- also in scope the two would be ambiguous candidates at every match.
sizedPat : ∀ {@0 m} → Sized (Pat m)
Sized.theSize (sizedPat {m}) = m
Sized.size     sizedPat      = patSize

sizedConApp : ∀ {@0 m} → Sized (ConApp m)
Sized.theSize (sizedConApp {m}) = m
Sized.size     sizedConApp      = conAppSize

sizedPairPat : ∀ {@0 m} → Sized (PairPat m)
Sized.theSize (sizedPairPat {m}) = m
Sized.size     sizedPairPat      = pairPatSize

data Exp where
  Var     : ∀ {@0 n} → Fin n → Exp n
  Lam     : ∀ {@0 n} → Bind1 Exp Exp n → Exp n
  App     : ∀ {@0 n} → Exp n → Exp n → Exp n
  LetPair : ∀ {@0 n} → Exp n → Branch PairPat n → Exp n
  Con     : ∀ {@0 n} → String → Exp n
  Case    : ∀ {@0 n} → Exp n → List (Branch Pat) n → Exp n

-- Haskell writes the existential as @forall m. SNatI m => ...@, and
-- needs a quantified @forall m. Sized (pat m)@ constraint plus the
-- @SizeIndex@ class (whose content is @Size (pat m) ~ m@) wherever a
-- branch is taken apart.
--
-- Agda has neither quantified constraints nor superclass equations, so
-- the constructor simply stores both: the `Sized` instance, and the
-- equation relating its size to the existential index.  The equation is
-- `@0`, so it costs nothing.
data Branch pat where
  mkBranch : ∀ {@0 m n} {{_ : Sized (pat m)}} → @0 (Size (pat m) ≡ m)
           → BindPat.Bind Exp Exp (pat m) n → Branch pat n

data Pat where
  PVar  : Pat N1                    -- binds exactly one variable
  PHead : ∀ {@0 m} → ConApp m → Pat m

data ConApp where
  PCon : String → ConApp N0         -- binds zero variables
  PApp : ∀ {@0 m1 m2} → ConApp m1 → Pat m2 → ConApp (m2 + m1)

data PairPat where
  PPVar : PairPat N1
  PPair : ∀ {@0 m1 m2} → PairPat m1 → PairPat m2 → PairPat (m2 + m1)

patSize PVar      = s1
patSize (PHead p) = conAppSize p

conAppSize (PCon s)     = s0
conAppSize (PApp p1 p2) = sPlus (patSize p2) (conAppSize p1)

pairPatSize PPVar         = s1
pairPatSize (PPair p1 p2) = sPlus (pairPatSize p2) (pairPatSize p1)

------------------------------------------------------------------------
-- * Substitution
------------------------------------------------------------------------

instance
  SubstVarExp : SubstVar Exp
  SubstVar.var SubstVarExp = Var

{-# TERMINATING #-}
applyExp    : ∀ {@0 n m} → Env Exp n m → Exp n → Exp m
applyBranch : ∀ {pat : @0 Nat → Set} {@0 n m} → Env Exp n m → Branch pat n → Branch pat m

instance
  SubstExpExp : Subst Exp Exp
  Subst.applyE SubstExpExp = applyExp

  SubstExpBranch : ∀ {pat : @0 Nat → Set} → Subst Exp (Branch pat)
  Subst.applyE SubstExpBranch = applyBranch

applyExp r (Var x)        = applyEnv r x
applyExp r (Lam b)        = Lam (applyBind1 r b)
applyExp r (App e1 e2)    = App (applyExp r e1) (applyExp r e2)
applyExp r (Con s)        = Con s
applyExp r (Case e brs)   = Case (applyExp r e) (applyE r brs)
applyExp r (LetPair e1 b) = LetPair (applyExp r e1) (applyBranch r b)

applyBranch r (mkBranch eq bnd) = mkBranch eq (applyE r bnd)

------------------------------------------------------------------------
-- * Comparing patterns
------------------------------------------------------------------------

patEqPat     : ∀ {@0 m1 m2} → Pat m1     → Pat m2     → Maybe (Erased (m1 ≡ m2))
patEqConApp  : ∀ {@0 m1 m2} → ConApp m1  → ConApp m2  → Maybe (Erased (m1 ≡ m2))
patEqPairPat : ∀ {@0 m1 m2} → PairPat m1 → PairPat m2 → Maybe (Erased (m1 ≡ m2))

patEqPat PVar       PVar       = Just [ Refl ]
patEqPat (PHead p1) (PHead p2) = patEqConApp p1 p2
patEqPat _ _ = Nothing

patEqConApp (PApp p1 p2) (PApp p1' p2') = do
  [ Refl ] ← patEqConApp p1 p1'
  [ Refl ] ← patEqPat p2 p2'
  return [ Refl ]
patEqConApp (PCon s1) (PCon s2) with eqString s1 s2
... | true  = Just [ Refl ]
... | false = Nothing
patEqConApp _ _ = Nothing

patEqPairPat (PPair p1 p2) (PPair p1' p2') = do
  [ Refl ] ← patEqPairPat p1 p1'
  [ Refl ] ← patEqPairPat p2 p2'
  return [ Refl ]
patEqPairPat PPVar PPVar = Just [ Refl ]
patEqPairPat _ _ = Nothing

------------------------------------------------------------------------
-- * Pattern matching
------------------------------------------------------------------------

ppatternMatch : ∀ {@0 p m} → PairPat p → Exp m → Maybe (Env Exp p m)
ppatternMatch PPVar e = Just (oneE e)
ppatternMatch (PPair p1 p2) (App (App (Con s) e1) e2) with eqString s "cons"
... | true  = ppatternMatch p1 e1 >>= λ env1 →
              ppatternMatch p2 e2 >>= λ env2 →
              Just (appendE (pairPatSize p2) env2 env1)
... | false = Nothing
ppatternMatch _ _ = Nothing

patternMatch    : ∀ {@0 p m} → Pat p    → Exp m → Maybe (Env Exp p m)
patternMatchApp : ∀ {@0 p m} → ConApp p → Exp m → Maybe (Env Exp p m)

patternMatch PVar     e = Just (oneE e)
patternMatch (PHead p) e = patternMatchApp p e

patternMatchApp (PApp p1 p2) (App e1 e2) =
  patternMatchApp p1 e1 >>= λ env1 →
  patternMatch    p2 e2 >>= λ env2 →
  Just (appendE (patSize p2) env2 env1)
patternMatchApp (PCon s1) (Con s2) with eqString s1 s2
... | true  = Just zeroE
... | false = Nothing
patternMatchApp _ _ = Nothing

findBranch : ∀ {@0 n} → Exp n → List (Branch Pat) n → Maybe (Exp n)
findBranch e Nil = Nothing
findBranch {n} e (mkBranch {m} eq bnd :< brs) with patternMatch (BindPat.getPat bnd) e
... | Just r  = Just (BindPat.instantiate bnd (subst (λ q → Env Exp q n) (sym eq) r))
... | Nothing = findBranch e brs

------------------------------------------------------------------------
-- * Examples
------------------------------------------------------------------------

t0 : Exp Z
t0 = Lam (bind1 (Var f0))

t1 : Exp Z
t1 = Lam (bind1 (Lam (bind1 (App (Var f1) (App (Lam (bind1 (Var f0))) (Var f0))))))

t2 : Exp Z
t2 = Lam (bind1 (Case (Var f0)
       ( mkBranch {{sizedPat}} Refl
           (BindPat.bind {pat = Pat N0} {{sizedPat}} (PHead (PCon "Nil")) (Var f0))
      :< mkBranch {{sizedPat}} Refl
           (BindPat.bind {pat = Pat N2} {{sizedPat}}
              (PHead (PApp (PApp (PCon "Cons") PVar) PVar)) (Var f0))
      :< Nil)))

t3 : Exp Z
t3 = App (App (Con "cons") (Con "a"))
         (App (App (Con "cons") (Con "b")) (Con "nil"))

pp1 : Pat N2
pp1 = PHead (PApp (PApp (PCon "C") PVar) PVar)

pp2 : Pat N2
pp2 = PHead (PApp (PApp (PCon "D") PVar) PVar)

e1 : Exp N0
e1 = App (App (Con "C") (Con "A")) (Con "B")

e2 : Exp N0
e2 = App (App (Con "D") (Con "A")) (Con "C")

t4 : Exp Z
t4 = App t2 t3

------------------------------------------------------------------------
-- * Evaluation
------------------------------------------------------------------------

-- AGDA: the Haskell calls `error "No match!"` when a `LetPair` scrutinee
-- does not match its pattern.  Agda has no `error`, so the stuck term is
-- returned instead.
{-# NON_TERMINATING #-}
eval : ∀ {@0 n} → Exp n → Exp n
eval (Var x) = Var x
eval (Lam b) = Lam b
eval (Con s) = Con s
eval {n} (App e1 e2) = apply (eval e1) (eval e2)
  where
    apply : Exp n → Exp n → Exp n
    apply (Lam b) v = eval (instantiate1 b v)
    apply t       v = App t v
eval {n} (Case e brs) = sel (eval e)
  where
    sel : Exp n → Exp n
    sel v with findBranch v brs
    ... | Just br = eval br
    ... | Nothing = Case v brs
eval {n} (LetPair e br) = sel br (eval e)
  where
    sel : Branch PairPat n → Exp n → Exp n
    sel (mkBranch eq b) v with ppatternMatch (BindPat.getPat b) v
    ... | Just r  = eval (BindPat.instantiate b (subst (λ q → Env Exp q n) (sym eq) r))
    ... | Nothing = LetPair v (mkBranch eq b)

{-# TERMINATING #-}
step : ∀ {@0 n} → Exp n → Maybe (Exp n)
step (Var x) = Nothing
step (Lam b) = Nothing
step (Con s) = Nothing
step (App (Lam b) e2) = Just (instantiate1 b e2)
step (App e1 e2) with step e1
... | Just e1' = Just (App e1' e2)
... | Nothing with step e2
...   | Just e2' = Just (App e1 e2')
...   | Nothing  = Nothing
step {n} (LetPair e (mkBranch eq b)) with ppatternMatch (BindPat.getPat b) e
... | Just r  = Just (BindPat.instantiate b (subst (λ q → Env Exp q n) (sym eq) r))
... | Nothing with step e
...   | Just e' = Just (LetPair e' (mkBranch eq b))
...   | Nothing = Nothing
step (Case e brs) with findBranch e brs
... | Just br = Just br
... | Nothing with step e
...   | Just e' = Just (Case e' brs)
...   | Nothing = Nothing

{-# NON_TERMINATING #-}
eval' : ∀ {@0 n} → Exp n → Exp n
eval' e with step e
... | Just e' = eval' e'
... | Nothing = e

{-# NON_TERMINATING #-}
nf   : ∀ {@0 n} → Exp n → Exp n
nfBr : ∀ {pat : @0 Nat → Set} {@0 n} → Branch pat n → Branch pat n

nf (Var x) = Var x
nf (Con s) = Con s
nf (Lam b) = Lam (bind1 (nf (getBody1 b)))
nf {n} (App e1 e2) = apply (nf e1)
  where
    apply : Exp n → Exp n
    apply (Lam b) = instantiate1 b (nf e2)
    apply t       = App t (nf e2)
nf {n} (Case e brs) = sel (nf e)
  where
    sel : Exp n → Exp n
    sel v with findBranch v brs
    ... | Just b  = nf b
    ... | Nothing = Case e (L.map nfBr brs)
nf {n} (LetPair e br) = sel br (nf e)
  where
    sel : Branch PairPat n → Exp n → Exp n
    sel (mkBranch eq b) v with ppatternMatch (BindPat.getPat b) v
    ... | Just r  = nf (BindPat.instantiate b (subst (λ q → Env Exp q n) (sym eq) r))
    ... | Nothing = LetPair v (nfBr (mkBranch eq b))

nfBr (mkBranch eq bnd) =
  mkBranch eq (BindPat.bind (BindPat.getPat bnd) (nf (BindPat.getBody bnd)))

------------------------------------------------------------------------
-- * Free variables  (Haskell: `instance FV Exp` -- an empty instance)
------------------------------------------------------------------------

{-# TERMINATING #-}
appearsFreeExp    : ∀ {@0 n} → Fin n → Exp n → Bool
appearsFreeBranch : ∀ {pat : @0 Nat → Set} {@0 n} → Fin n → Branch pat n → Bool

instance
  FVExp : FV Exp
  FV.appearsFree FVExp = appearsFreeExp

  FVBranch : ∀ {pat : @0 Nat → Set} → FV (Branch pat)
  FV.appearsFree FVBranch = appearsFreeBranch

appearsFreeExp x (Var y)        = eqFin x y
appearsFreeExp x (Con s)        = false
appearsFreeExp x (Lam b)        = appearsFree x b
appearsFreeExp x (App e1 e2)    = appearsFreeExp x e1 || appearsFreeExp x e2
appearsFreeExp x (LetPair e b)  = appearsFreeExp x e || appearsFreeBranch x b
appearsFreeExp {n} x (Case e brs) = appearsFreeExp x e || anyBr brs
  where
    anyBr : List (Branch Pat) n → Bool
    anyBr Nil       = false
    anyBr (b :< bs) = appearsFreeBranch x b || anyBr bs

appearsFreeBranch x (mkBranch eq b) = appearsFree x b

------------------------------------------------------------------------
-- * Strengthening  (Haskell: `instance Strengthen Exp` -- also empty)
------------------------------------------------------------------------

{-# TERMINATING #-}
strengthenExp    : ∀ {@0 n} (k m : Nat) → Exp (k + (m + n)) → Maybe (Exp (k + n))
strengthenBranch : ∀ {pat : @0 Nat → Set} {@0 n} (k m : Nat)
                 → Branch pat (k + (m + n)) → Maybe (Branch pat (k + n))

instance
  StrengthenExp : Strengthen Exp
  Strengthen.strengthenRec StrengthenExp = strengthenExp

  StrengthenBranch : ∀ {pat : @0 Nat → Set} → Strengthen (Branch pat)
  Strengthen.strengthenRec StrengthenBranch = strengthenBranch

strengthenExp k m (Var x) = Var <$> strengthenRecFin k m x
  where open import Data.Fin using (strengthenRecFin)
strengthenExp k m (Con s) = Just (Con s)
strengthenExp k m (Lam b) = Lam <$> strengthenBind1 k m b
  where open import Rebound.Bind.PatN using (strengthenBind1)
strengthenExp k m (App e1 e2) =
  strengthenExp k m e1 >>= λ e1' → strengthenExp k m e2 >>= λ e2' → Just (App e1' e2')
strengthenExp k m (LetPair e b) =
  strengthenExp k m e >>= λ e' → strengthenBranch k m b >>= λ b' → Just (LetPair e' b')
strengthenExp {n} k m (Case e brs) =
  strengthenExp k m e >>= λ e' → strBrs brs >>= λ brs' → Just (Case e' brs')
  where
    strBrs : List (Branch Pat) (k + (m + n)) → Maybe (List (Branch Pat) (k + n))
    strBrs Nil       = Just Nil
    strBrs (b :< bs) =
      strengthenBranch k m b >>= λ b' → strBrs bs >>= λ bs' → Just (b' :< bs')

strengthenBranch k m (mkBranch eq b) = mkBranch eq <$> strengthenBind k m b
  where open import Rebound.Bind.Pat using (strengthenBind)
