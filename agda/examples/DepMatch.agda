{-# OPTIONS --erasure #-}

-- | A dependent type system, with nested dependent pattern matching for
-- Sigma types.  This is an advanced usage of the binding library,
-- demonstrating the use of scoped patterns.  It doesn't correspond to
-- any current system, but has its own elegance.
--
-- Agda transcription of @rebound/examples/DepMatch.hs@.
module DepMatch where

-- The checker below runs in an error monad, so `do` is reserved for it;
-- Maybe's bind is imported under a different name.
open import Rebound hiding (_>>=_; _>>_; return)
open import Data.Prelude using () renaming (_>>=_ to _?>=_)
open import Rebound.Context
open import Rebound.Bind.PatN   using (Bind1; bind1; getBody1; instantiate1)
open import Rebound.Bind.Scoped using (ScopedSized; ScopedSize; scopedSize)
open import Data.Scoped.List    using (List; Nil; _:<_)
import Rebound.Bind.Scoped as Scoped
import Rebound.Bind.Pat    as BindPat
import Data.Scoped.List   as L

------------------------------------------------------------------------
-- * Syntax
------------------------------------------------------------------------

-- In this system, `Match` introduces a Pi type and generalizes
-- dependent functions.  If the pattern is a single variable, or an
-- annotated variable, then the `Match` term is just a normal lambda
-- expression.  But the pattern could be more structured than that,
-- supporting a general form of pattern matching.  In this language the
-- only type that supports pattern matching is a Sigma type, so every
-- match expression should have a single branch -- but for generality we
-- pretend that more are possible.

data Exp    : @0 Nat → Set
data Branch : @0 Nat → Set

-- | Patterns, which may include embedded type annotations.
-- @p@ is the number of variables bound by the pattern, @n@ the number of
-- free variables in its type annotations.
data Pat : @0 Nat → @0 Nat → Set

-- The size of a pattern does not depend on the scope, which is exactly
-- what `ScopedSized` demands.
patSize : ∀ {@0 p n} → Pat p n → Singleton p

instance
  ScopedSizedPat : ∀ {@0 p} → ScopedSized (Pat p)
  ScopedSized.theScopedSize (ScopedSizedPat {p}) = p
  ScopedSized.sizeOf         ScopedSizedPat      = patSize

data Exp where
  Star  : ∀ {@0 n} → Exp n
  Pi    : ∀ {@0 n} → Exp n → Bind1 Exp Exp n → Exp n
  Var   : ∀ {@0 n} → Fin n → Exp n
  Match : ∀ {@0 n} → List Branch n → Exp n          -- case lambda
  App   : ∀ {@0 n} → Exp n → Exp n → Exp n
  Sigma : ∀ {@0 n} → Exp n → Bind1 Exp Exp n → Exp n
  Pair  : ∀ {@0 n} → Exp n → Exp n → Exp n
  Annot : ∀ {@0 n} → Exp n → Exp n → Exp n

-- | A single branch in a match expression.  The number of variables the
-- pattern binds is existential.
data Branch where
  mkBranch : ∀ {@0 p n} → Scoped.Bind Exp Exp (Pat p) n → Branch n

data Pat where
  PVar   : ∀ {@0 n} → Pat N1 n
  -- Patterns are "telescopic": in a pair pattern we increase the scope
  -- so that variables bound in the left subterm can be referred to in
  -- the right subterm.
  PPair  : ∀ {@0 p1 p2 n} → Pat p1 n → Pat p2 (p1 + n) → Pat (p2 + p1) n
  -- Patterns can also include type annotations.
  PAnnot : ∀ {@0 p n} → Pat p n → Exp n → Pat p n

patSize PVar          = s1
patSize (PPair p1 p2) = sPlus (patSize p2) (patSize p1)
patSize (PAnnot p _)  = patSize p

------------------------------------------------------------------------
-- * Substitution
------------------------------------------------------------------------

instance
  SubstVarExp : SubstVar Exp
  SubstVar.var SubstVarExp = Var

-- AGDA: mutually recursive with the `Subst` instances the library
-- resolves, so termination is asserted -- as in Talk 3.
{-# TERMINATING #-}
applyExp    : ∀ {@0 n m} → Env Exp n m → Exp n → Exp m
applyPat    : ∀ {@0 p n m} → Env Exp n m → Pat p n → Pat p m
applyBranch : ∀ {@0 n m} → Env Exp n m → Branch n → Branch m
applyBind1  : ∀ {@0 n m} → Env Exp n m → Bind1 Exp Exp n → Bind1 Exp Exp m

instance
  SubstExpExp : Subst Exp Exp
  Subst.applyE SubstExpExp = applyExp

  -- This definition cannot be generic because Pat is a GADT.
  SubstExpPat : ∀ {@0 p} → Subst Exp (Pat p)
  Subst.applyE SubstExpPat = applyPat

  -- Nor this one, because of the existential in Branch.
  SubstExpBranch : Subst Exp Branch
  Subst.applyE SubstExpBranch = applyBranch

-- `Bind1 Exp Exp` is a partial application of a definition, so instance
-- search cannot see the `Pat.Bind` head; name the instance explicitly.
applyBind1 = Subst.applyE BindPat.SubstBind

applyExp r Star        = Star
applyExp r (Pi a b)    = Pi (applyExp r a) (applyBind1 r b)
applyExp r (Var x)     = applyEnv r x
applyExp r (Match brs) = Match (applyE r brs)
applyExp r (App a b)   = App (applyExp r a) (applyExp r b)
applyExp r (Sigma a b) = Sigma (applyExp r a) (applyBind1 r b)
applyExp r (Pair a b)  = Pair (applyExp r a) (applyExp r b)
applyExp r (Annot a t) = Annot (applyExp r a) (applyExp r t)

applyPat r PVar         = PVar
-- account for the new pattern variables bound by p1 when substituting p2
applyPat r (PPair p1 p2) = PPair (applyPat r p1) (applyPat (upN (patSize p1) r) p2)
applyPat r (PAnnot p t)  = PAnnot (applyPat r p) (applyExp r t)

applyBranch r (mkBranch b) = mkBranch (applyE r b)

-- | Shift by an amount recovered from a pattern.
shiftBy : ∀ {c : @0 Nat → Set} {{_ : Subst Exp c}} {@0 k n}
        → Singleton k → c n → c (k + n)
shiftBy ⟨ k , Refl ⟩ t = applyE (shiftNE k) t

------------------------------------------------------------------------
-- * Pattern matching
------------------------------------------------------------------------

-- | Compare a pattern with an expression, potentially producing a
-- substitution for all of the variables bound in the pattern.
--
-- AGDA: the recursive call in the PPair case is on a substituted
-- pattern, not a subterm, so termination is asserted.
{-# TERMINATING #-}
patternMatch : ∀ {@0 p n} → Pat p n → Exp n → Maybe (Env Exp p n)
patternMatch PVar e = Just (oneE e)
patternMatch (PPair p1 p2) (Pair e1 e2) =
  patternMatch p1 e1 ?>= λ env1 →
  -- NOTE: substitute into p2 with env1 before pattern matching
  patternMatch (applyE (appendE (patSize p1) env1 idE) p2) e2 ?>= λ env2 →
  Just (appendE (patSize p2) env2 env1)
-- ignore type annotations when pattern matching
patternMatch (PAnnot p _) e = patternMatch p e
patternMatch p (Annot e _)  = patternMatch p e
patternMatch _ _            = Nothing

findBranch : ∀ {@0 n} → Exp n → List Branch n → Maybe (Exp n)
findBranch e Nil = Nothing
findBranch e (mkBranch bnd :< brs) with patternMatch (Scoped.getPat bnd) e
... | Just r  = Just (Scoped.instantiate bnd r)
... | Nothing = findBranch e brs

------------------------------------------------------------------------
-- * Examples
------------------------------------------------------------------------

star : ∀ {@0 n} → Exp n
star = Star

-- | This definition supports telescopes: variables bound earlier in the
-- pattern can appear later.  For example, the pattern for a type paired
-- with a term of that type looks like @(x, (y : x))@.
pat0 : Pat N2 N0
pat0 = PPair PVar (PAnnot PVar (Var f0))

-- | The type of that pattern: @Sigma x:Star. x@
ty0 : Exp Z
ty0 = Sigma Star (bind1 (Var f0))

-- | A term that matches @(x, (y : x))@ and has type @Sigma x:*. x@
tm0 : Exp Z
tm0 = Pair Star ty0

-- No annotation on the binder
lam : ∀ {@0 n} → Exp (S n) → Exp n
lam b = Match (mkBranch (Scoped.bind PVar b) :< Nil)

-- Annotation on the binder
alam : ∀ {@0 n} → Exp n → Exp (S n) → Exp n
alam t b = Match (mkBranch (Scoped.bind (PAnnot PVar t) b) :< Nil)

-- | The identity function @λx. x@, i.e. @λ. 0@
t0 : Exp Z
t0 = lam (Var f0)

-- | A larger term @λ. λ. 1 (λ. 0 0)@
t1 : Exp Z
t1 = lam (lam (App (Var f1) (lam (App (Var f0) (Var f0)))))

-- Polymorphic identity function and its type
tyid : ∀ {@0 n} → Exp n
tyid = Pi star (bind1 (Pi (Var f0) (bind1 (Var f1))))

tmid : ∀ {@0 n} → Exp n
tmid = lam (lam (Var f0))

sigmaExample : Exp (S Z)
sigmaExample = Sigma star (bind1 (Sigma (Var f1) (bind1 (Var f1))))

tyEx : Exp Z
tyEx = Pi star (bind1 (Pi sigmaExample (bind1 (Var f1))))

tmEx : Exp Z
tmEx = Match (mkBranch (Scoped.bind PVar
         (Match (mkBranch (Scoped.bind (PPair PVar (PPair PVar PVar))
                   (Var f1)) :< Nil))) :< Nil)

------------------------------------------------------------------------
-- * Evaluation
------------------------------------------------------------------------

{-# NON_TERMINATING #-}
eval : ∀ {@0 n} → Exp n → Exp n
eval (Var x)     = Var x
eval (Match b)   = Match b
eval (App e1 e2) with eval e1
... | Match b with findBranch (eval e2) b
...   | Just e  = eval e
...   | Nothing = App (Match b) (eval e2)   -- pattern match failure
eval (App e1 e2) | t = App t (eval e2)
eval Star        = Star
eval (Pi a b)    = Pi a b
eval (Sigma a b) = Sigma a b
eval (Annot a t) = eval a
eval (Pair a b)  = Pair a b

-- small-step evaluation
{-# NON_TERMINATING #-}
step : ∀ {@0 n} → Exp n → Maybe (Exp n)
step (Var x)            = Nothing
step (Match b)          = Nothing
step (App (Match bs) e2) with findBranch e2 bs
... | Just r  = Just r
... | Nothing = Nothing
step (App e1 e2) with step e1
... | Just e1' = Just (App e1' e2)
... | Nothing with step e2
...   | Just e2' = Just (App e1 e2')
...   | Nothing  = Nothing
step Star        = Nothing
step (Pi a b)    = Nothing
step (Sigma a b) = Nothing
step (Pair a b)  = Nothing
step (Annot a t) = step a

-- | Find the head form.
{-# NON_TERMINATING #-}
whnf : ∀ {@0 n} → Exp n → Exp n
whnf (App a1 a2) with whnf a1
... | Match bs with findBranch (eval a2) bs
...   | Just b  = whnf b
...   | Nothing = App (Match bs) a2
whnf (App a1 a2) | t = App t a2
whnf (Annot a t) = whnf a
whnf a           = a

------------------------------------------------------------------------
-- * Type checking
------------------------------------------------------------------------

data Err : Set where
  NotEqual            : ∀ {@0 n} → Exp n → Exp n → Err
  PiExpected          : ∀ {@0 n} → Exp n → Err
  SigmaExpected       : ∀ {@0 n} → Exp n → Err
  PatternMismatch     : ∀ {@0 p1 n1 p2 n2} → Pat p1 n1 → Pat p2 n2 → Err
  AnnotationNeeded    : ∀ {@0 n} → Exp n → Err
  AnnotationNeededPat : ∀ {@0 p n} → Pat p n → Err

data Result (A : Set) : Set where
  ok  : A → Result A
  err : Err → Result A

infixl 1 _>>=_ _>>_
_>>=_ : {A B : Set} → Result A → (A → Result B) → Result B
ok x  >>= f = f x
err e >>= _ = err e

_>>_ : {A B : Set} → Result A → Result B → Result B
m >> k = m >>= λ _ → k

return : {A : Set} → A → Result A
return = ok

throwError : {A : Set} → Err → Result A
throwError = err

{-# NON_TERMINATING #-}
equate         : ∀ {@0 n} → Exp n → Exp n → Result ⊤
equateWHNF     : ∀ {@0 n} → Exp n → Exp n → Result ⊤
equatePat      : ∀ {@0 p1 p2 n} → Pat p1 n → Pat p2 n → Result ⊤
equateBranch   : ∀ {@0 n} → Branch n → Branch n → Result ⊤
equateBranches : ∀ {@0 n} → List Branch n → List Branch n → Result ⊤

equate t1 t2 = equateWHNF (whnf t1) (whnf t2)

equatePat PVar PVar = return tt
equatePat (PPair p1 p1') (PPair p2 p2') with testEquality (patSize p1) (patSize p2)
... | Just [ Refl ] = equatePat p1 p2 >> equatePat p1' p2'
... | Nothing       = throwError (PatternMismatch p1 p2)
equatePat (PAnnot p1 e1) (PAnnot p2 e2) = equatePat p1 p2 >> equate e1 e2
equatePat p1 p2 = throwError (PatternMismatch p1 p2)

equateWHNF Star Star = return tt
equateWHNF (Var x) (Var y) with eqFin x y
... | true  = return tt
... | false = throwError (NotEqual (Var x) (Var y))
equateWHNF (App a1 a2) (App b1 b2) = equateWHNF a1 b1 >> equate a2 b2
equateWHNF (Pi tyA1 b1) (Pi tyA2 b2) =
  equate tyA1 tyA2 >> equate (getBody1 b1) (getBody1 b2)
equateWHNF (Sigma tyA1 b1) (Sigma tyA2 b2) =
  equate tyA1 tyA2 >> equate (getBody1 b1) (getBody1 b2)
equateWHNF (Match b1) (Match b2) = equateBranches b1 b2
equateWHNF n1 n2 = throwError (NotEqual n1 n2)

equateBranch (mkBranch b1) (mkBranch b2)
  with testEquality (patSize (Scoped.getPat b1)) (patSize (Scoped.getPat b2))
... | Just [ Refl ] = equatePat (Scoped.getPat b1) (Scoped.getPat b2)
                   >> equate (Scoped.getBody b1) (Scoped.getBody b2)
... | Nothing = throwError (PatternMismatch (Scoped.getPat b1) (Scoped.getPat b2))

equateBranches Nil         Nil         = return tt
equateBranches (b1 :< bs1) (b2 :< bs2) = equateBranch b1 b2 >> equateBranches bs1 bs2
equateBranches _           _           = return tt

{-# NON_TERMINATING #-}
inferType    : ∀ {@0 n} → Ctx Exp n → Exp n → Result (Exp n)
checkType    : ∀ {@0 n} → Ctx Exp n → Exp n → Exp n → Result ⊤
checkBranch  : ∀ {@0 n} → Ctx Exp n → Exp n → Branch n → Result ⊤
checkBranches : ∀ {@0 n} → Ctx Exp n → Exp n → List Branch n → Result ⊤
checkPattern : ∀ {@0 p n} → Ctx Exp n → Pat p n → Exp n
             → Result (Ctx Exp (p + n) × Exp (p + n))
inferPattern : ∀ {@0 p n} → Ctx Exp n → Pat p n
             → Result (Ctx Exp (p + n) × Exp (p + n) × Exp n)
inferApp     : ∀ {@0 n} → Ctx Exp n → Exp n → Exp n → Result (Exp n)
checkPair    : ∀ {@0 n} → Ctx Exp n → Exp n → Exp n → Exp n → Result ⊤

inferPattern g (PAnnot p ty) = do
  r ← checkPattern g p ty
  return (fst r , snd r , ty)
inferPattern g p = throwError (AnnotationNeededPat p)

-- | Type check a pattern and produce an extended typing context, plus
-- the expression form of the pattern (for dependent pattern matching).
checkPattern g PVar a = return (g +++ a , var f0)
checkPattern {n = n} g (PPair {p1 = p1} {p2 = p2} q1 q2) (Sigma tyA tyB) = do
  r1 ← checkPattern g q1 tyA
  let g'   = fst r1
      e1   = snd r1
      tyB' = whnf (instantiate1 (shiftBy (patSize q1) tyB) e1)
  r2 ← checkPattern g' q2 tyB'
  -- need to know that + is associative
  return (subst (λ q → Ctx Exp q × Exp q) (axiomAssoc {p2} {p1} {n})
                (fst r2 , Pair (shiftBy (patSize q2) e1) (snd r2)))
checkPattern g p ty = do
  r ← inferPattern g p
  equate ty (snd (snd r))
  return (fst r , fst (snd r))

--      G |- p : A => G'      G' |- b : B { p / x}
--   ----------------------------------------------
--       G |- p => b : Pi x : A . B
checkBranch g (Pi tyA tyB) (mkBranch bnd) = do
  let pat  = Scoped.getPat bnd
      body = Scoped.getBody bnd
  r ← checkPattern g pat tyA
  -- shift tyB into the scope of the pattern and instantiate it with the
  -- pattern's expression form; simultaneously, because it is from a
  -- larger scope
  let tyB' = applyE (Scoped.instantiateWeakenEnv (patSize pat) (snd r))
                    (getBody1 tyB)
  checkType (fst r) body tyB'
checkBranch g t e = throwError (PiExpected t)

checkBranches g ty Nil       = return tt
checkBranches g ty (b :< bs) = checkBranch g ty b >> checkBranches g ty bs

checkType g (Pair a b) ty = do
  tyA ← inferType g a
  tyB ← inferType g b
  checkPair g a b ty
checkType g (Match bs) ty  = checkBranches g ty bs
checkType g e t1 = do
  t2 ← inferType g e
  equate (whnf t2) t1

inferType g (Var x) = return (applyEnv g x)
inferType g Star    = return star
inferType g (Pi a b) = do
  checkType g a star
  checkType (g +++ a) (getBody1 b) star
  return star
inferType g (Sigma a b) = do
  checkType g a star
  checkType (g +++ a) (getBody1 b) star
  return star
inferType g (App a b) = do
  tyA ← inferType g a
  inferApp g b (whnf tyA)
inferType g a = throwError (AnnotationNeeded a)

inferApp g b (Pi tyA1 tyB1) = do
  checkType g b tyA1
  return (instantiate1 tyB1 b)
inferApp g b t = throwError (PiExpected t)

checkPair g a b (Sigma tyA tyB) = do
  checkType g a tyA
  checkType g b (instantiate1 tyB a)
checkPair g a b ty = throwError (SigmaExpected ty)

