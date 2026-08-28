{-# OPTIONS --erasure #-}

------------------------------------------------------------------------
--  Part III: Using the rebound library, and reflections
--
--  Agda transcription of Talks.Hs26.Talk3.  See the "AGDA:" notes for
--  the places where the two languages part company.
--
--  Scopes, and the number of variables a pattern binds, are marked "@0":
--  erased before execution, exactly as in GHC.  Watch what that costs --
--  it is the reason `Sized` below looks like Haskell's class rather than
--  like a single number.
------------------------------------------------------------------------

module Talk3 where

-- Import rebound library
open import Rebound
open import Rebound.Bind.Pat using (bind; getBody; getPat; instantiate; SubstBind)
import Rebound.Bind.Pat as R


------------------------------------------------------------------------
-- * Challenge: Lang where # of binding vars not statically known
------------------------------------------------------------------------
{-

-- lambda calculus with unit, products, and pattern matching
e ::= x | \ x . e | e1 e2
   | () | (e1,e2) | inj1 e | inj2 e
   | case e of { brs }

-- list of branches
brs ::=   {- empty -}  |  p -> e ; brs

-- pattern
p ::= x | () | (p1,p2) | inj1 p

-}

------------------------------------------------------------------------
-- * Syntax and binding specification
------------------------------------------------------------------------

data Pat        : @0 Nat → Set
data Tm         : @0 Nat → Set
data BranchList : @0 Nat → Set

-- A pattern binds `m` variables.  Because `m` is erased we cannot just
-- hand it over: we have to walk the pattern to recover it, and return a
-- `Singleton m` -- a runtime number paired with an erased proof that it
-- is the `m` in the type -- so the walk is known to give the right
-- answer.
--
-- This is Haskell's instance, line for line:
--
--     instance Sized (Pat m) where
--       type Size (Pat m)  = m
--       size PVar          = s1
--       size PUnit         = s0
--       size (PPair p1 p2) = sPlus (size p2) (size p1)
--       size (PInj _ p)    = size p
--
-- with `Singleton` where Haskell writes `SNat`.  The return type is what
-- makes `size` trustworthy in both languages -- there is no separate
-- correctness lemma to prove.  The difference is that Haskell needs a
-- purpose-built singleton datatype (and a class, and a `withSNat`) for
-- every index type; `Singleton` is one generic record.
sizePat : ∀ {@0 m} → Pat m → Singleton m

instance
  SizedPat : ∀ {@0 m} → Sized (Pat m)
  SizedPat {m} = record { theSize = m ; size = sizePat }

-- rebound exports an abstract `Bind` type
-- Binds `n` variables of type `Tm` in body of type `Tm`, using pattern `p`
Bind : (p : Set) {{_ : Sized p}} (@0 n : Nat) → Set
Bind p n = R.Bind Tm Tm p n

data Tm where
  Var   : ∀ {@0 n} → Fin n → Tm n                    -- x
  Lam   : ∀ {@0 n} → Bind (Singleton N1) n → Tm n    -- \x. e
  App   : ∀ {@0 n} → Tm n → Tm n → Tm n              -- e1 e2
  Unit  : ∀ {@0 n} → Tm n                            -- ()
  Pair  : ∀ {@0 n} → Tm n → Tm n → Tm n              -- (e1, e2)
  Inj   : ∀ {@0 n} → Nat → Tm n → Tm n               -- inj1 e / inj2 e
  Match : ∀ {@0 n} → Tm n → BranchList n → Tm n      -- case e of { brs }

-- A list of pattern bindings of m variables, in scope n
-- Bind (Pat m) n contains a pattern (Pat m) and body (Tm (m + n))
data BranchList where
  BNil  : ∀ {@0 n} → BranchList n
  BCons : ∀ {@0 m n} → Bind (Pat m) n → BranchList n → BranchList n

-- A pattern: m is the number of variables *bound* by the pattern
data Pat where
  PVar  : Pat N1                                         -- x
  PUnit : Pat N0                                         -- ()
  PPair : ∀ {@0 m1 m2} → Pat m1 → Pat m2 → Pat (m2 + m1) -- (p1, p2)
  PInj  : ∀ {@0 m} → Nat → Pat m → Pat m                 -- inj1 p / inj2 p

sizePat PVar          = s1
sizePat PUnit         = s0
sizePat (PPair p1 p2) = sPlus (sizePat p2) (sizePat p1)
sizePat (PInj _ p)    = sizePat p


-----------------------------------------------------------------
-- API operations for Bind
-----------------------------------------------------------------

-- bind        : pat → c (Size pat + n) → Bind v c pat n
-- getPat      : Bind v c pat n → pat
-- getBody     : Bind v c pat n → c (Size pat + n)
-- instantiate : Bind v c pat n → Env v (Size pat) n → c n

-- Any type that is used as a pattern *must* be an instance of the
-- `Sized` type class, so that the library can determine the number of
-- binding variables.

-- (`instantiate1` needs the `Subst` instances, so Agda makes us define
-- it further down.)
--
--     instantiate1 : Bind (Singleton N1) n → Tm n → Tm n
--     instantiate1 b t = instantiate b (t ∷ zeroE)


--------------------------------------------------------------------
-- Counting bound variables
--------------------------------------------------------------------

-- `sizePat` above is the only definition of a pattern's size, and no
-- lemma relates it to the index, because its type
--
--     sizePat : Pat m -> Singleton m
--
-- already is the correctness statement.  That is the shape Haskell is
-- forced into, and it is a good shape -- the talk's point that internal
-- verification "avoids equational reasoning" applies here verbatim.


--------------------------------------------------------------------
-- * Environments
--------------------------------------------------------------------

-- Rebound exports an environment type:  `Env v m n`
-- where
--     applyEnv : Env v m n → Fin m → v n
--
--     zeroE : Env v Z n
--     _∷_   : v n → Env v m n → Env v (S m) n
--     idE   : Env v n n
--     up    : Env v m n → Env v (S m) (S n)
--
-- and, since the scopes are erased, an append that needs the length of
-- its first argument at runtime:
--
--     appendE : Singleton p → Env v p n → Env v m n → Env v (p + m) n
--     _++_    : {{Singleton p}} → Env v p n → Env v m n → Env v (p + m) n
--
-- Some operations need to identify the "Var" constructor:

instance
  SubstVarTm : SubstVar Tm
  SubstVar.var SubstVarTm = Var


--------------------------------------------------------------------
-- * Substitution
--------------------------------------------------------------------

-- applyE is a member of the two-parameter class "Subst v c"
--   v - type in RHS of environment
--   c - type that we are substituting into
--
--     applyE : Env v n m → c n → c m

-- AGDA: unlike Parts I and II, this one is asserted, and the assertion
-- is not an artifact of the checker.
--
-- In Parts I and II the cycle was avoidable: `applyE` only ever called
-- itself on stored terms in order to *weaken* them, and weakening is a
-- renaming, so pulling it out into its own traversal cut the knot.
--
-- Here the cycle runs through composition of delayed substitutions:
--
--     applyTm r (Lam b)                       -- b : Bind Tm Tm _ n
--       = Lam (applyE r b)                    -- Rebound.Bind.Pat
--       = Lam (mkBind p (env2 >>> r) body)    -- composes environments
--
--     comp (Cons k x xs) s2                   -- Rebound.Env
--       = Cons 0 (applyE (comp (Inc k) s2) x) ...
--                 ^^^^^^ substitutes into a term stored in the env
--
-- Composition genuinely has to substitute, and the term it substitutes
-- into is not a subterm of anything we are recursing on.  The pair does
-- terminate -- environments and terms are all finite -- but by a nested
-- measure, and proving it is essentially strong normalization for the
-- sigma-calculus, not a matter of rearranging the definitions.
--
-- `Rebound.Env.comp` carries the same assertion, and for the same
-- reason; the two are really one assumption counted twice.
{-# TERMINATING #-}
applyTm  : ∀ {@0 n m} → Env Tm n m → Tm n → Tm m
applyBrs : ∀ {@0 n m} → Env Tm n m → BranchList n → BranchList m

instance
  SubstTmTm : Subst Tm Tm
  Subst.applyE SubstTmTm = applyTm

  SubstTmBrs : Subst Tm BranchList
  Subst.applyE SubstTmBrs = applyBrs

applyTm r (Var x)       = applyEnv r x
applyTm r (App e1 e2)   = App (applyTm r e1) (applyTm r e2)
applyTm r (Lam b)       = Lam (applyE r b)
applyTm r Unit          = Unit
applyTm r (Pair e1 e2)  = Pair (applyTm r e1) (applyTm r e2)
applyTm r (Inj i e)     = Inj i (applyTm r e)
applyTm r (Match e brs) = Match (applyTm r e) (applyBrs r brs)

applyBrs r (BCons b brs) = BCons (applyE r b) (applyBrs r brs)
applyBrs r BNil          = BNil

-- Note that the `Lam`/`BCons` cases go through the library's `Subst`
-- instance for `Bind`, which only *composes* environments: no traversal
-- happens under the binder until someone asks for the body.

-- Promised above: open a single-variable binder.
instantiate1 : ∀ {@0 n} → Bind (Singleton N1) n → Tm n → Tm n
instantiate1 b t = instantiate b (t ∷ zeroE)


-----------------------------------------------------------------
-- * Why is Bind an abstract type?
-----------------------------------------------------------------

-- Can create instances for Subst (and other classes)
--    instance SubstVar v => Subst v (Bind v c p)

-- Simplifies other instances (see above)
-- Allows optimization: delay substitution at binders, allowing
-- fused traversals


--------------------------------------------------------------------
-- * Generic Substitution (GHC.Generics)
--------------------------------------------------------------------

-- The Haskell can replace `applyE` above with a one-line `isVar`
-- definition and let GHC.Generics write the traversal.  Agda has no
-- comparable deriving mechanism in the standard toolbox, so the
-- boilerplate above stays.


------------------------------------------------------------------------
-- * Alpha-equivalence
------------------------------------------------------------------------
-- (==) is alpha-equivalence

-- Tm is *not* a GADT in Haskell, so `deriving instance Eq (Tm n)`
-- works there.  Agda has no deriving, so we write it out.
--
-- AGDA: `getBody` applies the suspended substitution, so this is not a
-- structural recursion; assert termination.
{-# TERMINATING #-}
eqTm  : ∀ {@0 n} → Tm n → Tm n → Bool
eqBrs : ∀ {@0 n} → BranchList n → BranchList n → Bool

eqTm (Var x)       (Var y)         = eqFin x y
eqTm (Lam b1)      (Lam b2)        = eqTm (getBody b1) (getBody b2)
eqTm (App a1 b1)   (App a2 b2)     = eqTm a1 a2 && eqTm b1 b2
eqTm Unit          Unit            = true
eqTm (Pair a1 b1)  (Pair a2 b2)    = eqTm a1 a2 && eqTm b1 b2
eqTm (Inj i e1)    (Inj j e2)      = eqNat i j && eqTm e1 e2
eqTm (Match e1 b1) (Match e2 b2)   = eqTm e1 e2 && eqBrs b1 b2
eqTm _             _               = false

-- But Eq for BranchList is more challenging, due to the existential:
-- we cannot compare `b1` and `b2` with `eqTm` because their patterns
-- may bind a different number of variables.  (The Haskell talk leaves
-- the comparison commented out for exactly this reason.)
eqBrs BNil            BNil            = true
eqBrs (BCons b1 brs1) (BCons b2 brs2) = {- eqBind b1 b2 && -} eqBrs brs1 brs2
eqBrs _               _               = false


-- Compare two patterns for equality, even if we don't statically know
-- that they bind the same number of variables.
--
--     testEquality : Pat a → Pat b → Maybe (Erased (a ≡ b))
--
-- This is the operation the talk singles out as the good case for
-- proofs: the evidence falls out of a comparison we had to do anyway,
-- and costs nothing to produce or pass around.  `Erased` says exactly
-- that: whether the patterns matched is real data, the proof that they
-- bind the same number of variables is `@0`.  GHC gets the same deal --
-- it treats `Refl` as a "0-bit" value -- but cannot say so in a type.
instance
  TestEqualityPat : TestEquality Pat
  TestEquality.testEquality TestEqualityPat (PPair p1 p2) (PPair p1' p2') = do
    [ Refl ] ← testEquality p1 p1'
    [ Refl ] ← testEquality p2 p2'
    return [ Refl ]
  TestEquality.testEquality TestEqualityPat PVar      PVar  = return [ Refl ]
  TestEquality.testEquality TestEqualityPat PUnit     PUnit = return [ Refl ]
  TestEquality.testEquality TestEqualityPat (PInj i p) (PInj j p') with eqNat i j
  ... | true  = testEquality p p'
  ... | false = Nothing
  TestEquality.testEquality TestEqualityPat _ _ = Nothing


--------------------------------------------------------------------
-- Evaluator with pattern matching
--------------------------------------------------------------------

-- | Compare a pattern against a value, returning an environment binding
-- the pattern variables (if the pattern matches)
--
-- AGDA: `m` is erased, so appending the two environments needs a runtime
-- witness for the length of `env2`.  Recomputing it with `sizePat p2`
-- would walk the pattern a second time, so -- as in the Haskell -- the
-- witness is returned alongside the environment and the single walk pays
-- for both.
--
-- The only difference is at the point of use: `(.++)` takes the length
-- as a class constraint, so Haskell has to feed it back in with
--
--     withSNat m2 $ env2 .++ env1
--
-- while `appendE` takes it as an ordinary argument.
patternMatch : ∀ {@0 m} → Pat m → Tm Z → Maybe (Singleton m × Env Tm m Z)
patternMatch PVar  v     = return (s1 , oneE v)
patternMatch PUnit Unit  = return (s0 , zeroE)
patternMatch (PPair p1 p2) (Pair v1 v2) = do
  (m1 , env1) ← patternMatch p1 v1
  (m2 , env2) ← patternMatch p2 v2
  return (sPlus m2 m1 , appendE m2 env2 env1)
patternMatch (PInj i p) (Inj j v) with eqNat i j
... | true  = patternMatch p v
... | false = Nothing
patternMatch _ _ = Nothing

-- | (big-step) evaluation function
-- no scope errors, but types can fail at runtime
--
-- As in Parts I and II this evaluator really is partial, so it is marked
-- NON_TERMINATING: Agda will not unfold it while type checking, and
-- results are observed by running the program (talks/Test.agda).
{-# NON_TERMINATING #-}
eval : Tm Z → Maybe (Tm Z)

-- | Find the first branch whose pattern matches the scrutinee and
-- instantiate its body.
findBranch : Tm Z → BranchList Z → Maybe (Tm Z)

eval (Var ())
eval (Lam m)      = return (Lam m)
eval (App m n)    = eval m >>= λ where
                      (Lam b) → eval (instantiate1 b n)
                      _       → Nothing
eval Unit         = return Unit
eval (Pair e1 e2) = do
    v1 ← eval e1
    v2 ← eval e2
    return (Pair v1 v2)
eval (Inj i m) = do
    t ← eval m
    return (Inj i t)
eval (Match e brs) = do
    v  ← eval e
    br ← findBranch v brs
    eval br

findBranch _ BNil = Nothing
findBranch v (BCons b rest) with patternMatch (getPat b) v
... | Just (_ , r) = return (instantiate b r)
... | Nothing      = findBranch v rest


--------------------------------------------------------------------
-- * A worked example
--------------------------------------------------------------------

-- case (inj1 ((), ())) of { inj1 (x, y) -> y ; ... }
ex : Tm Z
ex = Match (Inj 1 (Pair Unit Unit))
           (BCons (bind (PInj 1 (PPair PVar PVar)) (Var f0)) BNil)

-- >>> eval ex
_ : Maybe (Tm Z)
_ = eval ex


--------------------------------------------------------------------
-- * What works for in Haskell?
--------------------------------------------------------------------

--   Erasure is the default
--      - Agda can use @0 annotations, but erasure must be requested
--      - Haskell is the opposite: singletons indicate non-erasure

--   Type soundness holds in presence of nontermination
--      - Weirich et al. "A specification of Dependent Haskell", ICFP 2017

--   Constraint solver automatically applies equations in types
--      - Sjoeberg & Weirich. "Programming Up-to-congruence", POPL 2015

--   Industrial-strength language features, libraries, and compiler (GHC)
--      - deriving and GHC.Generics available
--
-- AGDA: this file is the other side of each of those four.  Erasure is
-- requested here, one `@0` at a time -- which is why `Sized` needs its
-- `size` field back, and why `_++_` needs a `Singleton` witness.  The
-- evaluator below needs an explicit NON_TERMINATING pragma.  Every
-- coercion is a written-out `subst` rather than a solved constraint.
-- And `eqTm` is written by hand, because there is no `deriving`.

--------------------------------------------------------------------
-- * Conclusion: What have we learned about DTP from Haskell?
--------------------------------------------------------------------

-- Internal verification is a sweet spot
--   + (:~:) type important even in this context
--   + proofs written in this style are similar to Agda
--     (see Agda port in repository for more details)
--
-- When external verification is required, GHC has "answers"
--   + type inference supports "extensional" equality
--   + more expressive coercion language for proofs would help
--   + a combined terms and types would require a separate mechanism
--     for requesting runtime witnesses
