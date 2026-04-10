-- Solutions to the exercises in Lecture 3.
-- These solutions use Tutorial.Scoped.CPS.

module Tutorial.Exercise3 where

import Tutorial.Scoped.Syntax
import Tutorial.Scoped.CPS
import Tutorial.Scoped.Gen
import Tutorial.Scoped.ScopeCheck
import Tutorial.Scoped.Eval
import Test.QuickCheck as QC
import Data.Vec hiding ((++),bind)


------------------------------------------------------------------------
-- * Exercise 1: Tracing cpsExp by hand
------------------------------------------------------------------------

-- (a) Trace cpsExp idE Unit idTm
--
-- The Unit rule fires:
--   cpsExp r Unit k = App k Unit
-- With r = idE, k = idTm:
--   App idTm Unit
-- which pretty-prints as: (\ x. x) ()

ex1a :: Tm Z
ex1a = cpsExp idE Unit idTm

-- >>> pp ex1a
-- "(\ x. x) ()"


-- (b) Trace cpsExp idE (Lam (bind1 (LocalName "x") (Var FZ))) idTm
--
-- The Lam rule fires:
--   cpsExp r (Lam b) k = App k (Lam (bind1 nm (Lam (bind1 "k" (cpsExp r' body (Var FZ))))))
--   where r' = up r .>> wk
--
-- What does r' map FZ to?
--   applyEnv r' FZ
--   = applyEnv (up idE .>> wk) FZ
--   = applyE wk (applyEnv (up idE) FZ)   -- up idE is the identity on Tm (S n)
--   = applyE wk (Var FZ)                 -- identity maps FZ to Var FZ
--   = Var (FS FZ)                        -- wk shifts all indices up by 1
--
-- So inside the body (scope S (S Z)), x is at index FS FZ and k' is at index FZ.
--
-- Recursive call: cpsExp r' (Var FZ) (Var FZ)
--   = App (Var FZ) (applyEnv r' FZ)
--   = App (Var FZ) (Var (FS FZ))
--
-- Full output:
--   App idTm (Lam "x" (Lam "k" (App (Var FZ) (Var (FS FZ)))))
-- which pretty-prints as: (\ x. x) (\ x. \ k. k x)

ex1b :: Tm Z
ex1b = cpsExp idE (Lam (bind (LocalName "x") (Var FZ))) idTm

-- >>> pp ex1b
-- "(\ x. x) (\ x. \ k. k x)"


-- (c) Trace cpsExp idE (App (Lam (bind1 (LocalName "x") (Var FZ))) Unit) idTm
--
-- The App rule fires for t1 = Lam "x" (Var FZ), t2 = Unit, k = idTm:
--   r'  = idE .>> wk = wk
--   k'' = applyE (wk .>> wk) idTm = idTm   (idTm is closed, shifts are no-ops)
--
-- Step 1 — build the outer continuation for t1:
--   cont1 = Lam "v" (cpsExp wk Unit (Lam "w" (App (App (Var (FS FZ)) (Var FZ)) idTm)))
--
-- Step 2 — translate t2 = Unit inside the "v" binder:
--   cpsExp wk Unit (Lam "w" ...) = App (Lam "w" (App (App (Var (FS FZ)) (Var FZ)) idTm)) Unit
--
-- Step 3 — translate t1 = Lam "x" (Var FZ) with continuation cont1:
--   (Lam rule) App cont1 (Lam "x" (Lam "k" (App (Var FZ) (Var (FS FZ)))))
--
-- Full output (named):
--   (\ v. (\ w. v w (\ x. x)) ()) (\ x. \ k. k x)

ex1c :: Tm Z
ex1c = cpsExp idE (App (Lam (bind (LocalName "x") (Var FZ))) Unit) idTm

-- >>> pp ex1c
-- "(\ v. (\ w. v w (\ x. x)) ()) (\ x. \ k. k x)"


------------------------------------------------------------------------
-- * Exercise 2: Scope arithmetic in the App case
------------------------------------------------------------------------
--
-- Recall the App case:
--
--   cpsExp r (App t1 t2) k =
--       cpsExp r t1 (Lam (bind1 (LocalName "v")
--         (cpsExp r' t2 (Lam (bind1 (LocalName "w")
--             (App (App (Var (FS FZ)) (Var FZ)) k''))))))
--       where
--         r'  = r .>> wk
--         k'' = applyE (wk .>> wk) k
--
-- (a) Output scope when translating t2.
--
--     If the input scope is n and the output scope is m, then translating t1
--     produces a term in scope m.  The continuation for t1 is `Lam "v" (...)`,
--     which adds one binder.  So t2 is translated in scope S m, i.e. one deeper
--     than m.
--
-- (b) What do Var (FS FZ) and Var FZ name in App (App (Var (FS FZ)) (Var FZ)) k''?
--
--     We are inside two binders introduced by the continuations:
--       - inner binder (closest): "w" = value of t2, at index FZ
--       - outer binder:           "v" = value of t1, at index FS FZ
--     So Var (FS FZ) = v (the function, value of t1)
--        Var FZ      = w (the argument, value of t2)
--     This forms the direct application:  v w k
--
-- (c) Why is k shifted by wk .>> wk but r only by wk?
--
--     r maps input variables (scope n) to the output scope.  When we start
--     translating t2, we have crossed one new output binder ("v"), so r must
--     be shifted once: r' = r .>> wk.
--
--     k lives in the original output scope m.  By the time we are in the body
--     of the "w" binder (where k'' is used), we have crossed TWO new output
--     binders ("v" and "w"), so k must be shifted twice:
--       k'' = applyE (wk .>> wk) k
--
-- (d) Why does MatchPair shift k by wk .>> wk .>> wk (three shifts)?
--
--     The MatchPair case introduces three new output binders:
--       1. The outer "v1" continuation binder (for the scrutinee).
--       2. The first pattern variable (x1) from the bind2.
--       3. The second pattern variable (x2) from the bind2.
--     k is used inside all three, so it needs three shifts.


------------------------------------------------------------------------
-- * Exercise 3: Correctness properties — what fails and why
------------------------------------------------------------------------

-- (a) prop_cps_result fails.
--
-- Counterexample: Lam (bind1 (Var 0))   i.e. λx. x
--   eval (λx. x) = Just (λx. x)
--   cps  (λx. x) = (λx.x) (λx. λk. k x)
--   eval (cps (λx. x)) = Just (λx. λk. k x)
--
-- The CPS translation of a function value is NOT the same function value:
-- it wraps it in a new lambda and adds a continuation argument.  So
-- eval (cps e) /= eval e whenever eval e is a function value.
--
-- (b) prop_cps_result_firstorder passes but discards many cases.
--
-- We discard whenever eval e produces a function value (Lam).  Typed terms
-- can have any type, including function types, so most generated terms
-- evaluate to lambdas.  Only products, sums, and Unit give first-order
-- values, and even terms of those types often reduce through intermediate
-- lambdas.
--
-- (c) prop_cps_eval_cps fails for Unit.
--
-- The property is: eval (cps e) == cps <$> eval e
-- For e = Unit:
--   eval (cps Unit) = eval ((λx.x) ()) = Just ()
--   cps <$> eval Unit = cps <$> Just () = Just (cps ()) = Just ((λx.x) ())
-- These differ: Just () /= Just ((λx.x) ())
--
-- The RHS is cps applied to the *value* (), giving a non-value (a redex).
-- CPS always wraps a value v in "k v", so cps v is never itself a value.
--
-- (d) prop_cps_eval_simulates_open passes for pure lambda calculus.
--
-- Using a fresh variable k (via cpsK / cpsOptK) instead of idTm fixes the
-- Unit problem: cpsK () = App (Var FZ) () = k ().  And cpsK (eval ()) =
-- cpsK () = k () too.  Both sides are the same opaque application, so they
-- agree without evaluation.  The fresh variable acts as an abstract
-- continuation whose behaviour we never fix.
--
-- This property uses reduce rather than eval (to handle open terms with k
-- free) and holds for PureLC because there are no pattern-matching terms to
-- cause the asymmetry described in (e).

-- Here is the property from the lecture (already in CPS.hs as
-- prop_cps_reduce_cps_pure).  We name it differently to keep Exercise3
-- self-contained.
prop_cps_eval_simulates_open :: Property
prop_cps_eval_simulates_open = forAll0 Typed PureLC $ \e ->
    let pp' = ppWith ("k" ::: VNil)
    in  counterexample ("e         = " ++ pp e) $
        counterexample ("cpsK e    = " ++ pp' (cpsK e)) $
        reduce (cpsK e) == (cpsK <$> reduce e)

-- (e) Changing the generator to Typed Full exposes pattern-matching failures.
--
-- Counterexample (representative): MatchUnit () ()
--   reduce (MatchUnit () ())  = Just ()
--   cpsK (MatchUnit () ())
--     = cpsExp zeroE (MatchUnit () ()) (Var FZ)
--     = cpsExp zeroE () (Lam "v" (MatchUnit (Var FZ) (cpsExp (zeroE .>> wk) () (Var (FS FZ)))))
--     -- roughly: (λv. case v of () -> k ()) ()
--   reduce (cpsK (MatchUnit () ())) = ...  some term T
--   cpsK <$> reduce (MatchUnit () ()) = cpsK () = App (Var FZ) ()
--
--   T /= App (Var FZ) () because the CPS of MatchUnit introduces an extra
--   lambda layer around the branch body, so reducing the translated scrutinee
--   does not immediately match the translated result.
--
--   The pure lambda calculus avoids this because it has no eliminators: every
--   value is a lambda, and the CPS of a lambda-headed application reduces
--   predictably.

prop_cps_eval_simulates_full :: Property
prop_cps_eval_simulates_full = forAll0 Typed Full $ \e ->
    let pp' = ppWith ("k" ::: VNil)
    in  counterexample ("e         = " ++ pp e) $
        counterexample ("cpsK e    = " ++ pp' (cpsK e)) $
        reduce (cpsK e) == (cpsK <$> reduce e)

-- prop_cps_eval_simulates_full is known to fail (run it in GHCi to see a
-- counterexample).


------------------------------------------------------------------------
-- * Exercise 4: Meta continuations — counting administrative redexes
------------------------------------------------------------------------

-- (a) Compare outputs for App (\ x. x) ()
--
-- >>> pp (cps    (App (Lam (bind1 (LocalName "x") (Var FZ))) Unit))
-- "(\ v. (\ w. v w (\ x. x)) ()) (\ x. \ k. k x)"
--
-- Beta-redexes in the naive output:
--   1. (\ v. ...) (\ x. \ k. k x)   — the outer continuation applied to the translated Lam
--   2. (\ w. ...) ()                 — the inner continuation applied to the translated Unit
-- Total: 2 administrative redexes.
--
-- >>> pp (cpsOpt (App (Lam (bind1 (LocalName "x") (Var FZ))) Unit))
-- "(\ x. \ k. k x) () (\ x. x)"
--
-- The meta-continuations were instantiated at translation time, so no
-- (λ x. body) arg redexes appear.  Total: 0 administrative redexes.

ex4a_naive :: Tm Z
ex4a_naive = cps (App (Lam (bind (LocalName "x") (Var FZ))) Unit)

ex4a_opt :: Tm Z
ex4a_opt = cpsOpt (App (Lam (bind (LocalName "x") (Var FZ))) Unit)

-- >>> pp ex4a_naive
-- "(\ v. (\ w. v w (\ x. x)) ()) (\ x. \ k. k x)"

-- >>> pp ex4a_opt
-- "(\ x. \ k. k x) () (\ x. x)"


-- (b) applyCont eliminates the administrative redex for Unit.
--
-- With a Meta continuation  k = Meta (bind1 "x" body):
--   applyCont k Unit = instantiate1 (bind1 "x" body) Unit = body[Unit/x]
--
-- There is no (λx. body) Unit redex in the output at all — the substitution
-- happens at translation time inside the Haskell evaluation.  With an Obj
-- continuation we would emit App (Lam (bind1 "x" body)) Unit, which is an
-- administrative redex that must be reduced later.


-- (c) Why Meta cannot be used in the Lam case.
--
-- In the Lam case the recursive call is:
--   cpsExpOpt (skip (up r)) (getBody b) (Obj (Var FZ))
--
-- The continuation here is the caller-supplied k', represented by the
-- *runtime variable* Var FZ (the second lambda parameter).  This variable
-- exists only in the output program; it is not a Haskell-level binder we
-- control at translation time.  A Meta continuation must be a Haskell
-- Bind1 we can instantiate directly.  Since Var FZ is an object-level term,
-- we must wrap it in Obj and emit a genuine App at each call site.


-- (d) Correctness of the optimised translation.
--
-- Both prop_cpsOpt_result_firstorder and prop_cpsOpt_eval_simulates_open
-- pass (they are tested in CPS.testAll).  Together they show:
--
--   • For first-order results: eval (cpsOpt e) = eval e
--     (the optimisation does not change the observable result).
--
--   • With a continuation variable: reduce (cpsOptK e) = cpsOptK <$> reduce e
--     (cpsOpt correctly simulates reduction, for all well-typed terms).
--
-- So cpsOpt is not just faster — it is provably observationally equivalent
-- to cpsExp on well-typed inputs.


------------------------------------------------------------------------
-- * Exercise 5: Extending cpsExp with let
------------------------------------------------------------------------
--
-- Assume Let :: Tm n -> Bind1 Tm Tm n -> Tm n is added to Tm.
-- The CPS rule is:
--   [[let x = e in b]] k  =  [[e]] (λx. [[b]] k)
--
-- (a) New case for cpsExp:
--
--   cpsExp r (Let e b) k =
--       cpsExp r e (Lam (bind1 (getLocalName b)
--           (cpsExp r' (getBody1 b) k')))
--       where
--         r' = up r .>> wk
--         k' = applyE wk k
--
--   Explanation of each component:
--
--   • r' = up r .>> wk
--     The body of b is in scope S n (one new variable x is bound).  We lift r
--     under the new binder with `up r`, giving an env for scope S n → S m.
--     The outer Lam continuation adds one more output binder (for x in the
--     output), so the output scope is S m.  We shift the whole thing by wk to
--     account for that extra output binder.  Same reasoning as in the Lam case.
--
--   • k' = applyE wk k
--     k lives in output scope m.  The body of b is translated inside the Lam
--     continuation binder, so the output scope is S m.  We shift k up by one
--     with wk so it refers to the same continuation in the new scope.  Unlike
--     App (which crosses two output binders before using k), let crosses only
--     one (for x), hence a single wk rather than wk .>> wk.
--
--   • Comparison to Lam:
--     In the Lam case the body is also translated under one new input binder
--     and one new output binder, with r' = up r .>> wk.  The difference is
--     that Lam introduces an *extra* output binder for k' (the continuation
--     parameter), whereas Let does not — it reuses the current k directly
--     (shifted).  Hence Lam uses (Var FZ) as the recursive continuation (the
--     k' lambda parameter) while Let shifts k and passes it through.
--
-- (b) Optimised version using Meta:
--
--   cpsExpOpt r (Let e b) k =
--       cpsExpOpt r e (Meta (bind1 (getLocalName b)
--           (cpsExpOpt r' (getBody1 b) k')))
--       where
--         r' = up r .>> wk
--         k' = applyE wk k
--
--   The Meta here avoids the administrative redex that cpsExp would introduce:
--   instead of emitting  (λx. [[b]] k') (result of e)  in the output, the
--   meta-continuation directly substitutes the result into the body at
--   translation time.
--
-- (c) prop_cps_result_firstorder continues to pass after adding these cases
--     because Let desugars into App / Lam, and the Let CPS rule mirrors that
--     desugaring exactly.


------------------------------------------------------------------------
-- * Preserved from original Exercise3: Plotkin's simulation property
------------------------------------------------------------------------

-- | If e ->* v then [[e]]k ->* [[v]]k
-- This is Plotkin's key correctness theorem for the CPS translation.
prop_plotkin :: Property
prop_plotkin = forAll (genTm Typed PureLC) $ \e ->
    let
       cps_e = cpsExp zeroE e k
       cps_v = cpsExp zeroE v k
       k = Var FZ
       vv = "k" ::: VNil
       v = case eval e of
            Nothing -> discard
            Just v1 -> v1
    in
      step_star vv cps_e cps_v
