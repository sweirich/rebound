# Lecture 4: CPS Conversion

## Modules referenced in this lecture

- [Tutorial.Scoped.CPS](https://github.com/sweirich/rebound/blob/main/tutorial/main/src/Tutorial/Scoped/CPS.hs)


## Overview and Goals

The first three lectures built a well-scoped de Bruijn representation and discussed
some of the practical issues that occur when working with them in an
implementation. In this lecture, we see some of the payoff for
working with this sort of representation: we can work with and reason about
open code.

As an extended example, we will use a nontrivial *term-to-term
transformation*: called the continuation-passing style (CPS) conversion. CPS
is an important tool for programming language research: from a theoretical
side, it explains evaluation order and bridges between classical and
constructive logics. On the practical side, it has been used as a compiler
intermediate language and for the implementation of cooperative
multithreading. If you haven't seen it before, you should learn more about it.

For our purposes, CPS is a good case study because it changes the binding
structure of its input — each function gains an extra argument.  Therefore,
when implementing this operation, we need to work in a changing scope -- the
scope of the input term is not necessarily the same as the scope of the
output. Because we are working with de Bruijn indices, we need to be careful
what scope we are in, and the types help us with that.  At the same time, when
we go to test our implementation, to make sure that it has the desired
properties, we don't need to worry about variable names; we are naturally
working with terms up to alpha-equivalence.

---

## 1. What is CPS?

In direct style, a function returns its result to its caller implicitly.  In
*continuation-passing style* every function receives an extra argument — the
*continuation* — which represents "what to do with the result".  Instead of
returning, a function calls its continuation.

Here's a simple version of the CPS transformation, defined inductively on
terms.  We write `[[e]] k` to mean "translate `e`, passing results to
continuation `k`". An informal definition of this operation is below:

```
[[x]]          k = k x
[[λx. e]]      k = k (λx. λk'. [[e]] k')
[[e1 e2]]      k = [[e1]] (λx. [[e2]] (λy. x y k))
[[()]]         k = k ()
[[(e1, e2)]]   k = [[e1]] (λx. [[e2]] (λy. k (x,y)))
[[inj i e]]    k = [[e]] (λx. k (inj i x))
[[case e of p_i -> b_i]]  k = [[e]] (λz. case z of p_i → [[b_i]] k)
```

The top-level call typically uses the identity continuation: `cps e = [[e]] (λx. x)`.

Note that this is a call-by-value translation: the evaluation of the result of the translation
should occur in the same order as the call-by-value evaluation.

---

## 2. Implementation using `rebound` (pure lambda calculus)

Let's look at how we could translate the definition above to executable
Haskell code.  The difficult part of this translation is right there near the
top: when we translate a function, we need to introduce a new argument `k'` to
pass in the "continuation" of the function.

```
[[ \x.e ]] k = k (λx. λk'. [[e]] k')
```

That means that when we call the translation recursively, `e` might be in some
scope `S n`, because it is inside the body of a lambda expression. However,
the result is going to be in some larger scope that binds not just `x` but
also `k'`. What that means is that the *variable* case is also
challenging. Even though with names above we say `[[x]]k` produces `k x`, the
scope of the first `x` may be different from the scope of the second `x`, so
they may be different indices.

Therefore, we will parameterize our cps conversion function with an additional
argument---a substitution that talks about the scope change. If the input term
is in some scope `n` and the output scope is `m`, then we need an argument of
type `Env Tm n m` to go between the two.  Furthermore, the continuation
argument should be in the *output* scope (`m`) because it needs to be applied
to the result.

For the variable case, we apply this renaming to the variable, to get its version in the 
output scope. We can then use it to construct the application of the continuation to this 
new variable.

```
cpsExp :: Env Tm n m -> Tm n -> Tm m -> Tm m
cpsExp r (Var x) k = App k (applyEnv r x)
```

For the lambda case, we will also apply the continuation `k` to a value. 
But this value is the function of two parameters. The first parameter is the same 
one as the original function, the second is a new parameter. We then call the 
cps conversion function recursively on the body of the lambda expression, using 
this new parameter (variable 0 in the output scope) as the continuation.

```
cpsExp r (Lam b) k = App k 
    (Lam (bind1 (getLocalName b) 
      (Lam (bind1 (LocalName "k")
          (cpsExp r' (getBody b) (Var FZ))))))
    where 
        r' = up r .>> wk
```
What is the renaming for this recursive call? We need to translate this renaming 
to be used under the body of the lambda expression, with `up r`, but then we also 
need to account for the second binder for the continuation. This binder only
affects the output scope, as opposed to the first that is part of both. Therefore,
we need to shift the variables in the output, which we do by post-composing
the substitution with `wk`.

For applications, our original definition is 

```
[[e1 e2]]k = [[e1]] (λv. [[e2]] (λw. v w k))
```

Note that in this case, our output scope introduces two binders: `v` and `w`, naming 
the values of `e1` and `e2`. Because `v` is a function, we can apply it to both 
its argument `w` and the current continuation `k`.

With CPS translation, we need to create the two lambda bindings, for `v` and `w` above, and 
use them for the continuations as we translate `t1` and `t2`.  In the body of the 
second continuation `v w k`, `v` is at index 1, `w` is at index 0, and k needs to 
be shifted two steps.

```
cpsExp r (App t1 t2) k = 
    cpsExp r t1 (Lam (bind1 (LocalName "v")
      (cpsExp r' t2 (Lam (bind1 (LocalName "w")
          (App (App (Var (FS FZ)) (Var FZ)) k''))))))  
       where
         r'  = r .>> wk
         k'' = applyE (wk .>> wk) k
```

Note that this function is structurally recursive on the input. 

---

## 3. What does it mean for CPS conversion to be correct?

If we implement the cps conversion algorithm, we want to know that we did so
correctly. Intuitively, this means that when we apply this transformation to
some code, the output should produce the same result when we run it.

But what does that mean formally?  We can start with this simple statement,
which asserts that we get the same result from reducing any term and its
cps conversion:

```
prop_cps_result e = reduce e == reduce (cps e)
```

But already we have a problem. This property is not true.
```
ghci> quickCheck prop_cps_result
*** Failed! Falsified (after 1 test):  
Lam (bind1 (Var 0))
e          = (λ x. x)
cps_e      = (λ x. x) (λ x k. k x)
```

The result of evaluation after CPS translating the identity function is `(λ x k. k x)`. 
And this is not the same as `(λ x. x)`. We can fix this by only looking at the cases 
where the result of evaluation is "first-order", i.e. a value that does not contain 
a function.

This solves the issue, but we need to throw away a lot of cases.

```
ghci> qc prop_cps_result_firstorder
+++ OK, passed 1000 tests; 1373 discarded.
```

### Simulation properties

Perhaps we can restate correctness using a simulation property.
if the source language reduces a term to some result, then the CPS-converted version
evaluates the converted term to an equivalent result. 

We might draw a picture like this:

```
  if         e  =>  v 
                 
  then      cps e => cps v
```

In other words, we want to show that if `e` evaluates to `v`, then `cps e` evaluates to `cps v`.
```
prop_cps_simulates :: Property
prop_cps_simulates = forAll0 Typed Full $ \e ->
       counterexample ("e          = " ++ pp e)          $
       counterexample ("cps_e      = " ++ pp (cps e))    $
       eval (cps e) == (cps <$> eval e)
```

But, this property is not true!

```
ghci> qc prop_cps_simulates
*** Failed! Falsified (after 1 test):  
Unit
e          = ()
cps_e      = (λ x. x) ()
```
In this counterexample, we have a value that translates to a non-value. But 
reduction always produces inert terms.
The problem is that CPS translation has inserted an "administrative reduction" 
into the term.

---

## 4. Optimized CPS conversion

A naive implementation would represent every continuation `k` as a `Tm g`
(an object-level lambda) and apply it with `App k v`.  But this introduces
*administrative redexes* — beta redexes of the form `(λx. body) v` that were
not present in the source and must be reduced away.


### Introducing Meta continuations

To avoid this we distinguish two cases:

```haskell
data Cont (g :: Nat) where
    Obj  :: Tm g          -> Cont g   -- object-level term (usual)
    Meta :: Bind1 Tm Tm g -> Cont g   -- meta-level binder (new!)
```

- **`Obj t`** — the continuation is an existing object-level term `t`.  To
  apply it we emit a genuine `App`: `applyCont (Obj t) v = App t v`.

- **`Meta k`** — the continuation is represented as a Haskell-level binder.
  To apply it we substitute directly, *without* introducing a lambda in the
  output: `applyCont (Meta k) v = instantiate1 k v`.

```haskell
applyCont :: Cont g -> Tm g -> Tm g
applyCont (Obj  o) v = App o v
applyCont (Meta k) v = instantiate1 k v
```

When a `Meta` continuation must appear as an object-level term (e.g. as the
extra argument passed to a CPS'd function), we reify it:

```haskell
reifyCont :: Cont g -> Tm g
reifyCont (Obj  o) = o
reifyCont (Meta k) = Lam k
```

`Meta` continuations are used for all the intermediate continuations built
*inside* `cpsExp`; the top-level call uses `Meta (bind1 "x" (Var FZ))` (the
identity function `λx. x` as a meta-continuation).

Since `Cont g` contains `Tm g` values, it needs a `Subst` instance so that
the library can apply environments to it:

```haskell
instance Subst Tm Cont where
  applyE r (Obj o)  = Obj (applyE r o)
  applyE r (Meta b) = Meta (applyE r b)
```

### Updating the translation to use Meta continuations

To update the translation, we change the type of the continuation 
argument to be a `Cont m` instead of a raw term. 

```
cpsOpt :: forall n m. Env Tm n m -> Tm n -> Cont m -> Tm m
```

The Haskell typechecker then 
points out all of the places where we need to change uses of `App` 
to `applyCont`, and insert a use of `reifyCont` when we use 
a `Cont m` as a `Tm m`.  Whenever we construct a continuation using 
`Lam`, we have a choice: we can either wrap it with `Obj` or change 
the `Lam` to `Meta` .... but using the `Meta` continuation is more 
efficient.

At the top level, we have a new way to start the transformation. We 
can either start with the identity function, as before, or we can 
start with a meta-level identity function.

```
-- | entry point with identity function
cpsOpt :: Tm Z -> Tm Z
cpsOpt e = cpsExpOpt zeroE e (Obj idTm)

-- | entry point with meta-identity function
cpsOptM :: Tm Z -> Tm Z
cpsOptM e = cpsExpOpt zeroE e (Meta (bind (LocalName "x") (Var FZ)))
```

Now let's try our simulation property with these two: 

```
ghci> qc prop_cpsOpt_simulates
*** Failed! Falsified (after 1 test):  
()
e          = ()
eval_e     = ()
cps_e      = (\ x. x) ()
cps_eval_e = (\ x. x) ()
eval_cps_e = ()
ghci> qc prop_cpsOptM_simulates
+++ OK, passed 100000 tests.
ghci> 
```


## 5. Historical Notes

**The CPS transformation.** The idea of compiling programs into continuation-passing style has two early origins. Fischer ("Lambda Calculus Schemata", 1972; published in revised form 1993) and Plotkin ("Call-by-Name, Call-by-Value and the Lambda-Calculus", 1975) independently described the CPS translation as a way to explain evaluation order. Plotkin's paper is particularly influential: it proved that call-by-value and call-by-name evaluation correspond to two different CPS translations, and it coined the term *administrative redex* for the spurious beta-redexes introduced by a naive translation.

**CPS as a compiler intermediate language.** Steele's "Rabbit: A Compiler for Scheme" (1978) first used CPS as a compiler intermediate representation, making continuations explicit so that tail calls, closures, and control effects could all be handled uniformly. This idea was further developed in the SML/NJ compiler (Appel, "Compiling with Continuations", 1992) and influenced many subsequent compiler designs.

**One-pass CPS and administrative redexes.** A naive CPS translation produces many administrative redexes. Eliminating them requires a separate reduction pass. Danvy and Filinski ("Representing Control: A Study of the CPS Transformation", 1992) showed how to produce administrative-redex-free output in a single pass by distinguishing *meta-level* continuations (Haskell functions) from *object-level* continuations (lambda terms in the target). The `Cont` datatype with `Meta` and `Obj` constructors in Section 4 directly implements this idea. 

**CPS and classical logic.** Griffin ("A Formulae-as-Types Notion of Control", 1990) observed that continuations correspond to classical logic under the Curry–Howard correspondence: the call/cc operator corresponds to the law of excluded middle. This connection was further developed by Parigot (λμ-calculus, 1992) and many others, giving a logical foundation for the computational behavior of control operators.


---

## 6. Exercises

**1. Tracing `cpsExp` by hand.** Work through the following calls step by step, writing down the output term produced at each recursive call.  Verify your answers in GHCi using `pp (cps e)`.

**(a)** Trace `cpsExp idE Unit idTm`.
- What rule applies?
- What is the output term?

**(b)** Trace `cpsExp idE (Lam (bind1 (LocalName "x") (Var FZ))) idTm`:
- When the rule for `Lam` calls `cpsExp r' (Var FZ) (Var FZ)` recursively, what is the environment `r'`?
  - `r' = up idE .>> wk :: Env Tm (S Z) (S (S Z))`
  - What does `r'` map `FZ` to?  (Hint: `up idE` is the identity on `Tm (S Z)`, then `.>> wk` shifts.)
- What is the full output term?  Use `pp` to check your answer looks like `(λ x. x) (λ x. λ k. k x)`.

**(c)** Trace `cpsExp idE (App (Lam (bind1 (LocalName "x") (Var FZ))) Unit) idTm`.
The `App` case introduces two intermediate continuations.  Write down the complete output term and verify it matches `pp (cps (App (Lam ...) Unit))`.

---

**2. Scope arithmetic in the `App` case.**  The `App` case of `cpsExp` is:

```haskell
cpsExp r (App t1 t2) k =
    cpsExp r t1 (Lam (bind1 (LocalName "v")
      (cpsExp r' t2 (Lam (bind1 (LocalName "w")
          (App (App (Var (FS FZ)) (Var FZ)) k''))))))
    where
      r'  = r .>> wk
      k'' = applyE (wk .>> wk) k
```

Answer the following:

**(a)** If the input scope is `n` and output scope is `m`, what is the output scope when translating `t2`?  The continuation for `t2` is a lambda we are *building*, so we are one binder deeper.

**(b)** In the body `App (App (Var (FS FZ)) (Var FZ)) k''`, what do `Var (FS FZ)` and `Var FZ` name?

**(c)** Why is `k` shifted by `wk .>> wk` to produce `k''`, but `r` is only shifted by a single `wk` to produce `r'`?  (Hint: `r` maps input variables to the output scope — how many new output binders have been crossed at each point?)

---

**3. Correctness properties — what fails and why.**

**(a)** Run `qc prop_cps_result` in GHCi.  Record the counterexample.  Explain in one sentence why CPS-converting a function value does not preserve `eval`.

**(b)** Run `qc prop_cps_result_firstorder`.  This passes, but with a high discard rate.  Why are so many test cases discarded?

**(c)** Run `qc prop_cps_eval_simulates`.  The counterexample involves `Unit`.  Explain why `()` is the simplest failing case: what does `cps ()` reduce to, and why is that not equal to `cps (eval ())`?

**(d)** Run `qc prop_cps_eval_simulates_open`.  This passes for the pure lambda calculus.  The property uses `cpsK` instead of `cps`.  Explain: why does replacing the identity-function continuation with a fresh variable `k` fix the `Unit` counterexample?

**(e)** Change the generator in `prop_cps_eval_simulates_open` from `Typed PureLC` to `Typed Full` and run it.  Record the counterexample.  Which language construct causes it to fail, and why does the pure lambda calculus not have this problem?

---

**4. Meta continuations — counting administrative redexes.**

**(a)** Evaluate the following in GHCi and compare the two outputs:

```haskell
ghci> pp (cps    (App (Lam (bind1 (LocalName "x") (Var FZ))) Unit))
ghci> pp (cpsOpt (App (Lam (bind1 (LocalName "x") (Var FZ))) Unit))
```

Count the number of beta-redexes (sub-terms of the form `(λ x. body) arg`) in each.  Which version has fewer?

**(b)** For `cpsExpOpt r Unit (Meta (bind1 (LocalName "x") body))`, show that `applyCont k Unit` directly substitutes `Unit` into `body`, producing `body[Unit/x]` with no `(λ x. body) ()` redex.

**(c)** In the `Lam` case of `cpsExpOpt`, the continuation passed to the recursive call is `Obj (Var FZ)` — not `Meta`.  Explain why `Meta` cannot be used here.  (Hint: `Var FZ` is a *runtime* variable for the caller-supplied continuation `k'`, not a compile-time binder we control.)

**(d)** Run `qc prop_cpsOpt_result_firstorder` and `qc prop_cpsOpt_simulates`.  Do both pass?  What do they tell you about the correctness of the optimised translation?

---

**5. Extending `cpsExp` with `let`.**  Assume `Let :: Tm n -> Bind1 Tm Tm n -> Tm n` has been added to `Tm` (Lecture 1, Exercise 3).  The CPS rule for `let` is:

```
[[let x = e in b]] k  =  [[e]] (λx. [[b]] k)
```

**(a)** Add a case to `cpsExp`:

```haskell
cpsExp r (Let e b) k =
    cpsExp r e (Lam (bind1 (getLocalName b)
        (cpsExp r' (getBody1 b) k')))
    where
      r' = up r .>> wk
      k' = applyE wk k
```

Explain each component:
- Why is `r'` the right environment for the body of `b`?
- Why is `k` shifted by `wk` to produce `k'`?
- How does this compare to the `Lam` case?

**(b)** Add the corresponding case to `cpsExpOpt`, replacing the `Lam`-built continuation with a `Meta` continuation:

```haskell
cpsExpOpt r (Let e b) k =
    cpsExpOpt r e (Meta (bind1 (getLocalName b)
        (cpsExpOpt r' (getBody1 b) k')))
    where
      r' = up r .>> wk
      k' = applyE wk k
```

What administrative redex does the `Meta` here avoid compared to `cpsExp`?

**(c)** After adding both cases, run `qc prop_cps_result_firstorder` and verify it still passes.

**6. Properties of step and normalize*  
    
Investigate properties of CPS conversion that hold and do not hold for small-step reduction or normalization (if you did that problem from the previous lecture).
