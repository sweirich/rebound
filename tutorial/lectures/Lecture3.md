# Lecture 3: CPS Conversion

Lectures 1 and 2 built a well-scoped de Bruijn representation and discussed some of the practical
issues that occur when working with them in an implementation. In this lecture, we start to see 
some of the payoff for working with this sort of representation: we can work with and reason about 
open code. 

As an extended example, we will us a nontrivial *term-to-term transformation*: 
continuation-passing style (CPS) conversion. CPS is an important tool for programming language research: from a theoretical side, it explains evaluation order and bridges between classical and constructive logics. On the practical side, it has been used as compiler intermediate languages or for the implementation of cooperative multi-threading. If you haven't seen it before, you should learn more about it.

For our purposes, CPS is a good case study because it changes the binding structure of its input — each function gains an extra argument.
Therefore, when implementing this operation, we need to work in a changing scope -- the scope of 
the input term is not necessarily the same as the scope of the output. Because we are working 
with de Bruijn indices, we need to be careful what scope we are in, and the types help us with that. 
At the same time, when we go to test our implementation, we don't need to worry about variable 
names; we are naturally working with terms up to alpha-equivalence. 

---

## 1. What is CPS?

In direct style, a function returns its result to its caller implicitly.  In
*continuation-passing style* every function receives an extra argument — the
*continuation* — which represents "what to do with the result".  Instead of
returning, a function calls its continuation.

The transformation is defined inductively on terms.  We write `[[e]] k` to
mean "translate `e`, passing results to continuation `k`". An informal 
definition of this operation is below:

```
[[x]]          k = k x
[[λx. e]]      k = k (λx. λk'. [[e]] k')
[[e1 e2]]      k = [[e1]] (λx. [[e2]] (λy. x y k))
[[()]]         k = k ()
[[(e1, e2)]]   k = [[e1]] (λx. [[e2]] (λy. k (x,y)))
[[inj i e]]    k = [[e]] (λx. k (inj i x))
[[case e of () -> b]]      k = [[e]] (λz. case z of () -> [[b]] k)
[[case e of (x,y) → b]]    k = [[e]] (λz. case z of (x,y) → [[b]] k)
[[case e of inj i → b_i]]  k = [[e]] (λz. case z of inj i → [[b_i]] k)
```

The top-level call typically uses the identity continuation: `cps e = [[e]] (λx. x)`.

Note that this is a call-by-value translation: the evaluation of the result of the translation
should occur in the same order as the call-by-value evaluation.

-- 

## 2. Implementation using rebound (pure lambda calculus)

Let's look at how we could translate the definition above to executable Haskell code. 
The difficult part of this translation is right there near the top: when we translate a function, we need to introduce a new argument `k'` to pass in the "continuation" of the function.

```
[[ \x.e ]] k = k (λx. λk'. [[e]] k')
```

That means that when we call the translation recursively, `e` might be in some scope `S n`, because 
it is inside the body of a lambda expression. However, the result is going to be in some larger scope
that binds not just `x` but also `k'`. What that means is that the *variable* case is also challenging. Even though with names above we say `[[x]]k` produces `k x`, the scope of the first `x`
may be different than the scope of the second `x`, so they may be different indices.

Therefore, we need to parameterize our cps conversion function with a substitution that talks about the scope change. If the input term is in some scope `n` and the output scope is `m`, then we need 
an argument of type `Env Tm n m` to go between the two.  Furthermore, the continuation argument 
should be in the *output* scope.  

For the variable case, we apply this renaming to the variable, to get its version in the 
output scope. We can then use it to construct the application of the continuation to this 
new variable.

```
cpsExp :: Env Tm n m -> Tm n -> Tm m -> Tm m
cpsExp r (Var x) k = App k (applyEnv r x)
```

For the lambda case, we will also apply the continutation `k` to a value. 
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
need to account for the second binder for the continutation. This binder only 
affects the output scope, as opposed to the first that is part of both. Therefore, 
we need to shift the variables in the output, which we do by post-composing 
the substiiution with `wk`.

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

If we implement the cps conversion algorithm, we want to know that we did so correctly. Intuitively, this means that when we apply this transformation to some code, the output should produce the same result when we run it.

But what does that mean formally?  We can start with this simple statement, which asserts
that we get the same result from evaluation for any term and its cps conversion:

```
prop_same_result e = eval e == eval (cps e)
```

But already we have a problem, here. This property is not true.
```
ghci> qc prop_cps_result
*** Failed! Falsified (after 1 test):  
Lam (bind1 (Var 0))
e          = (λ x. x)
cps_e      = (λ x. x) (λ x k. k x)
```

The result of evaluation after CPS translating the identity function is `(λ x k. k x)`. 
And this is not the same as `(λ x. x)`. We can fix this by only looking at the cases 
where the result of evaluation is "first-order", i.e. a value that does not contain 
a function.

This solves the issue, but we need to throwaway a lot of cases.

```
ghci> qc prop_cps_result_firstorder
+++ OK, passed 1000 tests; 1373 discarded.
```

### Simulation properties (big-step)

We can do better by thinking about simulation properties.

Another way to state the correctness of CPS conversion is through the use of a simulation relation. 
If our source language (the lambda calculus) evaluates to a result (the CPS-converted language)
evaluates to an equivalent result. We might draw a picture like this:

```
           e  =>  v 
           |      |
        cps e => cps v
```

In other words, we want to show that if `e` evaluates to `v`, then `cps e` evaluates to `cps v`.
```
prop_cps_eval_simulates :: Property
prop_cps_eval_simulates = forAll genTypedFull $ \e ->
       counterexample ("e          = " ++ pp e)          $
       counterexample ("cps_e      = " ++ pp (cps e))    $
       eval (cps e) == (cps <$> eval e)
```

Note that this property is not true. 

```
ghci> qc prop_cps_eval_simulates
*** Failed! Falsified (after 1 test):  
Unit
e          = ()
cps_e      = (λ x. x) ()
```
In this counter example, we have a value that translates to a non-value.

We can (partially) repair it by keeping our "top-level" continuation abstract. Instead of 
using the identity function, if we use a distinguished variable, then that solves the 
problem for `()`.

However, this solution will not scale to the full language.


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
```

The instance body is empty because the library's default generic machinery 
handles it.

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

---

## 5. Exercises