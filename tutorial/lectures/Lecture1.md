# Lecture 1: Well-Scoped De Bruijn Representations

## Overview

This lecture covers the representation of lambda calculus terms with *variable binding*. We build the infrastructure from scratch in `Tutorial.Scoped.Scratch`, use it in an evaluator in `Tutorial.Scoped.Eval`, and then show how to replace the hand-written infrastructure with the `rebound` library in `Tutorial.Scoped.Syntax`.

---

## 1. The Problem: Variable Binding

Variable binding is the central challenge in implementing any language with binders (λ-abstractions, let-expressions, pattern matching). The core operation is *substitution*: to evaluate

```
(λx. x + x) 42
```

we substitute `42` for `x` in `x + x`. But substitution in the presence of free variables requires care. A naive string-substitution breaks on examples like

```
(λx. λy. x) y   →   λz. y     -- must rename inner binder to avoid capturing y
```

*Capture-avoiding substitution* handles this by tracking free variables and renaming binders that would capture them. Correct implementations are tedious and a notorious source of bugs.

A separate nuisance: with named variables, `λx. x` and `λy. y` are *alpha-equivalent* but structurally different, so a naive `Eq` instance is wrong.

**De Bruijn indices** solve both problems. Replace variable names with numbers counting the binders between a use and its binding site:

```
λx. x          becomes   λ. 0
λx. λy. x      becomes   λ. λ. 1
λx. λy. x + y  becomes   λ. λ. 1 + 0
```

Alpha-equivalence collapses to structural equality — we get a correct `Eq` instance for free. And because there are no names, there is nothing to capture. The substitution function still requires care, as we will see, but at least the problem is well-defined.

---

## 2. Finite Sets and Scopes — `Nat` and `Fin`

The *well-scoped* approach tracks the number of variables in scope at the type level, ruling out out-of-scope variable references statically.

```haskell
data Nat = Z | S Nat
```

A term in scope `n` may refer to variables `0` through `n-1`. We represent this finite set as a GADT:

```haskell
data Fin n where
    FZ :: Fin (S n)           -- zero, valid in any non-empty scope
    FS :: Fin n -> Fin (S n)  -- successor
```

`Fin Z` is uninhabited, which means a closed term (scope `Z`) cannot contain any variables — the type checker enforces this statically. Some examples:

- `FZ :: Fin (S Z)` — the only variable in scope 1
- `FZ :: Fin (S (S Z))` — variable `0` in scope 2
- `FS FZ :: Fin (S (S Z))` — variable `1` in scope 2

---

## 3. Terms and Types — `Ty` and `Tm`

Our object language is a simply-typed lambda calculus with binary products and sums:

```haskell
data Ty = One | Zero | Ty :-> Ty | Ty :* Ty | Ty :+ Ty
```

Terms are indexed by their scope:

```haskell
data Tm (n :: Nat) where
    Var       :: Fin n -> Tm n
    Lam       :: Bind1 n -> Tm n
    Unit      :: Tm n
    Pair      :: Tm n -> Tm n -> Tm n
    Inj       :: Int -> Tm n -> Tm n
    App       :: Tm n -> Tm n -> Tm n
    MatchUnit :: Tm n -> Tm n -> Tm n
    MatchPair :: Tm n -> Bind2 n -> Tm n
    MatchSum  :: Tm n -> Bind1 n -> Bind1 n -> Tm n
```

Although written in GADT syntax, `Tm` is not a proper GADT — all constructors produce `Tm n` for the same `n`. The interesting type-level work happens in `Fin n`. A term of type `Tm Z` is closed.

---

## 4. Binders — `Bind1` and `Bind2`

When we cross a binder, the scope grows. `Bind1 n` packages a body that lives in scope `S n`:

```haskell
data Bind1 n where
    Bind1 :: Tm (S n) -> Bind1 n
```

`Bind2 n` packages a body under two simultaneous binders (used in `MatchPair`):

```haskell
data Bind2 n where
    Bind2 :: Tm (S (S n)) -> Bind2 n
```

Inside a `Bind1 n`, `FZ` is the newly-bound variable and `FS x` refers to whatever `x` referred to in the outer scope. Inside a `Bind2 n`, `FZ` is the second-bound variable, `FS FZ` the first-bound, and `FS (FS x)` escapes to the outer scope.

Some concrete examples:

```haskell
-- λx. x
ex_id :: Tm Z
ex_id = Lam (Bind1 (Var FZ))

-- λx. λy. x   (x = FS FZ inside inner body, y = FZ)
ex_const :: Tm Z
ex_const = Lam (Bind1 (Lam (Bind1 (Var (FS FZ)))))

-- λf. λg. λx. f (g x)
ex_comp :: Tm Z
ex_comp = Lam (Bind1 (Lam (Bind1 (Lam (Bind1
    (App (Var (FS (FS FZ))) (App (Var (FS FZ)) (Var FZ))))))))
--               f                    g               x
```

---

## 5. Substitution Environments

A *substitution environment* maps variables in one scope to terms in another:

```haskell
type Env m n = Fin m -> Tm n
```

An `Env m n` maps each of `m` variables to a term in scope `n`. You should think of this as 
an abstract data structure that maps indices to terms. Above, we represent it as a function (with a finite 
domain), but it could also be implemented with a length-indexed vector, array, tree, or other 
structure. In the fourth lecture we will discuss various trade-offs in the representation. However, first let's talk about the interface that we need from this structure.

The most important operation that we need for this data structure is to be able to apply it to a term, replacing all of the free variables in the term with their definitions in the environment.
This operation is sometimes called *parallel substitution* because it performs multiple substitutions at once.

```haskell
applyE :: Env m n -> Tm m -> Tm n
```

### List-like structure: empty and extension

```haskell
zeroE :: Env Z m             
zeroE = \n -> case n of {} 

infixr 5 .:
(.:) :: Tm n -> Env m n -> Env (S m) n
t .: env = \f -> case f of
              FZ   -> t
              FS x -> env x
```

Like cons: `t .: env` extends `env` with a binding for the outermost variable. Right-associativity lets us write `t1 .: t2 .: env` naturally.


### Identity and Shifting

```haskell
idE :: Env n n
idE = Var

shift :: Env m (S m)
shift = Var . FS
```
Weakens a scope: applying `applyE shift` to a term in scope `n` produces the same term in scope `S n`, where `FZ` is fresh.

### Lifting and Composition

```haskell
lift :: Env m n -> Env (S m) (S n)
lift env = Var FZ .: (applyE shift . env)
```

Lifts an environment under one binder. The new outermost variable maps to itself; every other variable `x` maps to `env x` weakened into the larger scope.

```haskell
compE :: Env m n -> Env l m -> Env l n
compE f g x = applyE f (g x)
```

Satisfies `applyE (compE f g) = applyE f . applyE g`.

---

## 6. Applying a Substitution — `applyE`

`applyE` traverses a term, replacing variables via the environment and lifting under each binder:

```haskell
applyE :: Env m n -> Tm m -> Tm n
applyE env (Var x)               = env x
applyE env (Lam (Bind1 b))       = Lam (Bind1 (applyE (lift env) b))
applyE _   Unit                  = Unit
applyE env (Pair a b)            = Pair (applyE env a) (applyE env b)
applyE env (Inj i t)             = Inj i (applyE env t)
applyE env (App f a)             = App (applyE env f) (applyE env a)
applyE env (MatchUnit a b)       = MatchUnit (applyE env a) (applyE env b)
applyE env (MatchPair a (Bind2 b)) =
    MatchPair (applyE env a) (Bind2 (applyE (lift (lift env)) b))
applyE env (MatchSum a (Bind1 b1) (Bind1 b2)) =
    MatchSum (applyE env a)
             (Bind1 (applyE (lift env) b1))
             (Bind1 (applyE (lift env) b2))
applyE env (Ann t ty)            = Ann (applyE env t) ty
```

The key cases are the binders. For `Lam (Bind1 b)`, the body lives in scope `S m`, so we apply `lift env :: Env (S m) (S n)`. For `MatchPair (Bind2 b)`, which binds two variables, we apply `lift (lift env)`.

Note that `applyE` and `lift` are mutually recursive. In a proof assistant like Agda or Rocq, this mutual recursion through non-structural calls causes problems for the termination checker. The standard fix is to first define a *renaming* function (mapping variables to variables, not terms), use that for shifting, and then define substitution separately. We sidestep this here since Haskell has no termination checker.

---

## 7. Opening Binders — `instantiate1` and `instantiate2`

To evaluate `(λx. body) arg` we *instantiate* the binder: substitute `arg` for `FZ` in `body`. An environment that does this is `arg .: idE`, which maps `FZ → arg` and `FS x → Var x`:

```haskell
instantiate1 :: Bind1 n -> Tm n -> Tm n
instantiate1 (Bind1 body) t = applyE (t .: idE) body
```

For double binders we supply two terms:

```haskell
instantiate2 :: Bind2 n -> Tm n -> Tm n -> Tm n
instantiate2 (Bind2 body) t1 t2 = applyE (t1 .: t2 .: idE) body
```

---

## 8. Using the Infrastructure — `Eval.hs`

The evaluator in `Tutorial.Scoped.Eval` applies these primitives. The type signature

```haskell
eval :: Tm Z -> Either String (Tm Z)
```

reflects that we only evaluate closed terms. A few representative cases:

**Function application:**
```haskell
eval (App m n) = do
    mv <- eval m
    nv <- eval n
    case mv of
        Lam b -> eval (instantiate1 b nv)
        _     -> Nothing
```

**Pair elimination:**
```haskell
eval (MatchPair e m) = do
    v <- eval e
    case v of
        Pair v1 v2 -> eval (instantiate2 m v1 v2)
        _          -> Nothing
```

**Sum elimination:**
```haskell
eval (MatchSum e0 m m') = do
    v <- eval e0
    case v of
        Inj 0 v1 -> eval (instantiate1 m  v1)
        Inj 1 v1 -> eval (instantiate1 m' v1)
        _        -> Nothing
```

The variable case requires no clause at all. Since `Tm Z` contains no variables, `Fin Z` is uninhabited, and the pattern match is vacuously exhaustive:

```haskell
eval (Var x) = case x of {}
```

---

## 9. Using `rebound` — `Scoped.Syntax`

The infrastructure in `Scratch.hs` — `Bind1`, `Bind2`, `applyE`, `idE`, `(.:)`, `shift`, `lift`, `instantiate1`, `instantiate2` — is entirely generic: none of it depends on the specific constructors of `Tm`. The `rebound` library packages this machinery so you do not have to rewrite it for each new language.

The file `Tutorial.Scoped.Syntax` shows the updated version. The differences are:

- Import the relevant modules from `rebound`
- Provide the type parameter to `Bind1`/`Bind2` in the `Tm` definition
- Derive `Generic1` for `Tm`
- Give instances of `SubstVar Tm` and `Subst Tm Tm` (the `Generic1` machinery fills in `applyE` automatically)

---

## 10. Testing with QuickCheck — `TestEval.hs`

With the evaluator in hand we can state and test natural correctness properties. Two main properties:

**`prop_evalVal`** — evaluation always produces a value (when it succeeds):

```haskell
prop_evalVal :: Tm Z -> Property
prop_evalVal e = case eval e of
    Nothing -> discard
    Just v  -> counterexample ("term: "  ++ pp e) $
               counterexample ("value: " ++ pp v) $
               isVal v
```

**`prop_evalStep`** — one small step does not change the final result:

```haskell
prop_evalStep :: Tm Z -> Property
prop_evalStep e =
    case step e of
        Nothing  -> discard
        Just e'  -> counterexample ("e  = " ++ pp e)  $
                    counterexample ("e' = " ++ pp e') $
                    eval e == eval e'
```

The `counterexample` calls translate to named syntax before printing, so failures look like

```
*** Failed! ...
term:  (λ x0. x0) ()
value: ...
```

rather than raw constructor soup.

Running the tests:

```
ghci> qc prop_evalVal
+++ OK, passed 1000 tests; 871 discarded.
ghci> qc prop_evalStep
+++ OK, passed 1000 tests; 543 discarded.
```

The high discard rate reflects the fact that randomly generated terms are often stuck (they are not well-typed). Random terms could in principle also diverge, but that is rare here. Importantly, all randomly generated terms are *well-scoped* — the type index guarantees that — so we at least avoid out-of-scope variable errors at runtime. Next time we will look at how to generate well-typed terms.

---

## Exercises

**1. Writing terms.** Write the following closed terms in `Tutorial.Scoped.Scratch`. Work out the de Bruijn indices by hand before trying it in GHCi.

- `ex_fst :: Tm Z` — the projection `λp. match p with (x, y) → x`
- `ex_snd :: Tm Z` — the projection `λp. match p with (x, y) → y`
- `ex_s :: Tm Z` — the S combinator `λf. λg. λx. f x (g x)`

Pay attention to the variable ordering inside `Bind2`. In `MatchPair e (Bind2 body)`, `FZ` refers to the *first* pair component and `FS FZ` to the second — you can verify this against `ex_swap` in `Scratch.hs`. (The reason: `instantiate2 m v1 v2` maps `FZ → v1`, and `eval` calls it with `v1` = first component.)

---

**2. Weakening.** Define a function

```haskell
weaken :: Tm n -> Tm (S n)
weaken = applyE shift
```

This embeds a term from scope `n` into the larger scope `S n`, leaving the new variable `FZ` unused. Verify in GHCi that `weaken ex_id :: Tm (S Z)` type-checks and that applying `instantiate1 (Bind1 (weaken e)) t` returns `e` unchanged for any `e` and `t`.

Why does `applyE shift` have the right type? Trace through the definition of `shift` and `applyE` to convince yourself.

---

**3. Adding `let`.** Extend the language in `Tutorial.Scoped.Scratch` with a `let`-expression:

```haskell
Let :: Tm n -> Bind1 n -> Tm n
```

`Let e b` binds the value of `e` in the body `b`. You will need to:
1. Add the constructor to `Tm`
2. Add a case to `applyE` — what environment do you pass into the binder?
3. Add a case to `eval` in `Tutorial.Scoped.Eval` — `let x = e in b` is a by-value let, so evaluate `e` first, then instantiate `b`

Check: is `Let e b` equivalent to `App (Lam b) e`? Do both evaluate the same way?

---

**4. Renamings.** A *renaming* is an environment that maps variables to variables rather than terms:

```haskell
type Ren m n = Fin m -> Fin n
```

Define `applyRen :: Ren m n -> Tm m -> Tm n` by structural recursion, analogous to `applyE`. You will also need `liftRen :: Ren m n -> Ren (S m) (S n)`.

Now observe: every renaming `r :: Ren m n` induces a substitution `Var . r :: Env m n`, and `applyRen r = applyE (Var . r)`. Verify this equality as a QuickCheck property on `Tm Z` for the specific case `r = FS` (i.e., `shift`).

The reason proof assistants define `applyRen` separately is that `applyRen` *is* structurally recursive (it produces variables, not terms), so it can be used to define `lift` without the mutual recursion that troubles Agda and Rocq.

---

**5. Substitution laws.** State and test the following equational laws as QuickCheck properties on `Tm Z`:

- *Identity*: `applyE idE t == t`
- *Composition*: `applyE f (applyE g t) == applyE (compE f g) t`
- *Instantiate-shift*: `instantiate1 (Bind1 (weaken t)) u == t` for any `t u :: Tm Z`

For the composition law, use concrete environments, e.g. `g = idE` and `f = idE`, or build simple environments with `(.:)`. Can you find a counterexample to any of these properties if you get the implementation of `lift` wrong?
