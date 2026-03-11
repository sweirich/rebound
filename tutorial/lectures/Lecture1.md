# Lecture 1: Well-Scoped De Bruijn Representations

## Overview

This lecture covers how to represent lambda calculus terms with *variable binding*
in Haskell. We will build the infrastructure from scratch in
`Tutorial.Scoped.Scratch`, use it in an evaluator in `Tutorial.Scoped.Eval`,
and then show how to replace the hand-written infrastructure with the
`rebound` library in `Tutorial.Scoped.Syntax`.

---

## 1. The Problem: Variable Binding

Before we even get to substitution, there is a more basic challenge: deciding
whether two terms are *the same*. With named variables, the terms `λx. x` and
`λy. y` are *alpha-equivalent* — they differ only in the names of bound
variables — yet a naive structural equality check would say they are different.
Implementing alpha-equivalence correctly requires comparing terms up to
consistent renaming, which is fiddly and easy to get wrong.

The central challenge in implementing a language with binders (λ-abstractions,
let-expressions, pattern matching) is *substitution*. Given a term like

```
(λx. x + x) 42
```

we evaluate the application by substituting `42` for `x` in the body `x + x`.
This sounds simple, but a naive string-substitution approach breaks when working with
terms with free variables:

```
(λx. λy. x) y   →   λz. y     -- must rename inner binder to avoid capturing y
```

A naive substitution would wrongly capture the inner `y` as the substitution propagates
under the binder.
The standard fix — *capture-avoiding substitution* — requires tracking free
variables and renaming binders that would capture them. This is tricky to get
right and has been a source of bugs in countless implementations.

**De Bruijn indices** sidestep the problem entirely by replacing variable
*names* with *numbers* that count the number of binders between a variable
occurrence and the binder that introduced it.

```
λx. x          becomes   λ. 0
λx. λy. x      becomes   λ. λ. 1
λx. λy. x + y  becomes   λ. λ. 1 + 0
```

Because there are no variable names, alpha-equivalence collapses to *structural
equality*: two terms are alpha-equivalent if and only if they are identical as
Haskell values. We get a correct `Eq` instance for free, with no extra work.

There are no names to capture, and the substitution function must be implemented 
with care. Furthermore, the representation is harder to read for humans,
but tooling (pretty-printers, parsers) can bridge that gap.

---

## 2. Finite Sets and Scopes — `Nat` and `Fin`

The key insight of *well-scoped* de Bruijn representations is to track the
*number of variables in scope* at the type level, so the type system rules out
out-of-scope variable references.

```haskell
data Nat = Z | S Nat
```

We use unary natural numbers as a type-level index. A term in scope `n` may
refer to variables `0` through `n-1`. We represent this finite set as a GADT:

```haskell
data Fin n where
    FZ :: Fin (S n)       -- the number 0, valid in any non-empty scope
    FS :: Fin n -> Fin (S n)  -- successor: if x is valid in n, x+1 is valid in S n
```

`Fin Z` is an *empty type* — there are no inhabitants — which means a closed
term (scope `Z`) cannot contain any variables. The Haskell type checker enforces
this statically.

Examples:
- `FZ :: Fin (S Z)` — the only variable in a scope of size 1
- `FZ :: Fin (S (S Z))` — variable `0` in a scope of size 2
- `FS FZ :: Fin (S (S Z))` — variable `1` in a scope of size 2

---

## 3. Terms and Types — `Ty` and `Tm`

Our language is a simply-typed lambda calculus with binary products and sums:

```haskell
data Ty = One | Zero | Ty :-> Ty | Ty :* Ty | Ty :+ Ty
```

Terms are parameterized by their scope:

```haskell
data Tm (n :: Nat) where
    Var       :: Fin n -> Tm n         -- a variable in scope n
    Lam       :: Bind1 n -> Tm n       -- λ-abstraction (see §4)
    Unit      :: Tm n                  -- the unit value ()
    Pair      :: Tm n -> Tm n -> Tm n  -- pair (e1, e2)
    Inj       :: Int -> Tm n -> Tm n   -- injection into a sum
    App       :: Tm n -> Tm n -> Tm n  -- function application
    MatchUnit :: Tm n -> Tm n -> Tm n  -- match () with () → e
    MatchPair :: Tm n -> Bind2 n -> Tm n        -- match e with (x,y) → e'
    MatchSum  :: Tm n -> Bind1 n -> Bind1 n -> Tm n  -- case analysis
```

Note that `Var` holds a `Fin n` — an index that is *provably in scope*. 
Even though we have written this data type with GADT syntax, unlike `Fin`, it is not a GADT. 
All of the magic of the well-scoped representation lies in the `Fin` type. 

A term of type `Tm Z` is a *closed* term with no free variables.

---

## 4. Binders — `Bind1` and `Bind2`

In the abstract syntax definition above, we mark binding locations 
using the types `Bind1` and `Bind2`. 

When we cross a binder (a `λ` or a pattern match), the scope grows by the
number of newly-bound variables. `Bind1 n` type packages a term whose body lives
in scope `S n` — one variable larger than the surrounding scope:

```haskell
data Bind1 n where
    Bind1 :: Tm (S n) -> Bind1 n
```

Similarly, `Bind2 n` packages a body under *two* binders (cf. `MatchPair`):

```haskell
data Bind2 n where
    Bind2 :: Tm (S (S n)) -> Bind2 n
```

Inside a `Bind1 n`, variable `FZ` refers to the newly-bound variable, and
`FS x` refers to whatever `x` referred to in the enclosing scope. Inside a
`Bind2 n`, `FZ` is the second-bound variable, `FS FZ` is the first-bound, and
`FS (FS x)` accesses the enclosing scope.

The example terms make this concrete:

```haskell
-- λx. x  (closed, scope Z)
ex_id :: Tm Z
ex_id = Lam (Bind1 (Var FZ))
--                       ^^  FZ refers to x

-- λx. λy. x  (scope Z, x=FS FZ inside inner body, y=FZ)
ex_const :: Tm Z
ex_const = Lam (Bind1 (Lam (Bind1 (Var (FS FZ)))))
--                                      ^^^^^  skips past y to reach x

-- λf. λg. λx. f (g x)
ex_comp :: Tm Z
ex_comp = Lam (Bind1 (Lam (Bind1 (Lam (Bind1
    (App (Var (FS (FS FZ))) (App (Var (FS FZ)) (Var FZ))))))))
--               f=FS(FS FZ)  g=FS FZ              x=FZ
```

---

## 5. Substitution Environments

To define substitution we introduce *substitution environments*:

```haskell
type Env m n = Fin m -> Tm n
```

An `Env m n` is a function that maps each of the `m` variables in scope to a
term living in scope `n`. There are several fundamental operations on environments:

### Identity

```haskell
idE :: Env n n
idE = Var
```

Maps every variable to itself. Applying `idE` leaves a term unchanged.

### Cons / Extension

```haskell
infixr 5 .:
(.:) :: Tm n -> Env m n -> Env (S m) n
t .: env = \case
    FZ   -> t      -- the new outermost variable maps to t
    FS x -> env x  -- all others delegate to env
```

Like list cons: `t .: env` extends `env` with a new binding for `FZ`.
The right-associativity means we can write `t1 .: t2 .: idE` naturally.

### Shift

```haskell
shift :: Env m (S m)
shift = Var . FS
```

Maps each variable `x` to `Var (FS x)`. This *weakens* a scope: applying
`applyE shift` to a term in scope `n` produces the same term in scope `S n`,
where variable `FZ` is fresh and unused.

### Lift

```haskell
lift :: Env m n -> Env (S m) (S n)
lift env = Var FZ .: (applyE shift . env)
```

Lifts an environment under one binder. The new outermost variable (`FZ`) maps
to itself. Every other variable `x` maps to `env x` weakened into the larger
scope with `applyE shift`. We use this operation when descending into a 
`Bind1` during substitution.

### Composition

We can *compose* two environments by applying the first to the codomain of the 
second.

```haskell
compE :: Env m n -> Env l m -> Env l n
compE f g x = applyE f (g x)
```

Satisfies `applyE (compE f g) = applyE f . applyE g`.

---

## 6. Applying a Substitution — `applyE`

`applyE` traverses a term, replacing each variable with its image under the
environment, lifting the environment under each binder:

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

The key cases are the binders. For `Lam (Bind1 b)`, the body `b` lives in
scope `S m` (one extra variable), so we must apply `lift env :: Env (S m) (S n)`
rather than `env`. For `MatchPair (Bind2 b)`, which binds two variables,
we apply `lift (lift env)`.

Note that `applyE` and `lift` are *mutually recursive*: `lift` calls
`applyE shift` to weaken each term, and `applyE` calls `lift` when descending
under binders. This operation is not structurally recursive so the fact that 
it terminates is not obvious to provers, such as Agda or Rocq. Instead, in these 
contexts, it is common to first define a renaming function (which only replaces variables by other variables) and then use that function for shifting when defining
substitution. We can side-step that complexity here.

---

## 7. Opening Binders — `instantiate1` and `instantiate2`

To evaluate an application `(λx. body) arg` we need to substitute `arg` for
`x` in `body`. We call this operation *instantiation*, implemented with the 
`instantiate1` function below.

The binder `Bind1 n` holds the body in scope `S n`; we instantiate it
by building an environment that maps `FZ` (the bound variable) to `arg` and
leaves all other variables unchanged:

```haskell
instantiate1 :: Bind1 n -> Tm n -> Tm n
instantiate1 (Bind1 body) t = applyE (t .: idE) body
```

Note that `t .: idE` maps `FZ → t` and `FS x → Var x`, which is exactly what we want.

For double binders, we supply two terms when we instantiate:

```haskell
instantiate2 :: Bind2 n -> Tm n -> Tm n -> Tm n
instantiate2 (Bind2 body) t1 t2 = applyE (t1 .: t2 .: idE) body
```

---

## 8. Using the Infrastructure — `Eval.hs`

The evaluator in `Tutorial.Scoped.Eval` shows these primitives in action.
It imports `Tutorial.Scoped.Scratch` and uses `instantiate1`/`instantiate2`
at every elimination step:

```haskell
eval :: Tm Z -> Either String (Tm Z)
```

The closed-term type `Tm Z` guarantees that a well-formed program has no free
variables. A few representative cases:

**Function application** — open the binder by substituting the argument:
```haskell
eval (App m n) = do
    mv <- eval m
    nv <- eval n
    case mv of
        Lam b -> eval (instantiate1 b nv)
        _     -> Nothing
```

**Pair elimination** — open a two-variable binder:
```haskell
eval (MatchPair e m) = do
    v <- eval e
    case v of
        Pair v1 v2 -> eval (instantiate2 m v1 v2)
        _          -> Nothing
```

**Sum elimination** — open whichever branch matches:
```haskell
eval (MatchSum e0 m m') = do
    v <- eval e0
    case v of
        Inj 0 v1 -> eval (instantiate1 m  v1)
        Inj 1 v1 -> eval (instantiate1 m' v1)
        _        -> Nothing
```

The variable case is vacuously handled — since `Tm Z` contains no variables,
the `Fin Z` index is an empty type and `case x of {}` is exhaustive:

```haskell
eval (Var x) = case x of {}
```

---

## 9. Using `rebound` — `Simple.Syntax`

The infrastructure in `Scratch.hs` — `Bind1`, `Bind2`, `applyE`, `idE`,
`(.:)`, `shift`, `lift`, `instantiate1`, `instantiate2` — is entirely
*generic*: it does not depend on the specific constructors of `Tm`. The
`rebound` library packages this machinery so you don't have to rewrite it for
every new language.

The file `Tutorial.Scoped.Syntax` shows the updated version. The key differences 
are: 
- import relevant modules from `rebound`
- supply type parameters to `Bind1`/`Bind2` types in `Tm` definition
- derive `Generic1` class for `Tm` (see below)
- create instances of `SubstVar Tm` and `Subst Tm Tm` to replace explicit
  definition of `applyE`.

---

## 10. Testing with QuickCheck — `TestEval.hs`

With the evaluator in hand we can state and test some natural correctness
properties using QuickCheck.  The two main properties are:

**`prop_evalVal`** — evaluation always produces a value (when it succeeds):

```haskell
prop_evalVal :: Tm Z -> Property
prop_evalVal e = case eval e of
    Nothing -> discard          -- stuck terms are not counterexamples
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

When a property fails, QuickCheck prints a counterexample.  Instead of
showing the raw Haskell constructor soup — `App (Lam (Bind1 (Var FZ))) Unit`
— the `counterexample` calls translate the term to a named syntax and run the
pretty printer first, giving readable output like:

```
*** Failed! ...
term:  (λ x0. x0) ()
value: ...
```

Running the tests:

```
ghci> qc prop_evalVal
+++ OK, passed 1000 tests; 871 discarded.
ghci> qc prop_evalStep
+++ OK, passed 1000 tests; 543 discarded.
```

The high discard rate reflects the fact that randomly generated terms often
get stuck (they are not well-typed). Randomly generated terms *could* also diverge, but that is rare in this context. However, we do know that our our randomly generated terms are *well-scoped*, so we can avoid that sort of runtime error. We will talk about how to do that next time.
