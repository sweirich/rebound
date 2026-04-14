# Lecture 1: Well-Scoped De Bruijn Representations

## Modules referenced in this lecture

- [Tutorial.Scoped.Scratch](https://github.com/sweirich/rebound/blob/main/tutorial/main/src/Tutorial/Scoped/Scratch.hs)
- [Tutorial.Scoped.Syntax](https://github.com/sweirich/rebound/blob/main/tutorial/main/src/Tutorial/Scoped/Syntax.hs)
- [Tutorial.Scoped.Eval](https://github.com/sweirich/rebound/blob/main/tutorial/main/src/Tutorial/Scoped/Eval.hs)

## Overview and Goals

This lecture covers a well-scoped representation of lambda calculus terms. By
well-scoped, we mean that the type system statically tracks the scope of each
term. If the type of the term says that its scope is empty, then it will be a
type error to reference a free variable in the term.

During the next fifty minutes, we will define this representation using de
Bruijn indices (i.e. natural numbers) to represent variables. We will also
implement a substitution-based interpreter with this representation, where
type checking ensures that we haven't made any scope errors.

The goals of this lecture are to: 

- cover the building blocks of working with the lambda calculus and
  implementing capture-avoiding substitution
    
- convince you that the small amount of dependently-typed programming needed
  for well-scoped lambda terms pays off, even in Haskell 
    
- show-off the `rebound` library 

In general, the ideas that we will cover this week should translate to any functional 
programming language with minimal support for dependent types. I'm using Haskell, but if 
you are working in Agda, Idris, Lean, or Rocq, you can translate this code to that 
setting.


## 1. The Problem: Variable Binding

Variable binding is the central challenge in implementing any language with binders (λ-abstractions, let-expressions, pattern matching). The core operation is *substitution*: to evaluate

```
(λx. x + x) 42
```

we substitute `42` for `x` in `x + x`. But substitution in the presence of free variables requires care. A naive string-substitution breaks on examples like

```
(λx. λy. x) y   →   λz. y     -- must rename inner binder to avoid capturing y
```

*Capture-avoiding substitution* handles this by tracking free variables and renaming binders that would capture them. Unfortunately, implementations of this operation are a notorious source of bugs.

Furthermore, with named variables, `λx. x` and `λy. y` are *alpha-equivalent* but structurally different. When implementing lambda calculus terms, we want to decide when terms are equivalent up-to the names of bound variables.


**De Bruijn indices** solve both problems, i.e. we replace variable names with numbers counting the binders between a use and its binding site:

```
λx. x          becomes   λ. 0
λx. λy. x      becomes   λ. λ. 1
λx. λy. x + y  becomes   λ. λ. 1 + 0
```

Alpha-equivalence collapses to structural equality — we get a correct
implementation in Haskell for free (by deriving the `Eq` type class). And
because there are no names, there is nothing to capture. While, we will still
need to do some work to define our substitution function, statically checking
the scopes will help us develop a correct implementation.

---

## 2. Finite Sets and Scopes — `Nat` and `Fin`

The *well-scoped* approach tracks the number of variables in scope at the type level, ruling out out-of-scope variable references statically. Let's start with the definition of natural numbers, zero and successor.

```haskell
data Nat = Z | S Nat
```

In Haskell, we can use these numbers in types. For example, here are some names that we can use for type-level numbers: 

```haskell
type N1 = S Z
type N2 = S (S Z)
type N3 = S (S (S Z))
```

A term in scope `n` may refer to variables `0` through `n-1`. We represent numbers in this finite scope as a GADT:

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

## 3. Types, Terms and Binders

Our object language is a simply-typed lambda calculus with binary products and sums:

```haskell
data Ty = One | Ty :-> Ty | Ty :* Ty | Ty :+ Ty
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

## 4. Substitution Environments

*Substitution* is an operation replaces the free variables in terms with other terms. We will use a data structure, called an environment, as part of this mapping. It stores the association between every variable in some scope `m` to terms that all must be in the same scope `n`.

The simplest way to express a *substitution environment* is using a function with the following type:

```haskell
type Env m n = Fin m -> Tm n
```

An `Env m n` maps each of `m` variables to a term in scope `n`. You should think of this as
an abstract data structure that maps indices to terms. Above, we represent it as a function (with a finite
domain), but it could also be implemented with a length-indexed vector, array, tree, or other
structure. In the fourth lecture we will discuss various trade-offs in the representation. First, however, let's look at the interface we need from this structure.

The most important operation that we need for this data structure is to be able to apply it to a term, replacing all of the free variables in the term with their definitions in the environment.
This operation is sometimes called *parallel substitution* because it performs multiple substitutions at once.

```haskell
applyE :: Env m n -> Tm m -> Tm n
```

However, we also need to be able to build substitutions, using the following operations.

### List-like structure: empty and extension

Another way to think about an environment is like a list, where the *i*th position 
in the list is a mapping for index *i*. 

```haskell
zeroE :: Env Z m             
zeroE = \n -> case n of {} 

infixr 5 .:
(.:) :: Tm n -> Env m n -> Env (S m) n
t .: env = \f -> case f of
              FZ   -> t
              FS x -> env x
```

Like cons: `t .: env` extends `env` with a binding for the outermost variable. Right-associativity lets us write `t1 .: t2 .: env` like list cons.

For example, we can create an environment using the example terms above. Here,
the type of the environment tells us that there are exactly three closed
terms.

```haskell
exampleE :: Env N3 Z
exampleE = ex_id .: ex_const .: ex_comp .: zeroE
```

### More operations

Here's another example environment: an identity substitution for terms with three free variables. We map each index to a variable with that index.

```haskell
id3E :: Env N3 N3
id3E = Var f0 .: Var f1 .: Var f2 .: zeroE
```
But that is overly complicated. We can also create an identity substitution for 
every scope, with the following definition:

```haskell
idE :: Env n n
idE = Var
```

Furthermore, this definition hints at how we might update *all* free variables in a term. The *shift* environment increments every index by one. 

```haskell
shift :: Env n (S n)
shift = Var . FS
```
Weakens a scope: applying `applyE shift` to a term in scope `n` produces the same term in scope `S n`. In this scope, the variable `Var FZ` is not used.

## 5. Applying a Substitution

`applyE` traverses a term, replacing variables via the environment and lifting under each binder:

```haskell
-- | Apply a substitution environment to a term
applyE :: Env m n -> Tm m -> Tm n
applyE env (Var x)               = env x
applyE env (Lam (Bind1 b))       = Lam (Bind1 (applyE (up env) b))
applyE _   Unit                  = Unit
applyE env (Pair a b)            = Pair (applyE env a) (applyE env b)
applyE env (Inj i t)             = Inj i (applyE env t)
applyE env (App f a)             = App (applyE env f) (applyE env a)
applyE env (MatchUnit a b)       = MatchUnit (applyE env a) (applyE env b)
applyE env (MatchPair a (Bind2 b)) =
    MatchPair (applyE env a) (Bind2 (applyE (up (up env)) b))
applyE env (MatchSum a (Bind1 b1) (Bind1 b2)) =
    MatchSum (applyE env a)
             (Bind1 (applyE (up env) b1))
             (Bind1 (applyE (up env) b2))

-- | Lift an environment under one binder
up :: Env m n -> Env (S m) (S n)
up env = Var FZ .: (applyE shift . env)
```

The key cases are the binders. For `Lam (Bind1 b)`, the body lives in scope `S m`, so we apply `up env :: Env (S m) (S n)`. For `MatchPair (Bind2 b)`, which binds two variables, we apply `up (up env)`.

In the `up` environment, the new outermost variable maps to itself; every other variable `x` maps to `env x` weakened into the larger scope.

Note that `applyE` and `up` are mutually recursive. In a proof assistant like Agda or Rocq, this mutual recursion through non-structural calls makes termination checking difficult. The standard fix is to first define a *renaming* function (mapping variables to variables, not terms), use that for shifting, and then define substitution separately. We sidestep this here since Haskell has no termination checker.

Finally, let's define a helper function for instantiating binders.
If we were to evaluate `(λx. body) arg` we need to *instantiate* the binder: substitute `arg` for `FZ` in `body`. An environment that does this is `arg .: idE`, which maps `FZ → arg` and `FS x → Var x`:

```haskell
instantiate1 :: Bind1 n -> Tm n -> Tm n
instantiate1 (Bind1 body) t = applyE (t .: idE) body
```

For double binders we supply two terms:

```haskell
instantiate2 :: Bind2 n -> Tm n -> Tm n -> Tm n
instantiate2 (Bind2 body) t1 t2 = applyE (t1 .: t2 .: idE) body
```

## 6. Working with well-scoped terms

Now let's write a function that uses our well-scoped representation!

The end of the file includes a substitution-based evaluator for closed terms. This evaluator could encounter a runtime type error; for simplicity we return `Nothing` in that case.

```haskell
eval :: Tm Z -> Maybe (Tm Z)
```

The type of the evaluator also reflects that we only evaluate *closed* terms. The argument must type check in a scope that contains no variables.
As a result, the variable case is impossible. Since `Tm Z` contains no variables, `Fin Z` is uninhabited, and the empty pattern match is vacuously exhaustive:

```haskell
eval (Var x) = case x of {}
```
In other cases, we use `instantiate1` and `instantiate2` to 
substitute for the arguments in binders. Observe the order of 
instantiation when working with pairs. As stated above, inside a `Bind2`,
`FZ` is the second-bound variable and `FS FZ` is the first-bound variable.
So the second component of the pair has index 0 and the first component
has index 1.

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
        Pair v1 v2 -> eval (instantiate2 m v2 v1)
        _          -> Nothing
```

---

## 7. Using `rebound` 

Some of the infrastructure in `Scratch.hs` is entirely generic: it doesn't depend on the specific constructors of `Tm`. The `rebound` library packages this machinery so you do not have to rewrite it for each new language.

The file `Tutorial.Scoped.Syntax` shows the updated version. The differences are:

- Import the relevant modules from `rebound`
- Provide the type parameter to `Bind1`/`Bind2` in the `Tm` definition
- Derive `Generic1` for `Tm`
- Give instances of `SubstVar Tm` and `Subst Tm Tm` 
  (the `Generic1` machinery fills in `applyE` automatically)

---

## Historical Notes

**Named variables and capture-avoiding substitution.** The difficulty of
substitution under binders — and the need for alpha-renaming — was understood
by Church (1941) and Kleene (1952). The *Barendregt convention* (assume all
bound variables are distinct from free variables) is a paper-level workaround;
implementing it correctly in software is error-prone and was a recognized
problem in early theorem provers and language implementations.

**De Bruijn indices.** Introduced by Nicolaas de Bruijn in ["Lambda Calculus
Notation with Nameless Dummies" (1972)](https://www.win.tue.nl/automath/archive/pdf/aut029.pdf) specifically to give a *canonical*
representation of lambda terms in which alpha-equivalent terms are
syntactically identical. The name "de Bruijn index" (counting binders outward
from the use site) is the convention adopted here; de Bruijn himself used the
opposite convention in some papers. An alternative is *de Bruijn levels*,
which count inward from the outermost binder.

**Parallel substitution.** The use of an environment `Fin m -> Tm n` that maps
all variables simultaneously — rather than one at a time — is sometimes called
*parallel* substitutions or *vector* substitutions. The version we present
here is inspired by the Autosubst tool for working with de Bruijn indices in
the Rocq proof assistant, which itself was inspired by the ["Explicit
Substitutions"](https://www.cambridge.org/core/journals/journal-of-functional-programming/article/explicit-substitutions/C1B1AFAE8F34C953C1B2DF3C2D4C2125) of Abadi, Cardelli, Curien, and Lévy. (1991).

**Well-scoped de Bruijn terms.** Tracking the number of free variables at the
type level using a natural-number index appears in Altenkirch and Reus,
["Monadic Presentations of Lambda Terms Using Generalized Inductive Types"
(1999)](https://link.springer.com/chapter/10.1007/3-540-48168-0_32), and in Bird and Paterson, ["De Bruijn Notation as a Nested Datatype"
(1999)](https://www.cambridge.org/core/journals/journal-of-functional-programming/article/de-bruijn-notation-as-a-nested-datatype/D8BFA383FDA7EA3DC443B4C42A168F30). These papers inspired Kmett's [`bound`](https://hackage.haskell.org/package/bound) library for working with well-scoped
lambda calculus terms efficiently.

**Renamings and the termination problem.** The mutual recursion between
`applyE` and `up` (noted in Section 5) is a real obstacle in proof
assistants. The standard fix — define `applyRen` on renamings first, use it to
implement `up`, then build `applyE` on top — is described in, e.g., Benton,
Hur, Kennedy, and McBride, ["Strongly Typed Term Representations in Coq"
(2012)](https://link.springer.com/article/10.1007/s10817-011-9219-0). Exercise 4 asks you to implement this version.

---

## Exercises

**1. Writing terms.** Write the following closed terms in `Tutorial.Scoped.Scratch`. Work out the de Bruijn indices by hand before trying it in GHCi.

- `ex_fst :: Tm Z` — the projection `λp. match p with (x, y) → x`
- `ex_snd :: Tm Z` — the projection `λp. match p with (x, y) → y`
- `ex_s :: Tm Z` — the S combinator `λf. λg. λx. f x (g x)`

Pay attention to the variable ordering inside `Bind2`. In `MatchPair e (Bind2 body)`, `FZ` refers to the *second* pair component and `FS FZ` to the first.

---

**2. Weakening.** Consider the following function:

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
3. Add a case to `eval`. We have `let x = e in b` is a by-value let, so evaluate `e` first, then instantiate `b`

Check: is `Let e b` equivalent to `App (Lam b) e`? Do both evaluate the same way?

---

**4. Renamings.** A *renaming* is an environment that maps variables to
variables rather than terms:

```haskell
type Ren m n = Fin m -> Fin n
```

Define `applyRen :: Ren m n -> Tm m -> Tm n` by structural recursion, analogous to `applyE`. You will also need `upRen :: Ren m n -> Ren (S m) (S n)`.

Now observe: every renaming `r :: Ren m n` induces a substitution `Var . r :: Env m n`, and `applyRen r = applyE (Var . r)`.

The reason proof assistants define `applyRen` separately is that `applyRen` *is* structurally recursive (it produces variables, not terms), so it can be used to define `up` without the mutual recursion that troubles Agda and Rocq.


**5. Alternative representation of Env.** 

```haskell
data Vec n a where
  VNil :: Vec Z a
  (:::) :: a -> Vec n a -> Vec (S n) a
```

Can you implement substitution environments as length-indexed lists?

```
type Env m n = Vec m (Tm n)
```

First, define the lookup operation for accessing the definition of a particular index.

```
applyEnv :: Env m n -> Fin m -> Tm n
```

Now consider the other operations on environment.The implementation of `zeroE` and `(.:)` is straightforward. But what about the other operations, such as `idE`, `shiftE`, and the composition 
of two environments.

