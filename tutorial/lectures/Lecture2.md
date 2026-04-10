# Lecture 2: Pattern Binding (plus scope checking)

## Modules referenced in this lecture

- [Tutorial.Scoped.Syntax](https://github.com/sweirich/rebound/blob/main/tutorial/main/src/Tutorial/Scoped/Syntax.hs)
- [Tutorial.Scoped.ScopeCheck](https://github.com/sweirich/rebound/blob/main/tutorial/main/src/Tutorial/Scoped/ScopeCheck.hs)
- [Tutorial.Named.Syntax](https://github.com/sweirich/rebound/blob/main/tutorial/main/src/Tutorial/Named/Syntax.hs)
- [Tutorial.Named.Parser](https://github.com/sweirich/rebound/blob/main/tutorial/main/src/Tutorial/Named/Parser.hs)
- [Tutorial.Named.Parser](https://github.com/sweirich/rebound/blob/main/tutorial/main/src/Tutorial/Named/PP.hs)

## Overview and Goals

In Lecture 1 we represented terms using de Bruijn indices and implemented an
evaluator.

But what about more sophisticated languages, which might include, say, pattern
matching?

And, when working on a real implementation, we want to be able to parse and
pretty-print our AST. While we won't cover parsing and pretty-printing in
general in this tutorial, we do need to consider how well scoped terms
interact with these operations. In particular, if a user writes their code
with explicit names, we need to ensure that all names are in scope. Similarly,
to print code nicely, we want to preserve the names that the user originally
wrote.

The goals of this lecture are to:

- cover more practical aspects of working with de Bruijn indices: maintaining
  user-supplied variable names and generating well-scoped syntax trees

- demonstrate pattern binding and sophisticated use of the `rebound` library


## 1. Parsing and pretty-printing scoped syntax

For simplicity, we  go through a named representation for parsing 
and printing.  In other words, to create scoped syntaxt, we divide the 
work into parsing raw strings into a representation that uses strings
for variable names, and a separate *projection* function that performs
scope checking. In this process, two sorts of failures could occur: 
perhaps the string doesn't parse, or perhaps one of the variables is 
out of scope.  This process also resolves *shadowing*, where the name of 
one variable hides another. 

             parse                      project
    String ------------> Named Syntax --------------> Scoped Syntax 

The inverse of parsing is pretty printing. For clarity, as above we do 
this in two stages. First we `inject` the scoped syntax into the named 
syntax, replacing all indices with strings. Then we use a pretty printer 
for the named syntax.
 
     inject                pretty-print
    Scoped Syntax -------> Named Syntax -------------> String

Below, and in the `ScopeCheck` module, we use `S` to refer to the
`Tutorial.Scoped.Syntax` module and `N` to refer to the
`Tutorial.Named.Syntax` module.


## 2. Remembering user supplied names

Where do the names come from during pretty printing? Of course, we can just 
make up names, making sure that we always use new ones. However, that can lead 
to confusion---we'd like to keep any user-supplied names if possible. 

Therefore, we use a simple type, called `LocalName` to remember such names for
printing, while making sure that they do not interfere with alpha-equivalence.

When a user writes `λx. x` and we scope-check it, we produce

```haskell
S.Lam (S.bind1 (S.LocalName "x") (S.Var FZ))
```

The string `"x"` is stored inside the binder as a `LocalName`.  When later printed
the printed output reads `λ x. x`.

### The `LocalName` type

A local name is just a wrapper for a string. 

```haskell
newtype LocalName = LocalName { name :: String }

instance Eq LocalName where
    x1 == x2 = True   -- all LocalNames are equal!
```

The deliberately trivial `Eq` instance means that two binders with
*different* user names are still considered equal as long as their bodies
are equal under de Bruijn comparison.  This gives the correct notion of
α-equivalence for free:


```haskell
--  λ x. x
t1 = S.Lam (S.bind (S.LocalName "x") (S.Var FZ))
--  λ y. y
t2 = S.Lam (S.bind (S.LocalName "y") (S.Var FZ))
-- >>> t1 == t2
-- True
```


### The `Local.Bind` interface

`Bind Tm Tm n` is a type defined in `Rebound.Bind.Local`.  It is a
specific instance of *pattern binding*: the pattern is a single local name,
stored alongside the body. The abstract type enforces that you access the body
only through the provided smart constructors and accessors, never by
pattern-matching on the internal representation directly.

`Bind Tm Tm n` is also an *abstract* type; the library provides smart
constructors and accessors instead of exposing the data constructor:

| Function | Type | Description |
|---|---|---|
| `bind1` | `LocalName -> Tm (S n) -> Bind1 Tm Tm n` | package a body under a binder |
| `getLocalName` | `Bind1 Tm Tm n -> LocalName` | retrieve the stored name |
| `getBody1` | `Bind1 Tm Tm n -> Tm (S n)` | apply any delayed substitution and return the body |
| `instantiate1` | `Bind1 Tm Tm n -> Tm n -> Tm n` | open the binder by substituting a term |
| `unbindl1` | `Bind1 Tm Tm n -> (LocalName, Tm (S n))` | retrieve name and body together |


## 3. General pattern binding

In our simple language (from module `Tutorial.Scoped.Scratch`), we had
separate constructors for pattern matching unit, pair and sum values. We would
like to combine these into a single `Match` expression that allows nested
patterns. This requires a pattern datatype and a way to bind the variables
introduced by a pattern in the branch body.

### The `Pat` datatype

```haskell
data Pat (m :: Nat) where
    PVar  :: LocalName -> Pat N1
    PUnit :: Pat N0
    PPair :: Pat m1 -> Pat m2 -> Pat (m2 + m1)
    PInj  :: Int -> Pat m -> Pat m
```

The index `m` is the number of variables *bound* by the pattern, tracked at
the type level.  `PVar` binds one variable, `PUnit` binds none, and `PPair`
binds the sum of its sub-pattern counts.  Note the order in the type of
`PPair`: variables from the *right* sub-pattern (`m2`) are innermost
(have the smaller de Bruijn indices), so they come first in the sum `m2 + m1`.
`PInj` is a tag for injection patterns and passes the binding count through
unchanged.

### The `Branch` datatype and `Pat.Bind`

```haskell
data Branch (n :: Nat) where
    Branch :: Pat.Bind Tm Tm (Pat m) n -> Branch n
```

`Pat.Bind Tm Tm (Pat m) n` is the pattern-binding abstraction provided by
`Rebound.Bind.Pat`.  It pairs a pattern of type `Pat m` with a body of type
`Tm (m + n)`, where the body's first `m` free variables are the ones the
pattern binds.  The existential over `m` is hidden inside `Branch`, so
callers do not need to know the pattern's arity statically.

The key API for `Pat.Bind`:

| Function | Type | Description |
|---|---|---|
| `Pat.bind` | `Pat m -> Tm (m + n) -> Pat.Bind Tm Tm (Pat m) n` | construct a branch |
| `Pat.getPat` | `Pat.Bind Tm Tm (Pat m) n -> Pat m` | extract the pattern |
| `Pat.getBody` | `Pat.Bind Tm Tm (Pat m) n -> Tm (m + n)` | extract the body |
| `Pat.instantiate` | `Pat.Bind Tm Tm (Pat m) n -> Env Tm m n -> Tm n` | open by substituting an environment |

### The `Sized` instance

The library needs to recover `m` at runtime (e.g. to know how many variables
to substitute).  The `Sized` instance supplies this:

```haskell
instance Sized (Pat m) where
    type Size (Pat m) = m

    size :: Pat m -> SNat (Size (Pat m))
    size (PVar _)      = s1
    size PUnit         = s0
    size (PPair p1 p2) = sPlus (size p2) (size p1)
    size (PInj _ p)    = size p
```

`sPlus (size p2) (size p1)` mirrors the type `m2 + m1` from the `PPair`
constructor, keeping the runtime value and the type-level index in sync.

### Building a branch

To construct a `Match` branch, first build a pattern and then wrap the body
with `Pat.bind`:

```haskell
-- match a pair, binding x (index 1) and y (index 0)
pairBranch :: Branch n
pairBranch =
    Branch (Pat.bind (PPair (PVar "x") (PVar "y"))
                     (Pair (Var (FS FZ)) (Var FZ)))
```

Inside the body, `FZ` refers to the rightmost pattern variable (`y`) and
`FS FZ` refers to the leftmost (`x`), consistent with the `m2 + m1`
ordering.


## 4. Alpha-equivalence for branches and patterns

We cannot derive `Eq` automatically for `Pat` or `Branch` because of the
dependent index `m`.  Comparing two patterns may reveal that they bind
*different* numbers of variables; in that case they are definitely unequal,
and we also cannot compare their bodies (which would have different types).

### `PatEq`: heterogeneous pattern equality

`rebound` provides a typeclass for this:

```haskell
class PatEq p1 p2 where
    patEq :: p1 -> p2 -> Maybe (Size p1 :~: Size p2)
```

`patEq p1 p2` returns `Just Refl` if the patterns have the same structure
(and therefore bind the same number of variables), or `Nothing` otherwise.
The `Refl` proof lets the caller unify the two `m` indices and proceed with
body comparison.

The instance for our `Pat` type recurses structurally:

```haskell
instance PatEq (Pat m1) (Pat m2) where
  patEq (PPair p1 p2) (PPair p1' p2') = do
    Refl <- patEq p1 p1'
    Refl <- patEq p2 p2'
    return Refl
  patEq (PVar x)  (PVar y)            = return Refl
  patEq PUnit     PUnit               = return Refl
  patEq (PInj i p) (PInj j p') | i == j = patEq p p'
  patEq _ _                           = Nothing
```

Notice that `PVar` patterns are always considered equal regardless of the
stored name—consistent with `LocalName`'s trivial `Eq` instance.

### `Eq` for `Pat` and `Branch`

With `patEq` in hand, the `Eq (Pat m)` instance is a one-liner:

```haskell
instance Eq (Pat m) where
  p1 == p2 = Maybe.isJust (patEq p1 p2)
```

For `Branch`, the `m` index is existentially hidden, so we must recover it
at runtime using `size` and then call `testEquality` on the resulting
`SNat` values before we can compare bodies:

```haskell
instance Eq (Branch n) where
  Branch b1 == Branch b2 =
    case testEquality (size (Pat.getPat b1)) (size (Pat.getPat b2)) of
        Just Refl -> b1 == b2
        Nothing   -> False
```

If the sizes differ the branches are unequal; if they agree, `Refl` unifies
the `m` indices and the library's derived `Eq` instance for `Pat.Bind` does
the rest.


## 5. Evaluating pattern matching

The evaluator in `Tutorial.Scoped.Eval` provides three reduction strategies
and uses pattern matching throughout.

### Big-step evaluation (`eval`)

`eval :: Tm Z -> Maybe (Tm Z)` evaluates closed terms to values.  The
interesting cases are application and match:

```haskell
eval (App m n) = do
    mv <- eval m
    nv <- eval n
    case mv of
        Lam b -> eval (instantiate1 b nv)
        _     -> Nothing
eval (Match e brs) = do
    v <- eval e
    br <- findBranch v brs
    eval br
```

### Pattern matching: `patternMatch` and `findBranch`

```haskell
patternMatch :: Pat m -> Tm n -> Maybe (Env Tm m n)
```

`patternMatch` compares a pattern against a value and, on success, returns an
*environment* `Env Tm m n` — a mapping from the `m` pattern variables to
`Tm n` values.

| Case | Result |
|---|---|
| `PVar _` against any value `v` | `Just (oneE v)` — a single-entry environment |
| `PUnit` against `Unit` | `Just zeroE` — the empty environment |
| `PPair p1 p2` against `Pair v1 v2` | environments concatenated with `.++` |
| `PInj i p` against `Inj j v` when `i == j` | recurse on `p` and `v` |
| anything else | `Nothing` |

The pair case concatenates the two sub-environments, placing `p2`'s
variables innermost (lower indices), matching the `m2 + m1` convention from
the `PPair` type:

```haskell
patternMatch (PPair p1 p2) (Pair v1 v2) = do
    env1 <- patternMatch p1 v1
    env2 <- patternMatch p2 v2    -- p2's vars are innermost
    withSNat (size p2) $ return (env2 .++ env1)
```

`findBranch` iterates through the branch list and, for the first matching
branch, uses `Pat.instantiate` to substitute the environment into the body:

```haskell
findBranch :: Tm n -> [Branch n] -> Maybe (Tm n)
findBranch _ [] = Nothing
findBranch e (Branch b : rest) =
    case patternMatch (Pat.getPat b) e of
        Just r  -> Just (Pat.instantiate b r)
        Nothing -> findBranch e rest
```

## 6. Historical Notes


**Scope checking as a compiler pass.** The idea of converting named surface syntax to an internal nameless or index-based form is standard in compiler design. Early Lisp interpreters used association lists (`alist`) to map symbol names to values at runtime — the direct ancestor of the `[(String, Fin n)]` context used in `projectTmWith`. In modern compilers this conversion is a distinct front-end pass, often called *name resolution* or *scope analysis*, that runs after parsing and before type checking, and uses a more efficient data structure.

**Singleton types and `SNatI`.** To use a type-level natural number `n :: Nat` at runtime — e.g., to enumerate `Fin n` — one needs a *singleton*: a runtime value that mirrors the type. Simulating this in Haskell was described by McBride ("Faking It: Simulating Dependent Types in Haskell", 2002) and later systematized in the `singletons` library (Eisenberg and Weirich, 2012). The `SNatI` typeclass and `SNat` type used by `genTm` follow this pattern.


---

## Exercises

**1. Tracing `projectTmWith`.** Manually trace through the following call, writing down the association list at each recursive step and the final de Bruijn term produced:

```haskell
projectTm (N.Lam "x" (N.Lam "y" (N.Var "x")))
```

- What is the association list when we recurse into the body of the outer `λx.`?
- What is the association list when we recurse into the body of the inner `λy.`?
- What is the final `S.Tm Z` that is returned?

Now do the same for:

```haskell
projectTm (N.Case (N.Var "p")
    [(N.Pair [N.Var "x", N.Var "y"], N.Var "x")])
```

Which variable maps to `FZ` inside the body — `x` or `y`?  Why?

---

**2. Extending the conversions with `let`.** Extend `projectTmWith` and `injectTmWith` in `Tutorial.Scoped.ScopeCheck` to handle a `let`-expression.  Assume you have already added `Let :: Tm n -> Bind1 Tm Tm n -> Tm n` to `Tutorial.Scoped.Syntax` and `N.Let :: String -> N.Tm -> N.Tm -> N.Tm` to the named syntax.

- How does the treatment of `let` compare to `lam` in each direction?

- Does `prop_project_round_trip` still pass after this change?  Why or why not?

---

**3. `LocalName` and α-equivalence.** The `Eq` instance for `LocalName` makes every two `LocalName` values equal:

```haskell
instance Eq LocalName where
    x1 == x2 = True
```

Evaluate the following in GHCi and explain the result:

```haskell
S.Lam (S.bind1 (S.LocalName "x") (S.Var FZ))
  ==
S.Lam (S.bind1 (S.LocalName "y") (S.Var FZ))
```




