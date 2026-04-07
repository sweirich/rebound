# Lecture 2: Where Do Well-Scoped Terms Come From?

## Modules referenced in this lecture

- [Tutorial.Scoped.Syntax](Tutorial/Scoped/Syntax.hs)
- [Tutorial.Scoped.Eval](Tutorial/Scoped/Eval.hs)
- [Tutorial.Scoped.ScopeCheck](Tutorial/Scoped/ScopeCheck.hs)
- [Tutorial.Scoped.Gen](Tutorial/Scoped/Gen.hs)
- [Tutorial.Named.Syntax](Tutorial/Named/Syntax.hs)
- [Tutorial.Named.Parser](Tutorial/Named/Parser.hs)
- [Tutorial.Named.Parser](Tutorial/Named/PP.hs)

## Overview and Goals

In Lecture 1 we represented terms using de Bruijn indices and implemented an
evaluator. We also saw that we could use `rebound` to implement substitution 
and alpha-conversion automatically for our well-scoped syntax.

How do we know that our evaluator is correct? We use property-based testing,
with Haskell's Quickcheck library (QC). With this approach, we state
properties of our definitions, and then test those properties extensively,
using randomly generated values.

However, to use Quickcheck we need to generate *well-scoped*
terms. Furthermore, if QC finds a bug, we want to see it in the most
convenient form: with indices replaced by variable names and converted to a
concise concrete syntax.

We also want to use this named representation for parsing: users do not want
to write their code using abstract syntax and de Bruijn indices — instead we
should let them use good-old-fashioned variable names and verify that those
names are in scope.

So that means that there are two sources of *well-scoped* terms that we want to 
consider:

1. **From the user** — the user writes a program in the *named* surface
   syntax; a *scope-checker* converts it to the de Bruijn representation.
2. **From the generator** — QuickCheck generates them directly using a
   size-directed generator that tracks the scope as it recurses.

This lecture covers both, and uses QuickCheck to ensure that we are treating 
variable names consistently.

The goals of this lecture are to:

- cover more practical aspects of working with de Bruijn indices: maintaining
  user-supplied variable names and generating well-scoped syntax trees

- show how to convert between syntax representations

- demonstrate the use of Quickcheck for property-based testing

---

## 1. Parsing and Pretty-printing scoped syntax

For simplicity, we will go through a named representation for parsing 
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


### The `Bind1` interface

`Bind1 Tm Tm n` is an abstract type defined in `Rebound.Bind.Local`, re-exported
by `Tutorial.Scoped.Syntax`. It is a specific instance of *pattern binding*:
the pattern is a single local name, stored alongside the body. The abstract
type enforces that you access the body only through the provided smart
constructors and accessors, never by pattern-matching on the internal
representation directly.

`Bind1 Tm Tm n` is also the abstract type; the library provides smart
constructors and accessors instead of exposing the data constructor:

| Function | Type | Description |
|---|---|---|
| `bind1` | `LocalName -> Tm (S n) -> Bind1 Tm Tm n` | package a body under a binder |
| `getLocalName` | `Bind1 Tm Tm n -> LocalName` | retrieve the stored name |
| `getBody1` | `Bind1 Tm Tm n -> Tm (S n)` | apply any delayed substitution and return the body |
| `instantiate1` | `Bind1 Tm Tm n -> Tm n -> Tm n` | open the binder by substituting a term |
| `unbindl1` | `Bind1 Tm Tm n -> (LocalName, Tm (S n))` | retrieve name and body together |

The `Bind2` interface is analogous, with `getLocalName2 :: Bind2 Tm Tm n -> Vec N2 LocalName`
returning a length-2 vector of names.


---

## 3. Quick check properties 

We can connect parsing and generation — via a chain of
transformations:

```

        inject            scope-check
Tm Z    ────────►  N.Tm   ──────────►  Either ScopeCheckError (Tm Z)


         inject            pretty-print          parse             scope-check
Tm Z    ────────►  N.Tm   ──────────►  String  ──────────► Either ParseError N.Tm  ──────────►  Either ScopeCheckError (Tm Z)
```

Two QuickCheck properties verify that our transformations are correct

```haskell
-- inject then project recovers the original term
prop_project_round_trip :: S.Tm Z -> Bool
prop_project_round_trip i =
    projectTm (injectTm i) == Right i

-- pretty-print then parse recovers the named term
prop_parse_round_trip :: S.Tm Z -> Bool
prop_parse_round_trip i =
    N.parseTm (show (N.test (injectTm i))) == Right (injectTm i)
```

However, to run QuickCheck properties we need a way to generate random `S.Tm Z`
values!  QuickCheck provides two central abstractions for property-based testing:

- **`Gen a`** — a probability distribution over values of type `a`.
  Combinators like `QC.sized`, `QC.oneof`, and `QC.elements`, and the 
  monad operations build generators compositionally.

- **`Arbitrary a`** — a typeclass that packages a default generator
  (`arbitrary :: Gen a`) and a shrinker (`shrink :: a -> [a]`):

  ```haskell
  class Arbitrary a where
      arbitrary :: Gen a
      shrink    :: a -> [a]
      shrink _  = []   -- default: no shrinking
  ```

  QuickCheck uses `arbitrary` to generate test inputs and `shrink` to
  reduce a failing case to a smaller one. 


The goal of this section is to implement  `Gen (S.Tm n)` — a generator
that only ever produces well-scoped de Bruijn terms, so that every
randomly generated term is a legitimate input to our properties.

The key idea is to carry the *scope* — the number of variables currently
in scope — as a runtime parameter for the generator.  When the generator recurses under a
binder it increments the scope, making the newly bound variable available.

## 4. A well-scoped generator for pure lambda calculus terms

Let's start with a simple well-scoped generator that targets only pure lambda
calculus terms (`Lam`, `App`, `Var`).  It is a good warm-up before tackling
the full language.

```haskell
genScopedPureLC :: forall n. SNatI n => QC.Gen (Tm n)
genScopedPureLC = QC.sized (go snat)
  where
    go :: forall n. SNat n -> Int -> QC.Gen (Tm n)
    go n sz | sz <= 1 = genBase n
    go n sz =
        let
          gen1 = bind1 @Tm <$> genLocalName <*> go (next n) (sz - 1)
          gen  = go n (sz `div` 2)
        in
          QC.oneof [genBase n, Lam <$> gen1, App <$> gen <*> gen]

    genBase :: forall n. SNat n -> Gen (Tm n)
    genBase SZ = return tmId
    genBase SS = Var <$> QC.elements Fin.universe
```

The generator is parameterized by the number of free variables in scope `n ::
Nat`, which is a *type*-level natural number.  To use this number at runtime
we need a *singleton*; the `SNatI n` constraint (explained below) provides
one.

The `go` function does the main work of generation. The first argument `n` is
the number of variables in scope, the second is `sz`, a size budget. During
property-based testing the `QC.sized` operation passes the current size budget
to the inner function `go` to generate progressively larger terms.  The `snat`
call converts the `SNatI n` constraint into an explicit `SNat n` value that
`go` can inspect and pass to recursive calls.

The local helper `go :: SNat n -> Int -> QC.Gen (Tm n)` carries both the
scope witness and the size budget:

- **Base case** (`sz <= 1`): delegate to `genBase`, which either returns
  `tmId` (the identity function `λx.x`, the smallest closed term) when the
  scope is empty (`SZ`), or picks a random variable from the scope (`SS`).
  Falling back to `tmId` rather than failing ensures the generator always
  produces a *closed* term when `n = Z`.

- **Recursive case**: three choices via `QC.oneof`:
  - `genBase n` — a variable or `tmId` (same as before, but available at any size)
  - `Lam <$> gen1` — wrap a binder; `gen1` generates the body in scope `S n`
    by calling `go (next n) (sz - 1)`.  The budget decreases by 1 (not halved)
    because a lambda chain `λx.λy.λz.…` is a linear sequence, not a tree.
  - `App <$> gen <*> gen` — apply two sub-terms, each in the *same* scope `n`
    but with budget `sz `div` 2` so that both branches together stay within budget.

- **Binders increment the scope**: `gen1` calls `go (next n) …`, where `next ::
  SNat n -> SNat (S n)` adds one to the runtime scope witness.  Inside the
  body of a `Lam`, the new variable `FZ` is automatically available because
  `Fin.universe` for `S n` includes `FZ`.

### Enumerating variables

Given `SNatI n`, we can list every valid variable in scope `n`:

```haskell
Fin.universe :: SNatI n => [Fin n]
```

For `n = S (S (S Z))` this gives `[FZ, FS FZ, FS (FS FZ)]` — all three
variables in scope.

Binders also need names for pretty-printing.  QuickCheck draws them from a
small pool:

```haskell
genLocalName :: QC.Gen LocalName
genLocalName = LocalName <$> QC.elements ["x", "y", "z", "w", "v", "u", "t", "s"]
```

This can produce name collisions (e.g. `"x"` can appear in nested
binders). However, this is not a problem:`injectTm` freshens names when
the same name is already in scope.  Correctness is unaffected because
`LocalName` equality ignores the stored string.

### Seeing the round trip in action

With this generator we can run our tests:

```
ghci> quickCheck (forAllShrinkShow genScopedPureLC shrinkScoped pp prop_project_round_trip)
+++ OK, passed 100 tests.
ghci> quickCheck (forAllShrinkShow genScopedPureLC shrinkScoped pp prop_parse_round_trip)
+++ OK, passed 100 tests.
```

We can inspect a single randomly generated term end-to-end:

```
ghci> t <- generate (genScopedPureLC :: Gen (S.Tm Z))
ghci> putStrLn (N.pp (injectTm t))
λ x1. case x1 of | Inj0 y2 -> (λ z3. z3) y2 | Inj1 w4 -> ()
ghci> projectTm (injectTm t) == Right t
True
```

The pretty-printer uses the `LocalName` values stored in the binders to
produce readable output.  The round-trip property confirms that
scope-checking the named term recovers exactly the original de Bruijn term.

## 4. Testing `eval` 

Now let's consider some properties that we might test for our evaluator.

### Big-step properties

The most basic property is that if a term evaluates to some result, then the 
result is a value.

```haskell

-- if a term evaluates, it produces a value
prop_evalVal :: Tm Z -> Property
prop_evalVal = \t ->
    counterexample ("term: " ++ pp t) $
    within 1000000 $
    case eval t of
        Just v -> 
            counterexample ("not a value: " ++ pp v) $
            property (isVal v)
        Nothing -> 
            discard
```

What else can we test? We can define a generalization of call-by-value evaluation called `reduce` that works with open terms. 

For closed terms it should agree with `eval`:

```haskell
prop_eval_reduce :: Tm Z -> Property
prop_eval_reduce = \t ->
    case eval t of
        Just v  -> reduce t == Just v
        Nothing -> discard
```

We also test that `reduce` produces an *inert* term (one that cannot step
further).  This property is checked at both the closed scope `Z` and the
open scope `S Z` (one free variable):

```haskell
prop_reduce_inert :: forall n. SNatI n => Tm n -> Property
prop_reduce_inert = \t ->
    case reduce t of
        Just v  -> property (isInert v)
        Nothing -> discard
```

### Small-step properties

Finally, we also develop a small-step version of `reduce`.
The small-step function `step` either returns a reduct or `Nothing` (the term
is already a value).  Two properties connect it to `eval` and `reduce`:

```haskell
-- for well-typed closed terms, step always reaches a value
prop_stepVal :: Tm Z -> Property
prop_stepVal = 
    let loop e =
          if isVal e then property True
          else case step e of
                 Nothing -> counterexample ("stuck at: " ++ pp e) (property False)
                 Just e' -> loop e'
    in loop

-- stepping preserves the final evaluation result
prop_evalStep :: Tm Z -> Property
prop_evalStep = \e ->
    case step e of
        Nothing -> property (isVal e)
        Just e' -> eval e == eval e'
```

## 5. Going further: A well-typed generator?

The well-scoped generator (`genScopedTm`) produces any structurally valid
term — but "well-scoped" does not mean "well-typed".  In an untyped
setting, terms like the ω combinator

```haskell
-- (λx. x x) (λx. x x)
omega :: Tm Z
omega = let self = Lam (bind1 (LocalName "x") (App (Var FZ) (Var FZ)))
        in App self self
```

are perfectly well-scoped and will be generated regularly.  Running
`eval omega` diverges: the evaluator loops forever.

This means properties tested with `genScopedTm` can hang rather than
fail, making it difficult to get useful QuickCheck output. This is a
real problem, because our well-scoped generator can produce such 
terms in practice.

```haskell
ghci> quickCheck (forAll genScopedPureLC prop_evalVal)
*** Failed! Timeout of 1000000 microseconds exceeded. (after 25 tests):
App (Lam (bind1 (Var 0))) (App (App (Lam (bind1 (App (Var 0) (Var 0)))) (Lam (bind1 (App (Var 0) (Var 0))))) (Lam (bind1 (Var 0))))
term: (\ x. x) ((\ u. u u) (\ v. v v) (\ x. x))
```

If we add shrinking, we can even see this smallest term.

```haskell
ghci> quickCheck (forAllShrinkShow genScopedPureLC shrinkScoped Tutorial.Top.pp prop_evalVal)
*** Failed! Timeout of 1000000 microseconds exceeded. (after 65 tests and 4 shrinks):
(\ x. x x) (\ s. s s)
term: (\ x. x x) (\ s. s s)
```

The solution is to add timeouts to our properties. However, if we do so, we end up discarding many cases.

```
prop_evalVal:
+++ OK, passed 1000 tests; 2133 discarded.
```

Alternatively, we can restrict generation to *well-typed* terms.  In the
simply-typed lambda calculus every term is strongly normalizing, so `eval` is
guaranteed to terminate on every well-typed input.

This also lets us state stronger type-soundness properties.  For example,
every well-typed closed term must evaluate to a value:

```haskell
prop_eval_exists_Val :: Tm Z -> Property
prop_eval_exists_Val = \t ->
    case eval t of
        Just v  -> property (isVal v)
        Nothing -> property False   -- well-typed terms must not get stuck
```

And the `step` function *must* produces a value for closed terms.

```haskell

-- | the step 
prop_stepVal :: Tm Z -> Property
prop_stepVal e =
    let loop e =
          if isVal e then property True
          else case step e of
             Nothing ->
                counterexample ("stuck at: " ++ pp e) $
                property False
             Just e' -> loop e'
    in within 1000000 $ loop e
```

These properties hold by type soundness (progress + preservation) and
would not be testable with the well-scoped generator alone.

## 6. Two dimensions of generation

Therefore, we can define a generator for our syntax that is parameterized over two orthogonal dimensions:

```haskell
data Constraint = Scoped | Typed
data Language   = PureLC | Full
```

- **`Scoped`** — generate any well-scoped term; types are ignored.
- **`Typed`** — generate a well-typed term by first picking a random type and context, then generating a term of that type.
- **`PureLC`** — only use `Lam`, `App`, and `Var` (the pure lambda calculus).
- **`Full`** — also include `Unit`, `Pair`, `MatchPair`, `Inj`, `MatchUnit`, and `MatchSum`.


For the `Typed` constraint, `genTypedTm` works by type-directed synthesis.  At
each recursive call it has a *target type* and a *typing context* (a vector
mapping each de Bruijn index to its type), and it only produces terms that
have exactly that type.

The high-level strategy is:

- **Introduction forms** are selected by the *target type*.  If the goal is
  `a :-> b`, generate a `Lam` whose body is generated at type `b` in an
  extended context.  If the goal is `a :* b`, generate a `Pair`.  And so on.

- **Elimination forms** (function application, pattern matching) require an
  *arbitrary* intermediate type, generated fresh for that sub-call.  For
  example, to generate an `App` targeting type `b`, first pick a random
  argument type `a`, then generate a function of type `a :-> b` and an
  argument of type `a`.

- **Variables** are filtered by type: only those indices whose context entry
  matches the target type are offered as candidates.

- **Fallback**: when no introduction or variable candidate applies (e.g. at
  size 0 targeting a function type with no matching variable), the generator
  falls back to `Unit`.

The top-level call also picks a random context and a random target type
before calling `genTypedTm`, so the resulting term may have free variables
with known types — or be closed if the context is empty.

### Shrinking

Random generation also requires shrinking. Because we have two different constraints for the terms that we generate, we need two different shrinking 
functions: `shrinkScoped` and `shrinkTyped`. 

Both shrinking function take a counter example (a term) and produce a list 
of smaller terms that satisfy the same constraint. For `shrinkScoped`, the constraint is that the smaller terms must have the same scope as the original term. The type system guarantees this constraint automatically. For `shrinkTyped` the smaller terms must still be well-typed, but because we are not tracking types in the type system, they may not have the *same* type.

## 7. Historical Notes


**Scope checking as a compiler pass.** The idea of converting named surface syntax to an internal nameless or index-based form is standard in compiler design. Early Lisp interpreters used association lists (`alist`) to map symbol names to values at runtime — the direct ancestor of the `[(String, Fin n)]` context used in `projectTmWith`. In modern compilers this conversion is a distinct front-end pass, often called *name resolution* or *scope analysis*, that runs after parsing and before type checking, and uses a more efficient data structure.

**Singleton types and `SNatI`.** To use a type-level natural number `n :: Nat` at runtime — e.g., to enumerate `Fin n` — one needs a *singleton*: a runtime value that mirrors the type. Simulating this in Haskell was described by McBride ("Faking It: Simulating Dependent Types in Haskell", 2002) and later systematized in the `singletons` library (Eisenberg and Weirich, 2012). The `SNatI` typeclass and `SNat` type used by `genTm` follow this pattern.

**QuickCheck.** Koen Claessen and John Hughes introduced QuickCheck in "QuickCheck: A Lightweight Tool for Random Testing of Haskell Programs" (2000). Property-based testing is now widely used across languages. The technique of generating *well-scoped* (or well-typed) terms directly — rather than generating strings and parsing them — avoids a large class of trivially-failing test cases and is the standard approach for testing language implementations.

**Well-scoped and well-typed term generation.** Generating terms directly in an indexed representation — rather than generating strings and filtering out ill-scoped ones — was popularized in the property-based testing literature by Pałka et al. ("Testing an Optimising Compiler by Generating Random Lambda Terms", 2011), who used it to find bugs in GHC.  Type-directed generation (producing only well-typed terms) is the natural extension: it avoids both scope errors and divergence, and was used by Dénès et al. and others for testing type-preserving compilers and proof assistants.

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

(a) Evaluate the following in GHCi and explain the result:

```haskell
S.Lam (S.bind1 (S.LocalName "x") (S.Var FZ))
  ==
S.Lam (S.bind1 (S.LocalName "y") (S.Var FZ))
```

(b) What would go wrong with `prop_project_round_trip` if `LocalName` had a *real* `Eq` instance that distinguished `"x"` from `"y"`? 

(c) QuickCheck generates names from the pool `["x","y","z","w","v","u","t","s"]`, so the same name can appear in nested binders.  Give an example generated term where `freshen` is needed during `injectTm`, and show what name it would produce.

---

**4. Extending `genTm`.** After adding `Let` to the language (Exercise 3 in Lecture 1 and Exercise 2 above), extend `genTm` in `Tutorial.Scoped.Gen` to also generate `let`-expressions.

```haskell
-- In the Full branch of gens inside genTm:
, Let <$> gen <*> gen1
```

where `gen1 = bind1 @Tm <$> genLocalName <*> genTm l (next n) sz'`.

- Why is `gen1` the right generator for the binder part of `Let`?
- What scope does the body of the `let` run in?  How does this differ from `App`?
- Check that `prop_project_round_trip` still passes after this change.

---

**5. An open-term round trip.** `projectTmWith` and `injectTmWith` work on open terms too.  Write a QuickCheck property analogous to `prop_project_round_trip` for terms with one free variable (`Tm (S Z)`), and test it:

```haskell
prop_project_round_trip_open :: S.Tm (S Z) -> Bool
prop_project_round_trip_open t =
    -- hint: use projectTmWith and injectTmWith with a suitable initial context
    undefined
```

You will need to choose a name for the free variable and pass it to `injectTmWith`.  Likewise, you will need to prime `projectTmWith` with an association list that maps that name to `FZ`.

- What initial `Vec (S Z) String` do you pass to `injectTmWith`?
- What initial `[(String, Fin (S Z))]` do you pass to `projectTmWith`?
- Does the choice of name matter?  Why or why not?

**6. Substitution laws.** State and test the following equational laws as QuickCheck properties on `Tm Z`:

- *Identity*: `applyE idE t == t`
- *Composition*: `applyE f (applyE g t) == applyE (compE f g) t`
- *Instantiate-shift*: `instantiate1 (Bind1 (weaken t)) u == t` for any `t u :: Tm Z`

For the composition law, use concrete environments, e.g. `g = idE` and `f = idE`, or build simple environments with `(.:)`. Can you find a counterexample to any of these properties if you get the implementation of `lift` wrong?

**7. More efficient scope checking** Instead of using the type `[(String, Var n)]` to map variable names to indices, design a more efficient data structure. This data structure should allow logarithmic lookup of names and constant time insertion of a new binding (while incrementing the indices of previous bindings).

If you would like a hint: check out the "Skewed Substitutions" described in this [blog post](https://mathisbd.github.io/blog/esubstitutions.html).


