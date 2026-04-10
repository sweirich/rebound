# Lecture 3: Property-Based Testing (PBT) with well-scoped and well-typed terms

## Modules referenced in this lecture

- [Tutorial.Scoped.Eval](https://github.com/sweirich/rebound/blob/main/tutorial/main/src/Tutorial/Scoped/Eval.hs)

- [Tutorial.Scoped.Gen](https://github.com/sweirich/rebound/blob/main/tutorial/main/src/Tutorial/Scoped/Gen.hs)


## Overview and Goals

How do we know that the code that we have written so far is correct? We could
write a bunch of unit tests, but it is more fun to use property-based testing,
with Haskell's Quickcheck library (QC). With this approach, we define
*properties* of our definitions, and then use Quickcheck test those properties
extensively with randomly generated values.

In this lecture, we will talk about how to generate random well-scoped (and
well-typed) terms and use them to test the parser/pretty printer and evaluator
that we defined in the previous lecture.

## 1. Quick check properties for parsing and pretty printing.

Re call that we can connect parsing and generation — via a chain of
transformations:

```

        inject            scope-check
Tm Z    ────────►  N.Tm   ──────────►  Either ScopeCheckError (Tm Z)


         inject            pretty-print          parse             scope-check
Tm Z    ────────►  N.Tm   ──────────►  String  ──────────► Either ParseError N.Tm  ──────────►  Either ScopeCheckError (Tm Z)
```

Two QuickCheck properties (`defined in Tutorial.Scoped.ScopeCheck`) verify that our transformations are correct:

```haskell
-- inject then project recovers the original term
prop_project_round_trip :: S.Tm Z -> Bool
prop_project_round_trip i =
    projectTm (injectTm i) == Right i

-- pretty-print then parse recovers the named term

-- | Pretty-printing a term and parsing it back yields the original named term.
prop_parse_round_trip :: S.Tm Z -> Bool
prop_parse_round_trip i =
   parse (pp i) == Right i
```

However, to run QuickCheck properties we need a way to generate random closed
values!  

## Quickcheck crash course

QuickCheck provides two central abstractions for property-based testing:

- **`Gen a`** — a type for generators of values of type `a`.
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


## 2. A well-scoped generator for pure lambda calculus terms

Let's start with a simple well-scoped generator that targets only pure lambda
calculus terms (`Lam`, `App`, `Var`).  It is a good warm-up before tackling
the full language.

Therefore we want to implement `Gen (S.Tm n)` — a generator that only ever
produces well-scoped de Bruijn terms, so that every randomly generated term is
a legitimate input to our properties.

The key idea is to carry the *scope* — the number of variables currently in
scope — as an implicit runtime parameter for the generator.  When the
generator recurses under a binder it increments the scope, making the newly
bound variable available.

The `Fin.universe` operation enumerates all indices from `0` to `n-1`. Then 
the `QC.elements` operation picks a random one. However, this only makese sense
if there is at least one free variable in scope. If `n` is zero, then we don't 
have any variables to pick from. Therefore, we just return the smallest 
closed term.

```haskell
-- At small size generate either a variable or "\x.x" depending on scope
genBase :: forall n. SNat n -> Gen (Tm n) 
genBase SZ = return tmId
genBase SS = QC.elements (map Var Fin.universe)
```

```haskell
genScopedPureLC :: forall n. SNatI n => QC.Gen (Tm n)
genScopedPureLC = QC.sized go
    where
      go :: forall n. SNatI n => Int -> QC.Gen (Tm n)
      go sz | sz <= 1 = genBase snat
      go sz = 
         let
           -- generate a random name and increment the number of free variables
           gen1 = bind <$> genLocalName <*> go (sz - 1)

           -- recursive calls for App divide size by two
           gen  = go (sz `div` 2)
         in 
         QC.oneof [genBase snat, Lam <$> gen1, App <$> gen <*> gen ]
```

The generator is parameterized by the number of free variables in scope `n ::
Nat`, which is a *type*-level natural number.  To use this number at runtime
we need a *singleton* provided by the `SNatI n`.

The `go` function does the main work of generation. The first argument `n` is
the number of variables in scope, the second is `sz`, a size budget. During
property-based testing the `QC.sized` operation passes the current size budget
to the inner function `go` to generate progressively larger terms.  The `snat`
call converts the `SNatI n` constraint into an explicit `SNat n` value that
`go` can inspect and pass to recursive calls.

The local helper `go :: SNat n -> Int -> QC.Gen (Tm n)` carries both the
scope witness and the size budget. When the size is larger than one,
there are three choices for generation via `QC.oneof`:

- `genBase n` — a variable or `tmId` (same as before, but available at any size)
- `Lam <$> gen1` — wrap a binder; `gen1` generates the body in scope `S n`
    by calling `go (sz - 1)`.  The budget decreases by 1 (not halved)
    because a lambda chain `λx.λy.λz.…` is a linear sequence, not a tree.
- `App <$> gen <*> gen` — apply two sub-terms, each in the *same* scope `n`
   but with budget `sz ``div`` 2` so that both branches together stay within budget.

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

## 3. Seeing the round trip in action

With this generator we can run our tests:

```
ghci> import Tutorial.Scoped.ScopeCheck
ghci> import Tutorial.Scoped.Gen
ghci> import Test.QuickCheck
ghci> quickCheck (forAllShrinkShow genScopedPureLC shrinkScoped pp prop_project_round_trip)
+++ OK, passed 100 tests.
ghci> quickCheck (forAllShrinkShow genScopedPureLC shrinkScoped pp prop_parse_round_trip)
+++ OK, passed 100 tests.
```

The `forAllShrinkShow` instructs quickcheck which scoped generator, scoped shrinker, and 
pretty printer to use when testing.

The round-trip properties confirm that scope-checking the named term recovers
exactly the original de Bruijn term.

## 4. Testing `eval` 

Now let's consider some properties that we might test for our evaluator.

### Big-step properties

The most basic property is that if a term evaluates to some result, then the 
result is a value. We can write this test as follows:

```haskell

-- if a term evaluates, it produces a value
prop_evalVal :: Tm Z -> Property
prop_evalVal = \t ->
    discardAfter 1000000 $
    case eval t of
        Just v -> 
            counterexample ("not a value: " ++ pp v) $
            property (isVal v)
        Nothing -> 
            discard
```

We can strengthen this property by requiring the evaluation to produce a 
result. This property only holds for well-typed terms. 

```haskell

-- all terms evaluate to values
prop_evalVal :: Tm Z -> Property
prop_evalVal = \t ->
    discardAfter 1000000 $
    case eval t of
        Just v -> 
            counterexample ("not a value: " ++ pp v) $
            property (isVal v)
        Nothing -> 
            property False
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

## 6. Historical Notes

**QuickCheck.** Koen Claessen and John Hughes introduced QuickCheck in "QuickCheck: A Lightweight Tool for Random Testing of Haskell Programs" (2000). Property-based testing is now widely used across languages. The technique of generating *well-scoped* (or well-typed) terms directly — rather than generating strings and parsing them — avoids a large class of trivially-failing test cases and is the standard approach for testing language implementations.

**Well-scoped and well-typed term generation.** Generating terms directly in an indexed representation — rather than generating strings and filtering out ill-scoped ones — was popularized in the property-based testing literature by Pałka et al. ("Testing an Optimising Compiler by Generating Random Lambda Terms", 2011), who used it to find bugs in GHC.  Type-directed generation (producing only well-typed terms) is the natural extension: it avoids both scope errors and divergence, and was used by Dénès et al. and others for testing type-preserving compilers and proof assistants.


## Exercises


**1. Extending `genTm`.** After adding `Let` to the language (Exercise 3 in Lecture 1 and Exercise 2 above), extend `genTm` in `Tutorial.Scoped.Gen` to also generate `let`-expressions.

```haskell
-- In the Full branch of gens inside genTm:
, Let <$> gen <*> gen1
```

where `gen1 = bind1 @Tm <$> genLocalName <*> genTm l (next n) sz'`.

- Why is `gen1` the right generator for the binder part of `Let`?
- What scope does the body of the `let` run in?  How does this differ from `App`?
- Check that `prop_project_round_trip` still passes after this change.

---

**2. An open-term round trip.** `projectTmWith` and `injectTmWith` work on open terms too.  Write a QuickCheck property analogous to `prop_project_round_trip` for terms with one free variable (`Tm (S Z)`), and test it:

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

**3. Substitution laws.** State and test the following equational laws as QuickCheck properties on `Tm Z`:

- *Identity*: `applyE idE t == t`
- *Composition*: `applyE f (applyE g t) == applyE (compE f g) t`
- *Instantiate-shift*: `instantiate1 (Bind1 (weaken t)) u == t` for any `t u :: Tm Z`

For the composition law, use concrete environments, e.g. `g = idE` and `f = idE`, or build simple environments with `(.:)`. Can you find a counterexample to any of these properties if you get the implementation of `lift` wrong?


**4. Full reduction (normalization).** The `reduce` function in `Tutorial.Scoped.Eval` is a *weak* reducer: the `Lam` case returns the lambda unchanged without looking inside the body. Implement *full* reduction (also called *normalization*), which reduces everywhere — including under binders:

```haskell
normalize :: Tm n -> Maybe (Tm n)
normalize = _
```

Hints:

- The key new case is `Lam b`. Use `unbindl1 b` to extract the stored local name and the body (of type `Tm (S n)`). Recursively normalize the body, then re-package it with `bind1`. Because `Tm (S n)` is an *open* term, the recursive call is well-typed without any extra constraint.
- For `App`, first normalize both sub-terms. If the function normalizes to `Lam b` and the argument to `nv`, perform the beta step with `instantiate1 b nv` and normalize the result. If the function is inert, return the application of the normalized sub-terms.
- The other cases (`Pair`, `Inj`, `MatchSum`, `MatchPair`, `MatchUnit`) follow the same pattern as in `reduce`, but calling `normalize` recursively instead of `reduce`, and also normalizing inside constructor arguments.
- `normalize` should agree with `reduce` on terms that contain no redexes under binders. State and test this as a QuickCheck property on `Tm (S Z)`:

  ```haskell
  prop_normalize_reduce :: Tm (S Z) -> Property
  prop_normalize_reduce t = ...
  ```

  *Hint*: find a predicate `noLambdaRedex :: Tm n -> Bool` that holds when there are no beta redexes inside any lambda body, and use `QC.classify` to report what fraction of generated terms satisfy it.

- Define `isNormal :: Tm n -> Bool` that holds when a term contains no beta redexes *anywhere* (including under binders). Then state and test:

  ```haskell
  prop_normalize_normal :: Tm (S Z) -> Property
  prop_normalize_normal t =
      case normalize t of
          Just nf -> property (isNormal nf)
          Nothing -> discard
  ```

- On closed terms, does `normalize t` succeed exactly when `eval t` succeeds? State this as a property and test it. Does it hold for well-scoped terms? For well-typed terms? Explain any discrepancies you observe.
