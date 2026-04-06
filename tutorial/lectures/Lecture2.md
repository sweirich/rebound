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
evaluator. 

How do we know that our evaluator is correct? We use property-based testing,
of course.

However, to using Haskell's Quickcheck library we need to generate
well-scoped terms. If QC finds a bug, we want to convert the term to a named
representation for printing. We will also want to use this named representation for
parsing: users do not want to write their code using de Bruijn indices —
instead we should let them use good-old-fashioned variable names and verify
that those names are in scope.

So that means that there are two sources of *well-scoped* terms that we want to 
consider:

1. **From the user** — the user writes a program in the *named* surface
   syntax; a *scope-checker* converts it to the de Bruijn representation.
2. **From the generator** — QuickCheck generates them directly using a
   size-directed generator that tracks the scope as it recurses.

This lecture covers both, and uses QuickCheck to ensure that we are treating 
variable names consistently.

The goals of this lecture are to:

- cover more practical aspects of working with de Bruijn indices: maintaining user-supplied variable names and generating well-scoped syntax trees

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

Therefore, we use a simple type, called `LocalName` to remember such names for printing, while making sure that they do not interfere with alpha-equivalence.

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

`Bind1 Tm Tm n` is an abstract type; the library provides smart
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







### The `Arbitrary LocalName` instance

QuickCheck generates random names from a small pool:

```haskell
genLocalName :: QC.Gen LocalName
genLocalName = LocalName <$> QC.elements ["x", "y", "z", "w", "v", "u", "t", "s"]
```

This intentionally produces name collisions (e.g. `"x"` can be generated
multiple times in one term), which is why `injectTm` must be able to
freshen names before extending the context.

---

## 5. Generating Arbitrary Well-Scoped Terms

The `Arbitrary (Tm n)` instance for the scoped representation does not go
through parsing: it generates de Bruijn terms directly, using a *scope*
parameter to know which variables are available.

### The `SNatI` typeclass

The scope `n :: Nat` is a type-level natural number.  To *use* it at runtime
(e.g. to enumerate all variables in scope), we need a singleton:

```haskell
class SNatI n where
    snat :: SNat n
```

`SNat n` is a runtime witness for the scope size — essentially a Peano
numeral `Z`, `S Z`, `S (S Z)`, … that can be inspected at runtime.  The
typeclass constraint `SNatI n` says "at this type, we have a witness available."

The library provides:

```haskell
snat  :: SNatI n => SNat n         -- retrieve the witness
next  :: SNat n -> SNat (S n)      -- successor
snat_ :: SNat n -> SNatView n      -- case analysis
```

where `SNatView n` is either `SZ_` (n = Z) or `SS_ (SNat m)` (n = S m).

### Enumerating variables in scope

Given `SNatI n`, we can list every valid variable:

```haskell
Fin.universe :: SNatI n => [Fin n]
```

For `n = S (S (S Z))` this gives `[FZ, FS FZ, FS (FS FZ)]` — all three
variables in scope.

### The generator

```haskell
genTm :: forall n. SNat n -> Int -> QC.Gen (Tm n)
genTm n sz =
    let sz' = sz `div` 2
        gens = [ Lam <$> (bind1 <$> arbitrary <*> genTm (next n) sz')
               , App <$> genTm n sz' <*> genTm n sz'
               , pure Unit
               , MatchUnit <$> genTm n sz' <*> genTm n sz'
               , Pair <$> genTm n sz' <*> genTm n sz'
               , MatchPair <$> genTm n sz'
                           <*> (bind2 <$> arbitrary <*> arbitrary
                                      <*> genTm (next (next n)) sz')
               , Inj <$> QC.elements [0,1] <*> genTm n sz'
               , MatchSum <$> genTm n sz'
                          <*> (bind1 <$> arbitrary <*> genTm (next n) sz')
                          <*> (bind1 <$> arbitrary <*> genTm (next n) sz')
               ]
    in
    case snat_ n of
        SZ_ ->    -- closed scope: no variables available
            if sz <= 1 then pure Unit
                       else QC.oneof gens
        SS_ x ->  -- open scope: can generate a variable
            let genVar = withSNat x $ QC.elements (map Var Fin.universe)
            in  if sz <= 1 then QC.oneof [genVar, pure Unit]
                           else QC.oneof (genVar : gens)
```

Key observations:

- **Binders increase the scope**: generating a `Lam` body uses `genTm (next n) sz'`, which runs in scope `S n`.  The fresh variable `FZ` is automatically in scope inside.

- **Two binders**: `MatchPair` uses `next (next n)` for its body, binding two variables at once.

- **Variables use `Fin.universe`**: once we have the `SNatI n` witness (via `withSNat x`), `Fin.universe` gives all valid indices.  We wrap each one in `Var` and pick uniformly.

- **Base case**: when `sz <= 1` we only generate a variable (if available) or `Unit`, preventing infinite recursion.

- **Names are generated independently**: `arbitrary :: Gen LocalName` generates a random name for each binder, with no freshness guarantee.  That is fine — `LocalName` equality ignores names, so correctness is unaffected.

### The `Arbitrary` instance

```haskell
instance SNatI n => QC.Arbitrary (Tm n) where
    arbitrary = QC.sized (genTm snat)
    shrink    = shrinkTm
```

`QC.sized` passes a size parameter controlled by QuickCheck's test runner.
`snat :: SNat n` is the scope witness retrieved from the `SNatI n` instance.
For generating *closed* terms we use `n = Z`, so the instance becomes
`Arbitrary (Tm Z)`.

### Shrinking

`shrinkTm` produces smaller terms by:

- For `Var FZ`: no smaller variable, return `[]`.
- For `Var (FS x)`: return `[Var (pred x)]` — a variable with a smaller index.
- For `Lam b`: shrink the body, wrapping back in `Lam` with the same name.
- For `App`, `Pair`, etc.: return each sub-term alone, then all pairwise shrinks.
- For `MatchPair`: return the scrutinee, all scrutinee shrinks, and all body shrinks.

Crucially, shrinking preserves the scope: a shrunken `Tm n` is still a `Tm n`.

---

## 6. Demo: The Round Trip

We can connect both sources — parsing and generation — via a chain of
transformations:

```
generate           inject              pretty-print         parse              scope-check
Tm Z    ────────►  N.Tm   ──────────►  String  ──────────►  N.Tm  ──────────►  Either ScopeCheckError (Tm Z)
```

Two QuickCheck properties verify this:

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

Running these:

```
ghci> qc prop_project_round_trip
+++ OK, passed 1000 tests.
ghci> qc prop_parse_round_trip
+++ OK, passed 1000 tests.
```

No discards: every randomly generated `Tm Z` is well-scoped by construction,
so both directions of the round trip always succeed.

### Seeing the round trip in action

We can inspect a single randomly generated term end-to-end:

```
ghci> t <- generate (arbitrary :: Gen (Tm Z))
ghci> putStrLn (PP.pp (injectTm t))
λ x1. case x1 of | Inj0 y2 -> (λ z3. z3) y2 | Inj1 w4 -> ()
ghci> projectTm (injectTm t) == Right t
True
```

The pretty-printer uses the `LocalName` values stored in the binders to
produce readable output.  The round-trip property confirms that
scope-checking the named term recovers exactly the original de Bruijn term.

---

## 8. Historical Notes

**Scope checking as a compiler pass.** The idea of converting named surface syntax to an internal nameless or index-based form is standard in compiler design. Early Lisp interpreters used association lists (`alist`) to map symbol names to values at runtime — the direct ancestor of the `[(String, Fin n)]` context used in `projectTmWith`. In modern compilers this conversion is a distinct front-end pass, often called *name resolution* or *scope analysis*, that runs after parsing and before type checking, and uses a more efficient data structure.

**Singleton types and `SNatI`.** To use a type-level natural number `n :: Nat` at runtime — e.g., to enumerate `Fin n` — one needs a *singleton*: a runtime value that mirrors the type. Simulating this in Haskell was described by McBride ("Faking It: Simulating Dependent Types in Haskell", 2002) and later systematized in the `singletons` library (Eisenberg and Weirich, 2012). The `SNatI` typeclass and `SNat` type used by `genTm` follow this pattern.

**QuickCheck.** Koen Claessen and John Hughes introduced QuickCheck in "QuickCheck: A Lightweight Tool for Random Testing of Haskell Programs" (2000). Property-based testing is now widely used across languages. The technique of generating *well-scoped* (or well-typed) terms directly — rather than generating strings and parsing them — avoids a large class of trivially-failing test cases and is the standard approach for testing language implementations.

TODO: add citation for well-scoped and well-typed term generation

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

**4. Extending `genTm`.** After adding `Let` to the language (Exercises 2–3 in Lecture 1 and Exercise 2 above), extend `genTm` in `Tutorial.Scoped.Gen` to also generate `let`-expressions.

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

**5. Substitution laws.** State and test the following equational laws as QuickCheck properties on `Tm Z`:

- *Identity*: `applyE idE t == t`
- *Composition*: `applyE f (applyE g t) == applyE (compE f g) t`
- *Instantiate-shift*: `instantiate1 (Bind1 (weaken t)) u == t` for any `t u :: Tm Z`

For the composition law, use concrete environments, e.g. `g = idE` and `f = idE`, or build simple environments with `(.:)`. Can you find a counterexample to any of these properties if you get the implementation of `lift` wrong?

**6. More efficient scope checking** Instead of using the type `[(String, Var n)]` to map variable names to indices, design a more efficient data structure. This data structure should allow logarithmic lookup of names and constant time insertion of a new binding (while incrementing the indices of previous bindings).

If you would like a hint: check out the "Skewed Substitutions" described in this [blog post](https://mathisbd.github.io/blog/esubstitutions.html).


