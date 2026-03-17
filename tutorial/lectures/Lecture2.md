# Lecture 2: Where Do Well-Scoped Terms Come From?

In Lecture 1 we represented terms using  de Bruijn indices and implmented an 
evaluator. To make sure that our code was correct, we used 
used QuickCheck to generate well-scoped terms to test the properties of 
our evaluator. In the case that QC finds a bug, we converted the term to a 
named representation for printing. We also want to use this named representation 
for parsing: users do not want to write their code using de Bruijn indices... instead
we should let them use good-old-fashioned variable names and check for them 
that these names are in scope.

So that means that there are two sources of *well-scoped* terms that we want to 
consider:

1. **From the user** — the user writes a program in the *named* surface
   syntax; a *scope-checker* converts it to the de Bruijn representation.
2. **From the generator** — QuickCheck generates them directly using a
   size-directed generator that tracks the scope as it recurses.

This lecture covers both, and uses QuickCheck to ensure that we are treating 
variable names consistently.

---

## 1. Two Representations

We maintain two parallel term representations:

| Module | Type | Variables | Purpose |
|---|---|---|---|
| `Named.Syntax` | `Tm` | `String` | parsing, pretty-printing |
| `Scoped.Syntax` | `Tm n` | `Fin n` | evaluation, compilation |

The named representation is convenient for humans: variable names are
readable strings and there is no type index to worry about.  The scoped
representation is safe by construction: the type system rules out
out-of-scope variables entirely.

`ScopeCheck.hs` bridges the gap.  The top-level entry points are:

```haskell
injectTm  :: S.Tm Z -> N.Tm           -- always succeeds
projectTm :: N.Tm   -> Maybe (S.Tm Z) -- fails for free variables / unsupported patterns
```

Each is a one-liner that delegates to a worker that carries an explicit
context, making the workers usable independently:

```haskell
injectTmWith  :: Vec n String      -> S.Tm n -> N.Tm
projectTmWith :: [(String, Fin n)] -> N.Tm   -> Maybe (S.Tm n)
```

---

## 2. Scope-Checking: Named → Scoped (`projectTmWith`)

The scope-checker converts a named term, where variables are strings, into a
well-scoped term, where variables are de Bruijn indices.  The key challenge is
tracking which names are in scope and what index each one corresponds to.

### The scope-checking context

We use an association list `[(String, Fin n)]` threading through the
recursion.  Each entry records a name and the de Bruijn index it is currently
bound to in scope `n`.

```haskell
projectTmWith :: [(String, Fin n)] -> N.Tm -> Maybe (S.Tm n)

projectTm :: N.Tm -> Maybe (S.Tm Z)
projectTm = projectTmWith []
```

The outer call starts with the empty list `[]` (no variables in scope), so
the result is a *closed* term `S.Tm Z`.

### Variable lookup

```haskell
projectTmWith vs (N.Var v) = do
    x <- lookup v vs
    return $ S.Var x
```

If `v` is not in the association list the term has a free variable and we
return `Nothing`.

### Crossing a binder

```haskell
projectTmWith vs (N.Lam v b) = do
    b' <- projectTmWith ((v, FZ) : map (fmap FS) vs) b
    return $ S.Lam (S.bind1 (S.LocalName v) b')
```

When we cross a `λv.`, we extend the scope.  The new variable `v` maps to
`FZ` (the innermost de Bruijn index).  Every existing variable in the list is
shifted up by one (`fmap FS`) because they are now one binder further away.
The result is packed into `S.bind1`, which stores the user's name `v` as a
`LocalName` for later pretty-printing.

### Pattern matching

For `MatchPair`, which binds two names simultaneously, we add both to the
list and shift the rest by two:

```haskell
projectTmWith vs (N.Case e [(N.Pair [N.Var v1, N.Var v2], e1)]) = do
    a' <- projectTmWith vs e
    b' <- projectTmWith ((v2, FZ) : (v1, FS FZ) : map (fmap (FS . FS)) vs) e1
    return (S.MatchPair a' (S.bind2 (S.LocalName v1) (S.LocalName v2) b'))
```

Note the order: `v2` is innermost (`FZ`) and `v1` is next (`FS FZ`).  This
matches the convention used by `instantiate2` in `Eval.hs`.

For `MatchSum`, the two branches are independent: each introduces one name
into its own copy of the scope:

```haskell
projectTmWith vs (N.Case e [(N.Inj 0 (N.Var v1), e1), (N.Inj 1 (N.Var v2), e2)]) = do
    a'  <- projectTmWith vs e
    b1' <- projectTmWith ((v1, FZ) : map (fmap FS) vs) e1
    b2' <- projectTmWith ((v2, FZ) : map (fmap FS) vs) e2
    return (S.MatchSum a' (S.bind1 (S.LocalName v1) b1')
                          (S.bind1 (S.LocalName v2) b2'))
```

---

## 3. Printing: Scoped → Named (`injectTmWith`)

Going the other direction is always safe: a well-scoped term has no free
variables and every variable is a valid index.  The job is to replace each
`Fin n` index with a human-readable name.

### The naming context

We carry a `Vec n String` — a length-indexed vector of names — that maps each
in-scope de Bruijn index to a string.  The head of the vector (index `FZ`) is
the innermost (most recently bound) variable; names are prepended at each
binder site.

```haskell
injectTmWith :: Vec n String -> S.Tm n -> N.Tm

injectTm :: S.Tm Z -> N.Tm
injectTm = injectTmWith VNil
```

`VNil :: Vec Z String` is the empty vector for the closed-term case.

### The traversal

```haskell
injectTmWith vs (S.Var x)     = N.Var (vs ! x)
injectTmWith vs (S.Lam t)     = N.Lam s (injectTmWith (s ::: vs) (S.getBody1 t))
                                  where s = freshen (show (S.getLocalName t)) vs
```

`vs ! x` looks up index `x` in the vector.  At a `Lam`, we retrieve the
stored `LocalName` hint with `getLocalName`, convert it to a string, *freshen*
it (see below), then prepend it to the vector before recursing into the body.
This is the inverse of `projectTmWith`: the name stored by `bind1` is
recovered here.

### Name freshening

The `LocalName` hints stored in binders are *just hints* — they need not be
unique.  QuickCheck, for example, freely generates terms where two nested
binders share the same name hint.  If we used the hints verbatim the
pretty-printed output would contain shadowed names and the round-trip property
`prop_project_round_trip` would fail (the parser can't recover which binder a
shadowed name refers to).

We solve this with a small helper:

```haskell
-- | True if the string appears anywhere in the vector.
inVec :: String -> Vec n String -> Bool
inVec _ VNil       = False
inVec x (y ::: ys) = x == y || inVec x ys

-- | Return s unchanged if it is not in scope; otherwise append 0, 1, 2, …
-- until a fresh name is found.
freshen :: String -> Vec n String -> String
freshen s vs
    | not (inVec s vs) = s
    | otherwise        = head [ s ++ show i | i <- [0 :: Int ..], not (inVec (s ++ show i) vs) ]
```

At every binder site, the proposed name is checked against the current vector
and suffixed with a number if necessary.  For `MatchPair`, which introduces
two names at once, the second name is freshened against the already-extended
context that includes the first:

```haskell
injectTmWith vs (S.MatchPair e1 e2) =
    N.Case (injectTmWith vs e1) [(N.Pair [N.Var s1, N.Var s2], injectTmWith vs' e2')]
    where s1    = freshen (show (names ! FZ))      vs
          s2    = freshen (show (names ! FS FZ))   (s1 ::: vs)
          names = S.getLocalName2 e2
          e2'   = S.getBody2 e2
          vs'   = s2 ::: s1 ::: vs
```

---

## 4. Keeping User-Supplied Names — `LocalName`

When a user writes `λx. x` and we scope-check it, we produce

```haskell
S.Lam (S.bind1 (S.LocalName "x") (S.Var FZ))
```

The string `"x"` is stored inside the binder as a `LocalName`.  When we
later call `injectTm`, `getLocalName` retrieves it, so the printed output
reads `λ x. x` rather than `λ x0. x0`.

### The `LocalName` type

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
-- λ x. x  ==  λ y. y
Lam (bind1 (LocalName "x") (Var FZ))
  ==
Lam (bind1 (LocalName "y") (Var FZ))
-- True, because the bodies both reduce to Var FZ
```

The library example makes this explicit:

```haskell
t1 = Lam (bind (LocalName "x") (Var Fin.f0))
t2 = Lam (bind (LocalName "y") (Var Fin.f0))
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
instance Arbitrary LocalName where
    arbitrary = do
        str <- elements ["x", "y", "z", "w"]
        num <- elements [1,2,3,4,5,0]
        return (LocalName (str ++ show num))
```

This intentionally produces name collisions (e.g. `x1` can be generated
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
Tm Z    ────────►  N.Tm   ──────────►  String  ──────────►  N.Tm  ──────────►  Maybe (Tm Z)
```

Two QuickCheck properties verify this:

```haskell
-- inject then project recovers the original term
prop_project_round_trip :: S.Tm Z -> Bool
prop_project_round_trip i =
    projectTm (injectTm i) == Just i

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
ghci> projectTm (injectTm t) == Just t
True
```

The pretty-printer uses the `LocalName` values stored in the binders to
produce readable output.  The round-trip property confirms that
scope-checking the named term recovers exactly the original de Bruijn term.

---

## 7. Summary

| Concept | Where | Key idea |
|---|---|---|
| Named → scoped | `projectTmWith` | association list `[(String, Fin n)]`; extend and shift at each binder |
| Scoped → named | `injectTmWith` | `Vec n String` naming context; retrieve `LocalName` hint, freshen if shadowed |
| α-equivalence | `LocalName` | `Eq` instance makes all names equal; de Bruijn does the real comparison |
| Well-scoped generation | `genTm` | scope tracked as `SNat n`; binders widen scope with `next`; variables from `Fin.universe` |
| Round-trip | `prop_project_round_trip` | inject ∘ project = id on closed terms |

In the next lecture we will add types to the picture: generating
*well-typed* terms requires threading a typing context alongside the scope,
producing terms that evaluate without getting stuck.

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

For `projectTmWith`:

```haskell
projectTmWith vs (N.Let v e b) = do
    e' <- projectTmWith vs e
    b' <- projectTmWith ((v, FZ) : map (fmap FS) vs) b
    return $ S.Let e' (S.bind1 (S.LocalName v) b')
```

For `injectTmWith`:

```haskell
injectTmWith vs (S.Let e b) =
    N.Let s (injectTmWith vs e) (injectTmWith (s ::: vs) (S.getBody1 b))
    where s = freshen (show (S.getLocalName b)) vs
```

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

(b) What would go wrong with `prop_project_round_trip` if `LocalName` had a *real* `Eq` instance that distinguished `"x"` from `"y"`?  Construct a concrete term where the property would fail.

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
