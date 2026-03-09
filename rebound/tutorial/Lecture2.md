# Lecture 2: Where Do Well-Scoped Terms Come From?

In Lecture 1 we built the de Bruijn representation and an evaluator, and
observed that QuickCheck discards a large fraction of generated tests because
randomly-built terms get stuck.  The root cause is that `Arbitrary (Tm n)`
generates *syntactically* valid terms with no regard for types.

Before we can fix that we need to step back: even before asking about
*well-typed* terms, where do *well-scoped* terms come from in the first
place?  There are two sources:

1. **From the user** — the user writes a program in the *named* surface
   syntax; a *scope-checker* converts it to the de Bruijn representation.
2. **From the generator** — QuickCheck generates them directly using a
   size-directed generator that tracks the scope as it recurses.

This lecture covers both, and ends with a demo showing that the two roads
form a round trip.

---

## 1. Two Representations

We maintain two parallel term representations:

| Module | Type | Variables | Purpose |
|---|---|---|---|
| `Named.Syntax` | `Tm` | `String` | parsing, pretty-printing |
| `Simple.Syntax` | `Tm n` | `Fin n` | evaluation, type-checking |

The named representation is convenient for humans: variable names are
readable strings and there is no type index to worry about.  The scoped
representation is safe by construction: the type system rules out
out-of-scope variables entirely.

`ScopeCheck.hs` bridges the gap with four functions:

```haskell
injectTy  :: I.Ty   -> N.Ty          -- always succeeds
projectTy :: N.Ty   -> Maybe I.Ty    -- fails for n-ary types

injectTm  :: I.Tm Z -> N.Tm          -- always succeeds
projectTm :: N.Tm   -> Maybe (I.Tm Z)-- fails for free variables / unsupported patterns
```

---

## 2. Scope-Checking: Named → Scoped (`projectTm`)

The scope-checker converts a named term, where variables are strings, into a
well-scoped term, where variables are de Bruijn indices.  The key challenge is
tracking which names are in scope and what index each one corresponds to.

### The scope-checking context

We use an association list `[(String, Fin n)]` threading through the
recursion.  Each entry records a name and the de Bruijn index it is currently
bound to in scope `n`.

```haskell
projectTm :: N.Tm -> Maybe (I.Tm Z)
projectTm = to [] where
    to :: [(String, Fin n)] -> N.Tm -> Maybe (I.Tm n)
```

The outer call starts with the empty list `[]` (no variables in scope), so
the result is a *closed* term `I.Tm Z`.

### Variable lookup

```haskell
    to vs (N.Var v) = do
        x <- lookup v vs
        return $ I.Var x
```

If `v` is not in the association list the term has a free variable and we
return `Nothing`.

### Crossing a binder

```haskell
    to vs (N.Lam v b) = do
        b' <- to ((v, FZ) : map (fmap FS) vs) b
        return $ I.Lam (I.bind1 (I.LocalName v) b')
```

When we cross a `λv.`, we extend the scope.  The new variable `v` maps to
`FZ` (the innermost de Bruijn index).  Every existing variable `x` in the
list is shifted up by one (`fmap FS`) because they are now one binder
further away.  The result is packed into `I.bind1`, which stores the user's
name `v` as a `LocalName` for later pretty-printing.

### Pattern matching

For `MatchPair`, which binds two names simultaneously, we add both to the
list and shift the rest by two:

```haskell
    to vs (N.Case e [(N.Pair [N.Var v1, N.Var v2], e1)]) = do
        a' <- to vs e
        b' <- to ((v2, FZ) : (v1, FS FZ) : map (fmap (FS . FS)) vs) e1
        return (I.MatchPair a' (I.bind2 (I.LocalName v1) (I.LocalName v2) b'))
```

Note the order: `v2` is innermost (`FZ`) and `v1` is next (`FS FZ`).  This
matches the convention used by `instantiate2` in `Eval.hs`.

For `MatchSum`, the two branches are independent: each introduces one name
into its own copy of the scope:

```haskell
    to vs (N.Case e [(N.Inj 0 (N.Var v1), e1), (N.Inj 1 (N.Var v2), e2)]) = do
        a'  <- to vs e
        b1' <- to ((v1, FZ) : map (fmap FS) vs) e1
        b2' <- to ((v2, FZ) : map (fmap FS) vs) e2
        return (I.MatchSum a' (I.bind1 (I.LocalName v1) b1')
                              (I.bind1 (I.LocalName v2) b2'))
```

Unsupported patterns return `Nothing`:

```haskell
    to vs _ = Nothing
```

---

## 3. Printing: Scoped → Named (`injectTm`)

Going the other direction is always safe: a well-scoped term has no free
variables and every variable is a valid index.  The job is to replace each
`Fin n` index with a human-readable name.

### The naming context

We carry a context `Ctx n` — in the simplest version, a function
`Fin n -> String` — that maps each in-scope index to a name:

```haskell
type Ctx n = Fin n -> String

emptyCtx :: Ctx Z
emptyCtx = \x -> case x of {}   -- Fin Z is empty, so no case needed

(+%) :: Ctx n -> String -> Ctx (S n)
ctx +% s = \x -> case x of { FZ -> s ; FS y -> ctx y }
```

`Fin Z` is an empty type (there are no constructors), so `emptyCtx` is
vacuously total.  Extending with `(+%)` mirrors the structure of `(.:)` for
substitution environments from Lecture 1.

### The traversal

```haskell
injectTm :: I.Tm Z -> N.Tm
injectTm = to emptyCtx where
    to :: forall n. SNatI n => Ctx n -> I.Tm n -> N.Tm
    to vs (I.Var x)     = N.Var (vs x)
    to vs (I.Lam t)     = N.Lam s (to (vs +% s) (I.getBody1 t))
                            where s = show (I.getLocalName t)
    ...
```

At a `Lam`, we retrieve the stored `LocalName` from the binder with
`getLocalName`, convert it to a string, and extend the context before
recursing into the body.  This is the inverse of `projectTm`: the name that
was stored by `bind1` is recovered here.

The `SNatI n` constraint is needed so that `Fin.universe :: [Fin n]` is
available in the generator (see §5); `injectTm` itself does not need it, but
the constraint appears on the helper `to` in order to satisfy the type of
`getBody1`.

---

## 4. Keeping User-Supplied Names — `LocalName`

When a user writes `λx. x` and we scope-check it, we produce

```haskell
I.Lam (I.bind1 (I.LocalName "x") (I.Var FZ))
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
prop_project_round_trip :: I.Tm Z -> Bool
prop_project_round_trip i =
    projectTm (injectTm i) == Just i

-- pretty-print then parse recovers the named term
prop_parse_round_trip :: I.Tm Z -> Bool
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
| Named → scoped | `projectTm` | association list `[(String, Fin n)]`; extend and shift at each binder |
| Scoped → named | `injectTm` | context `Ctx n = Fin n -> String`; retrieve `LocalName` from each binder |
| α-equivalence | `LocalName` | `Eq` instance makes all names equal; de Bruijn does the real comparison |
| Well-scoped generation | `genTm` | scope tracked as `SNat n`; binders widen scope with `next`; variables from `Fin.universe` |
| Round-trip | `prop_project_round_trip` | inject ∘ project = id on closed terms |

In the next lecture we will add types to the picture: generating
*well-typed* terms requires threading a typing context alongside the scope,
producing terms that evaluate without getting stuck.
