# Lecture 3: CPS Conversion

Lectures 1 and 2 built a well-scoped de Bruijn representation and showed how
terms flow in from parsing and out to the pretty-printer.  This lecture adds a
non-trivial *term-to-term transformation*: continuation-passing style (CPS)
conversion.

CPS is a good case study because:

- It changes the *shape* of binders — each function gains an extra argument.
- It requires carefully tracking how de Bruijn indices shift across the
  transformation.
- It produces terms in a richer scope, so we need a separate index-mapping
  structure.
- Its correctness properties illuminate the difference between big-step and
  small-step semantics.

---

## 1. What is CPS?

In direct style, a function returns its result to its caller implicitly.  In
*continuation-passing style* every function receives an extra argument — the
*continuation* — which represents "what to do with the result".  Instead of
returning, a function calls its continuation.

The transformation is defined inductively on terms.  We write `[[e]] k` to
mean "translate `e`, passing results to continuation `k`":

```
[[x]]          k = k x
[[λx. e]]      k = k (λx. λk'. [[e]] k')
[[e1 e2]]      k = [[e1]] (λx. [[e2]] (λy. x y k))
[[()]]         k = k ()
[[(e1, e2)]]   k = [[e1]] (λx. [[e2]] (λy. k (x,y)))
[[inj i e]]    k = [[e]] (λx. k (inj i x))
[[case e of (x,y) → b]]    k = [[e]] (λz. case z of (x,y) → [[b]] k)
[[case e of inj i → b_i]]  k = [[e]] (λz. case z of inj i → [[b_i]] k)
```

The top-level call uses the identity continuation: `cps(e) = [[e]] (λx. x)`.

---

## 2. Two Flavors of Continuation — `Cont`

A naive implementation would represent every continuation `k` as a `Tm g`
(an object-level lambda) and apply it with `App k v`.  But this introduces
*administrative redexes* — beta redexes of the form `(λx. body) v` that were
not present in the source and must be reduced away.

To avoid this we distinguish two cases:

```haskell
data Cont (g :: Nat) where
    Obj  :: Tm g          -> Cont g   -- object-level term
    Meta :: Bind1 Tm Tm g -> Cont g   -- meta-level binder
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

The instance body is empty because `Generic1` is not derived for `Cont` — in
practice the library's default generic machinery handles it, or the user can
derive it.

---

## 3. The Scope Problem

The CPS translation changes the scope.  Every `λ`-abstraction gains an extra
argument (the continuation `k'`), so a term in scope `n` becomes a term in a
*larger* scope.  Concretely:

- A closed term (`Tm Z`) translates to a closed term (`Tm Z`): the top-level
  call to the identity continuation is in scope 0.
- Inside `λx. e`, the body `e` is in scope `S g`.  After CPS, the body lives
  in scope `S (S g')` — one slot for `x`, one slot for `k'`.

This means we cannot simply apply `cpsIdx` naively to variable indices.  A
variable `FZ` in the source body might map to `FS FZ` in the CPS body (if the
new continuation slot was inserted at position 0).

---

## 4. Tracking Index Shifts — `CpsCtx`

`CpsCtx g g'` is a GADT that records how variables in source scope `g` map
to positions in CPS scope `g'`:

```haskell
data CpsCtx g g' where
    CpsStart :: CpsCtx N0 N0
    CpsLam   :: CpsCtx g g' -> CpsCtx (S g) (S (S g'))
    CpsMeta  :: CpsCtx g g' -> CpsCtx (S g) (S g')
    CpsLift  :: CpsCtx g g' -> CpsCtx (S g) (S (S g'))
```

The three non-trivial constructors correspond to three different binder
situations:

### `CpsLam` — inside a translated lambda body

When we translate `λx. e`, the CPS output is `λx. λk'. body`.  Inside
`body`, the scope has grown by two:

- `FZ` is now the continuation `k'`
- `FS FZ` is the original parameter `x`
- `FS (FS v)` are the outer variables

So `x` (which was `FZ` in the source body) maps to `FS FZ` in the CPS body,
and every outer variable `v` maps to `FS (FS (cpsIdx gg v))`:

```haskell
cpsIdx (CpsLam gg) FZ     = FS FZ
cpsIdx (CpsLam gg) (FS v) = FS (FS (cpsIdx gg v))
```

### `CpsMeta` — inside a meta-continuation body

When we build an intermediate continuation `Meta (bind1 k body)`, inside
`body` there is one extra variable (the value passed to the continuation).
This variable maps to itself (`FZ → FZ`), and outer variables shift by one:

```haskell
cpsIdx (CpsMeta gg) FZ     = FZ
cpsIdx (CpsMeta gg) (FS v) = FS (cpsIdx gg v)
```

### `CpsLift` — inside a case branch body

When we translate `case e of { inj_i y_i → b_i }`, the output is:

```
[[e]] (λz. case z of { inj_i y_i → [[b_i]] k })
```

Inside the branch body, the scope is `S (S g')`:

- `FZ` is `y_i` (the pattern variable, freshly bound by the case branch)
- `FS FZ` is `z` (the scrutinee result, bound by the outer meta-lambda)
- `FS (FS v)` are the outer CPS variables

The source branch body has one extra variable (`y_i` at `FZ`).  We need to
translate it to CPS scope `S (S g')` while:

- keeping `FZ` (= `y_i`) at `FZ`
- mapping outer variables `FS v` to `FS (FS (cpsIdx g v))` — skipping over
  the scrutinee slot at `FS FZ`

```haskell
cpsIdx (CpsLift gg) FZ     = FZ
cpsIdx (CpsLift gg) (FS v) = FS (FS (cpsIdx gg v))
```

Note that `CpsLift` and `CpsLam` have the *same* index mapping — both shift
the outermost variable to position 0 and shift outer variables up by two.  The
difference is semantic: `CpsLam` is used for lambda bodies (where the
outer-scope variable is `k'`), while `CpsLift` is used for case branches
(where the outer-scope variable is the scrutinee `z`).

---

## 5. The Translation — `cpsExp`

```haskell
cpsExp :: CpsCtx g g' -> Tm g -> Cont g' -> Tm g'
```

`cpsExp ctx e k` translates expression `e` (in source scope `g`) to a CPS
term in scope `g'`, threading results through continuation `k`.

### Variables and unit

```haskell
cpsExp g (Var v) k = applyCont k (Var (cpsIdx g v))
cpsExp g Unit    k = applyCont k Unit
```

Values are immediately passed to the continuation.  Variables are remapped
through `cpsIdx`.

### Lambda

```haskell
cpsExp g (Lam b) k =
    let e' = Lam . bind1 (getLocalName b)
               $ Lam . bind1 contName
                 $ cpsExp (CpsLam g) (getBody1 b) (Obj (Var FZ))
    in applyCont k e'
```

The translated lambda `e'` takes two arguments: the original parameter `x`
and a fresh continuation `k'` (at `FZ`).  The body is translated with
`CpsLam g` (which maps `x` to `FS FZ`) and the continuation `Obj (Var FZ)`
(i.e. `k'`, the new innermost variable).  The whole lambda `e'` is then
passed to `k`.

Note that `Lam k` inside `reifyCont` uses the library's `Lam` constructor,
which takes a `Bind1`.  The `bind1 contName` call stores the user-visible
name `"k"` for pretty-printing.

### Application

```haskell
cpsExp g (App e1 e2) k =
    let k1 = Meta . bind1 contName $
               cpsExp (CpsMeta g) (applyE weaken e2) k2
        k2 = Meta . bind1 contName $
               App (App (Var (FS FZ)) (Var FZ))
                   (reifyCont (applyE (weaken .>> weaken) k))
    in cpsExp g e1 k1
```

This implements `[[e1]] (λx. [[e2]] (λy. x y k))`.

- We translate `e1` with intermediate continuation `k1`.
- Inside `k1` (scope `S g'`), `x = Var FZ` is the result of `e1`.
  We translate `e2` with `k2`.  Since `e2` is from scope `g` but we are now
  in scope `S g'`, we weaken it with `applyE weaken e2`.  The context
  `CpsMeta g` maps `e2`'s variables correctly into scope `S g'`.
- Inside `k2` (scope `S (S g')`), `y = Var FZ` and `x = Var (FS FZ)`.
  We emit the application `x y` forwarded to `k`.  The outer continuation `k`
  is in scope `g'`, so we weaken it twice (`weaken .>> weaken`) to reach
  scope `S (S g')`, then reify it as an object-level term.

`weaken :: Env Tm n (S n)` is `shift1E` — the environment that shifts every
variable up by one, i.e. `Var . FS`.  Composing it twice with `.>>` gives the
environment that shifts up by two.

### Pair

```haskell
cpsExp g (Pair e1 e2) k =
    let k1 = Meta . bind1 contName $
               cpsExp (CpsMeta g) (applyE weaken e2) k2
        k2 = Meta . bind1 contName $
               applyCont k' (Pair (Var (FS FZ)) (Var FZ))
        k' = applyE (weaken .>> weaken) k
    in cpsExp g e1 k1
```

The structure mirrors `App`: evaluate `e1` then `e2`, collect the two results
as `Var (FS FZ)` and `Var FZ` in scope `S (S g')`, form the pair, and pass it
to `k`.

### Injection

```haskell
cpsExp g (Inj i e) k =
    cpsExp g e (Meta . bind1 contName $
        applyCont (applyE weaken k) (Inj i (Var FZ)))
```

Evaluate `e`, wrap the result in `Inj i`, pass to `k`.  We are inside one
binder, so `k` must be weakened once.

### Case on unit

```haskell
cpsExp g (MatchUnit e1 e2) k =
    cpsExp g e1 (Meta . bind1 contName $
        MatchUnit (Var FZ)
            (cpsExp (CpsMeta g) (applyE weaken e2) (applyE weaken k)))
```

Evaluate the scrutinee, then emit `MatchUnit`.  The continuation body `e2` is
from scope `g`; inside the meta-binder it is in scope `S g'`, so we weaken
both `e2` and `k`.

### Case on a sum

```haskell
cpsExp g (MatchSum e0 e1 e2) k =
    cpsExp g e0 (Meta . bind1 contName $
        MatchSum (Var FZ)
            (bind1 (getLocalName e1)
                (cpsExp (CpsLift g) (getBody e1)
                    (applyE (weaken .>> weaken) k)))
            (bind1 (getLocalName e2)
                (cpsExp (CpsLift g) (getBody e2)
                    (applyE (weaken .>> weaken) k))))
```

The scrutinee is evaluated and bound at `FZ` by the outer meta-binder.  Each
branch then binds its pattern variable at the new `FZ`, pushing the scrutinee
to `FS FZ`.  The `CpsLift` context (rather than `CpsMeta (CpsMeta g)`)
handles this: it maps `FZ` → `FZ` (the pattern variable) and outer vars
`FS v` → `FS (FS (cpsIdx g v))` (skipping the scrutinee slot at `FS FZ`).
The continuation `k` is weakened twice (past the scrutinee and the pattern
variable).

### Case on a pair

```haskell
cpsExp g (MatchPair e1 b) k =
    let b'  = getBody2 b
        g'  = CpsMeta (CpsMeta g)
        k'  = applyE (weaken .>> weaken) k
        b'' = bind2 x1 x2 (cpsExp g' b' k')
        k1  = Meta . bind1 contName $
                MatchPair (Var FZ) (applyE weaken b'')
    in cpsExp g e1 k1
```

`MatchPair` binds *two* variables simultaneously.  The body `getBody2 b` is
in scope `S (S g)`.  We use `CpsMeta (CpsMeta g)` which maps both bound
variables to themselves (`FZ → FZ`, `FS FZ → FS FZ`) and shifts outer vars up
by two.  The translated body is re-wrapped in `bind2 x1 x2`, then weakened
once (for the scrutinee meta-binder) before being placed inside `MatchPair`.

---

## 6. Correctness Properties

### Big-step: `prop_cps_eval`

```haskell
prop_cps_eval :: Tm Z -> Property
prop_cps_eval e = ...
    cps_eval_e == eval_cps_e
  where
    cps_eval_e = cps (eval e)   -- CPS the value
    eval_cps_e = eval (cps e)   -- evaluate the CPS term
```

`cps(eval(e)) == eval(cps(e))`: applying CPS to the evaluated result gives the
same thing as evaluating the CPS translation.  This is the standard
*correctness* theorem for CPS: the translation preserves big-step semantics.

QuickCheck confirms this:

```
ghci> qc prop_cps_eval
+++ OK, passed 1000 tests; ...
```

### Small-step: `prop_cps_step` — a cautionary tale

```haskell
prop_cps_step :: Tm Z -> Property
prop_cps_step e = ...
    cps (step e) == step (cps e)   -- this is TOO STRONG
```

This property asks for a *syntactic* single-step simulation:
`cps(step(e)) == step(cps(e))`.  It **fails**:

```
e      = let x = λz. () in x
step_e = λz. ()
cps_e  = (let x = λz k. k () in λk. k x) (λx. x)
cps(step_e) = λz k. k ()
step(cps_e) = let k = λx. x in k (λz k. k ())   -- NOT the same term
```

The CPS translation introduces *administrative redexes* — beta redexes that
were not present in the source.  Here, after one direct-style step we get a
value, but the CPS term needs one more step to eliminate the administrative
`let`.  The two sides are equal only after further reduction.

The correct small-step statement is:

```
eval(cps(step(e))) == eval(step(cps(e)))
```

Both sides reduce to the same final value: the left evaluates `cps` of the
stepped term, and the right evaluates one step of the CPS term.  This follows
from the big-step correctness theorem (`prop_cps_eval`) and the fact that
`eval` is stable under single steps (`prop_evalStep` from Lecture 1).

---

## 7. Summary

| Concept | Implementation | Key idea |
|---|---|---|
| CPS translation | `cpsExp` | inductive on term structure; continuation is threaded through |
| Two continuation forms | `Cont` (`Obj`/`Meta`) | `Meta` avoids administrative redexes by substituting directly |
| `reifyCont` | turns `Meta k` into `Lam k` | needed when continuation must appear as an object-level value |
| Index remapping | `CpsCtx` / `cpsIdx` | GADT tracks how source scope maps to CPS scope |
| `CpsLam` | `FZ → FS FZ` | lambda body: continuation takes slot 0, param moves to slot 1 |
| `CpsMeta` | `FZ → FZ` | meta-binder body: bound value stays at slot 0 |
| `CpsLift` | `FZ → FZ`, `FS v → FS (FS ...)` | case branch: pattern var stays at 0, scrutinee is at 1 |
| Weakening | `applyE weaken`, `applyE (weaken .>> weaken)` | lift arguments/continuations into larger scopes |
| Big-step correctness | `prop_cps_eval` | `cps(eval(e)) == eval(cps(e))` — passes |
| Small-step simulation | `prop_cps_step` as written | too strong; administrative redexes break syntactic equality |
