# Lecture 4: Efficient Implementation — Delayed and Defunctionalized Substitutions

Lectures 1–3 built a correct implementation of well-scoped de Bruijn terms,
showed how to convert between named and scoped representations, and used the
machinery to implement CPS conversion.  All of this worked using the `rebound`
library, but so far we have treated it as a black box.  This lecture opens the
box.

The focus is efficiency.  We will see:

1. **Why naive traversal is expensive** — every `applyE` call traverses
   the entire term.
2. **Delayed substitutions at binders** — store a pending substitution
   *inside* the `Bind` wrapper instead of applying it immediately.
3. **Defunctionalized environments** — represent substitutions as data
   rather than functions so that compositions can be simplified by
   smart constructor rules.
4. **The `applyOpt` shortcut** — detect the identity environment and
   bail out before touching the term.
5. **How it all fits together** — what `getBody`, `instantiate1`, and
   `applyE` actually do in the library.

---

## 1. The Problem: Traversal Cost for Substitutions

Recall the hand-written substitution from `Scratch.hs`:

```haskell
type Env m n = Fin m -> Tm n

applyE :: Env m n -> Tm m -> Tm n
applyE env (Lam (Bind1 b)) = Lam (Bind1 (applyE (lift env) b))
applyE env (App f a)       = App (applyE env f) (applyE env a)
-- ...

lift :: Env m n -> Env (S m) (S n)
lift env = Var FZ .: (applyE shift . env)
```

Every call to `applyE` traverses the entire term, recursing into every
sub-term.  Crucially, `lift` is called *once per binder encountered during
traversal*, and each `lift` itself calls `applyE shift` on every term in the
range of `env`.

Consider a deeply-nested expression: normalizing it requires many rounds of
substitution, and each round descends through all the binders above the
redex.  In the worst case — reducing a sequence of `n` beta redexes in a
term of depth `d` — the naive strategy costs O(n × d) traversals.

There is a classical solution, known since at least Abadi, Cardelli, Curien,
and Lévy's *Explicit Substitutions* (1991): **delay** the
substitution in the term instead of applying it immediately.

In that calculus, substitutions could be stored anywhere in the term. But here, we would
like to hide the delayed substitution from users. Therefore, we will only store substitutions in the
binder type.

### Measuring the cost

The paper accompanying the `rebound` library benchmarked several
implementations of full normalization on a standard stress test.  Here are
representative timings:

| Implementation | Strategy | Time (nf) |
|---|---|---|
| `SubstV` | Naive eager substitution (à la `Scratch.hs`) | 3330 ms |
| `BindV` | Delayed substitution inside `Bind` | 0.767 ms |
| `EnvV` | Explicit environment threaded everywhere | 0.586 ms |

The delayed-substitution approach (`BindV`) is roughly **4300× faster** than
the naive one.  The remaining sections explain how the library achieves this.

---

## 2. From Naive to Delayed: The `Bind` Type

In `Scratch.hs`, `Bind1` is a transparent wrapper around the body:

```haskell
-- Scratch.hs (naive)
data Bind1 n = Bind1 (Tm (S n))
```

There is nowhere to store a pending substitution.  When we cross a binder
with `applyE`, we must call `lift env` and descend into the body immediately.

The library's `Bind` type adds a slot for the name hint *and* a slot for the
pending substitution.  The tutorial's `Bind1 Tm Tm n` (from `Rebound.Bind.Local`)
is a synonym for:

```haskell
type Bind1 v c n = Pat.Bind v c LocalName n
```

The general `Bind` type (from `Rebound.Bind.Pat`) is:

```haskell
data Bind v c (pat :: Type) (n :: Nat) where
    Bind :: pat -> Env v m n -> c (Size pat + m) -> Bind v c pat n
```

There are three fields:

| Field | Type | Meaning |
|---|---|---|
| `pat` | `pat` | pattern metadata (e.g. `LocalName`, `Vec N2 LocalName`) |
| `Env v m n` | pending substitution | maps old scope `m` to current scope `n` |
| `c (Size pat + m)` | body | term under the binder, still in old scope `m` |

### Why does `Bind` carry a pattern?

The body of a binder lives in a larger scope than the surrounding term: the
scope grows by `Size pat` — the number of variables the pattern introduces.
For a simple lambda, `pat = LocalName` and `Size LocalName = 1`, so the body
lives in scope `S m`.  For a pair match, `pat = Vec N2 LocalName` and
`Size (Vec N2 LocalName) = 2`, so the body lives in scope `S (S m)`.

Beyond the scope bookkeeping, the pattern carries *metadata*.  For the
tutorial's `LocalName` pattern, that metadata is the user-visible name hint
used for pretty-printing:

```haskell
-- Lam stores the name "x" alongside the body
ex_id :: Tm Z
ex_id = Lam (bind1 (LocalName "x") (Var FZ))

-- retrieve the name hint later
getLocalName :: Bind1 v c n -> LocalName
```

The `Eq` instance for `LocalName` ignores the name (`x == y = True`), so
two binders with different names but identical bodies are considered equal.
The de Bruijn indices do the real comparison; `LocalName` is only for display.

### Constructing a binder

In `Rebound.Bind.Local`, `bind1` takes the name as an explicit argument:

```haskell
bind1 :: Subst v c => LocalName -> c (S n) -> Bind1 v c n
bind1 name body = Pat.bind name body    -- stores: Bind name idE body
```

The internal `Pat.bind` sets the pending environment to `idE`:

```haskell
bind :: Sized pat => Subst v c => pat -> c (Size pat + n) -> Bind v c pat n
bind pat = Bind pat idE
```

No traversal.  The body is stored as-is with a zero-cost identity substitution.

### Applying a substitution to a binder — O(1)

Here is the key insight.  The `Subst` instance for `Bind` is:

```haskell
instance SubstVar v => Subst v (Bind v c p) where
    applyE env1 (Bind p env2 body) = Bind p (env2 .>> env1) body
```

Applying environment `env1` to a binder does **not** touch the body at all.
It simply *composes* the new environment with the existing one.  The body is
untouched.

Compare this to the naive version:

```haskell
-- Scratch.hs (naive)
applyE env (Lam (Bind1 b)) = Lam (Bind1 (applyE (lift env) b))
--                                        ^^^^^^^^^^^^^^^^^^^^
--                                        traverses the entire body eagerly
```

With the library:

```haskell
-- rebound (delayed)
applyE env (Lam bnd) = Lam (applyE env bnd)
--                        = Lam (Bind p (old_env .>> env) body)
--                                       ^^^^^^^^^^^^^^^^
--                                       just a composition — no traversal
```

Every time a substitution passes over a binder, the cost is O(1).  The
traversal of the body is *deferred* until the body is actually needed.

### Forcing the body — `getBody`

The suspended substitution is applied on demand by `getBody`:

```haskell
getBody :: Subst v c => Bind v c pat n -> c (Size pat + n)
getBody (Bind (pat :: pat) (env :: Env v m n) body) =
    applyOpt applyE (upN (size pat) env) body
```

`upN k env` lifts `env` under `k` binders: the `k` locally-bound variables
map to themselves, and all outer variables are shifted appropriately.
`applyOpt` is described in §5.

---

## 3. Defunctionalized Environments

In `Scratch.hs` we used a function type:

```haskell
type Env m n = Fin m -> Tm n
```

Shifting a substitution over a binder is O(1), but only if environment
*composition* — the `.>>` operator — is itself cheap.  With a plain function,
we can compose:

```haskell
compE f g x = applyE f (g x)   -- O(1) to build, but no simplification possible
```

But there is no way to inspect a function to detect special cases like the
identity or consecutive shifts.  In particular, we cannot detect that
`shift .>> shift` should simplify to a single shift-by-two.

The `rebound` library uses a **defunctionalized** representation — substitutions
are *data*, not functions, so they can be inspected, simplified, and fused:

```haskell
data Env (a :: Nat -> Type) (n :: Nat) (m :: Nat) where
    Zero  :: Env a Z n                            -- empty domain (scope Z)
    Inc   :: SNat m -> Env a n (m + n)            -- shift every index up by m
    Cons  :: a m -> Env a n m -> Env a (S n) m    -- FZ ↦ head, rest to tail
    (:<>) :: Env a m n -> Env a n p -> Env a m p  -- sequential composition
```


Each constructor represents a specific, commonly-occurring substitution:

| Constructor | Naive function equivalent | Meaning |
|---|---|---|
| `Zero` | `\x -> case x of {}` | empty domain (scope 0) |
| `Inc m` | `\x -> Var (shiftN m x)` | shift every variable up by `m` |
| `Cons t r` | `\case FZ -> t; FS x -> r x` | extend: `FZ ↦ t`, rest via `r` |
| `e1 :<> e2` | `\x -> applyE e2 (applyEnv e1 x)` | sequential composition |

### `Fin.shiftN` — adding to an index

`Fin.shiftN m x` adds the natural number `m` to the de Bruijn index `x`,
producing a larger index in `Fin (m + n)`:

```haskell
Fin.shiftN :: SNat m -> Fin n -> Fin (m + n)
```

For example, `shiftN s2 FZ = FS (FS FZ)` — index 0 becomes index 2.  The
`Inc m` constructor uses this: `applyEnv (Inc m) x = var (shiftN m x)`.

### `shiftNE` — building an `Inc` environment

`shiftNE m` is the smart constructor that wraps `m` in `Inc`:

```haskell
shiftNE :: SubstVar v => SNat m -> Env v n (m + n)
shiftNE = Inc
```

Two standard aliases are built on top:

```haskell
idE     :: SubstVar v => Env v n n
idE     = shiftNE s0        -- Inc SZ  (shift by zero = identity)

shift1E :: SubstVar v => Env v n (S n)
shift1E = shiftNE s1        -- Inc s1  (shift by one)
```

Because `idE = Inc SZ` is *data*, `applyOpt` (§5 below) can inspect it without
calling into `applyE`.

### Interpreting the environment

The application function `applyEnv` interprets these constructors:

```haskell
applyEnv :: SubstVar a => Env a n m -> Fin n -> a m
applyEnv Zero        x      = Fin.absurd x
applyEnv (Inc m)     x      = var (Fin.shiftN m x)
applyEnv (Cons t _)  FZ     = t
applyEnv (Cons _ r)  (FS x) = applyEnv r x
applyEnv (s1 :<> s2) x      = applyE s2 (applyEnv s1 x)
```

### Why not a plain function?

The naive function-based environment (`type Env m n = Fin m -> Tm n`) is
perfectly correct, but cannot be inspected.  You cannot tell whether a function
is the identity, and you cannot fuse two consecutive shifts.  The paper measures
this directly:

| Environment | Time (nf) |
|---|---|
| `Functional` (plain function) | 126 ms |
| `Lazy` (defunctionalized + smart composition) | 0.84 ms |

The defunctionalized representation is roughly **150× faster** for full
normalization — almost entirely because it enables the smart composition rules
described next.

---

## 4. Smart Composition — `comp` and `.>>`

The function `comp` (exposed as `.>>`) builds a composed environment, but
applies a battery of algebraic simplifications before resorting to `(:<>)`:

```haskell
(.>>) :: Subst v v => Env v p n -> Env v n m -> Env v p m
(.>>) = comp

comp :: SubstVar a => Env a m n -> Env a n p -> Env a m p
comp Zero       _               = Zero
comp (Inc k1)   (Inc k2)        = Inc (k1 + k2)       -- merge two shifts
comp (Inc SZ)   s               = s                    -- shift by 0 = identity
comp s          (Inc SZ)        = s
comp (Inc (SS p)) (Cons _ r)    = comp (Inc p) r      -- skip the Cons head
comp (s1 :<> s2) s3             = comp s1 (comp s2 s3) -- re-associate right
comp (Cons t s1) s2             = Cons (applyE s2 t) (comp s1 s2)
comp s1          s2             = s1 :<> s2            -- fallback
```

Key cases:

- **Shift fusion**: `Inc k1 .>> Inc k2 = Inc (k1+k2)` — two consecutive
  shifts merge into one `Inc` without any traversal.
- **Identity elimination**: `Inc SZ .>> s = s` and `s .>> Inc SZ = s` —
  shifting by zero is the identity; discard it.
- **`Inc` and `Cons`**: `Inc (S p) .>> Cons _ r = Inc p .>> r` — a shift
  past the head of a `Cons` consumes the head and continues into the tail.

These rules mean that common patterns like repeatedly weakening a term never
accumulate deep `(:<>)` chains; they collapse to a single `Inc` at composition
time.

### How much does smart composition contribute?

The paper isolates each optimization with ablation benchmarks:

| Variant | What is missing | Time (nf) |
|---|---|---|
| `Lazy` (full) | — | 0.84 ms |
| `LazyA` | no `applyOpt` identity shortcut | 0.844 ms |
| `LazyB` | no smart composition | 2.36 ms |

Removing smart composition (`LazyB`) gives a **~2.8× slowdown** on full
normalization.  Removing just the identity shortcut (`LazyA`) is almost
unmeasurable — smart composition already handles most identity eliminations at
construction time.  The paper concludes: *"much of the speed up comes from
'smart composition'."*

---

## 5. The Identity Shortcut — `applyOpt`

Even with smart composition, we still need to call `applyE` when forcing a
binder.  But a very common case is that the environment *is already the
identity* — we are just retrieving a freshly-constructed body with no pending
substitution.  `applyOpt` detects this before touching the term:

```haskell
applyOpt :: (Env v n m -> c n -> c m) -> (Env v n m -> c n -> c m)
applyOpt f (Inc SZ) x = x
applyOpt f r        x = f r x
```

When the environment is `Inc SZ` (= `idE`, shift by zero), the term is
returned untouched.  This short-circuit fires routinely: every
`bind1 name body` stores `idE` as the initial environment, so if no
substitution has been composed in since construction, `getBody` returns the
body with zero traversal.

---

## 6. The `up` and `upN` Operations

When a substitution must be applied *under* binders — as happens inside
`getBody` — we need to *lift* it past the bound variables.  The `up` function
is the library's version of `lift` from `Scratch.hs`:

```haskell
up :: SubstVar v => Env v m n -> Env v (S m) (S n)
up (Inc SZ) = Inc SZ
up e        = var Fin.f0 .: comp e (Inc s1)
```

The special case recognises the identity and returns it immediately — lifting
the identity is still the identity.  The general case is the familiar
`lift`:

- `FZ` maps to `Var FZ` (the newly-bound variable stays at index 0).
- Every other variable `x` maps to `env x`, then shifted up by one (`Inc s1`)
  to make room for the new binder.

`upN p env` lifts `env` under `p` binders by iterating this operation,
producing an environment of type `Env v (p + m) (p + n)`.  `getBody` calls
`upN (size pat) env` to bring `env` into scope before applying it to the body.

---

## 7. Putting It All Together

Let us trace what happens when the evaluator opens a lambda binder:

```haskell
eval (App m n) = do
    mv <- eval m
    nv <- eval n
    case mv of
        Lam b -> eval (instantiate1 b nv)
        _     -> Nothing
```

`instantiate1 b nv` expands to:

```haskell
instantiate1 b v1 = Pat.instantiate b (v1 .: zeroE)
```

which calls:

```haskell
instantiate b e =
    unbindWith b
        (\p r body -> applyOpt applyE (withSNat (size p) $ e .++ r) body)
```

Breaking this down step by step:

1. **`unbindWith`** extracts the stored environment `r :: Env v m n` and the
   body `body :: Tm (1 + m)` *without forcing the body*.

2. **`e .++ r`** appends the instantiation environment `e = (nv .: zeroE)` to
   the stored environment `r`, giving an environment of type `Env v (1 + m) n`
   that maps:
   - `FZ` → `nv` (the argument value)
   - `FS x` → `applyEnv r x` (outer variables via the stored `r`)

3. **`applyOpt applyE env body`** applies the combined environment to the body.
   If `r` was `idE` (common when `b` was freshly created with `bind1`), the
   combined environment simplifies to `nv .: idE`, and the full traversal
   proceeds once.

The important observation: *building the binder* (`Lam b`) was O(1), and
*every substitution that passed over this binder* while evaluating the outer
context was O(1).  The single traversal happens once, precisely when the binder
is opened.

---

## 8. What You Get for Free — `Generic1`

In `Tutorial.Scoped.Syntax`, the term type derives `Generic1`:

```haskell
data Tm (n :: Nat) where
    Var   :: Fin n -> Tm n
    Lam   :: Bind1 Tm Tm n -> Tm n
    -- ...
      deriving (Generic1, Eq, Show)

instance SubstVar Tm where
    var = Var

instance Subst Tm Tm where
    isVar (Var x) = Just (Refl, x)
    isVar _       = Nothing
```

The `Subst Tm Tm` instance has a default method body:

```haskell
applyE :: Env Tm m n -> Tm m -> Tm n
applyE = gapplyE   -- dispatches through Generic1
```

`gapplyE` first calls `isVar`: if the term is a variable, it looks it up in
the environment directly via `applyEnv env x` — the fast path.  Otherwise it
calls the generic machinery to recurse over all fields, applying `applyE`
recursively to each sub-term and the O(1) binder instance to each `Bind`.

In contrast, `Scratch.hs` requires a hand-written `applyE` that explicitly
dispatches on every constructor and manually calls `lift` at each binder.
With `rebound` you write `deriving Generic1` and two-line `SubstVar`/`Subst`
instances, and the library handles everything else.

---

## 9. Summary

| Technique | Where | What it does |
|---|---|---|
| Delayed substitution | `Bind v c pat n` | stores `Env v m n` in the binder; applying `applyE` is O(1) |
| Pattern field | `LocalName` in `Bind` | carries name hints for pretty-printing; `Eq` ignores them |
| Defunctionalized `Env` | `Rebound.Env.Lazy` | substitutions are data; enables smart composition |
| Smart composition | `comp` / `.>>` | fuses shifts, drops identities, re-associates |
| `applyOpt` | `Rebound.Env.Lazy` | skips traversal when the environment is the identity |
| `upN` / `up` | `Rebound.Env` | lifts an environment under `p` binders; recognises identity |
| `Generic1` | `Rebound.Generics` | derives `applyE` over all constructors automatically |
| `isVar` shortcut | `Subst` class | fast path: `applyE env (Var x)` → `applyEnv env x` |

The combination of these techniques means that:

- **Building** a binder (`bind1`, `Lam`) is O(1).
- **Passing** a substitution over a binder (`applyE env (Lam b)`) is O(1).
- **Opening** a binder (`getBody`, `instantiate1`) forces the accumulated
  substitution in a single pass over the body.
- **Identity environments** are detected and discarded without touching the
  term.
- **Consecutive shifts** are fused into a single `Inc` at composition time.

These are the same optimisations found in mature normalisers and type-checkers;
the `rebound` library packages them in a reusable, type-safe interface so that
every new language implementation gets them for free.
