# Agda port of rebound and the HS26 talk

An Agda transcription of `tutorial/main/src/talks/hs26/{Talk1,Talk2,Talk3}.hs`,
the part of `rebound/src` they need, and eight of the examples in
`rebound/examples`. The goal is to follow the Haskell as closely as Agda
allows, so that the places where the two languages genuinely differ stand
out.

This port was created by Claude Opus 5.

```
agda/
  rebound-agda.agda-lib     -- include paths: rebound, talks, examples
  rebound/                  -- port of the library
    Data/Prelude.agda       -- Maybe, Erased, ⊥, ⊤, Σ (Bool/String from Agda.Builtin)
    Data/Type/Equality.agda -- _≡_ / Refl / subst   (Haskell: (:~:))
    Data/Nat.agda           -- Nat, _+_, and the three monoid laws
    Data/Singleton.agda     -- erased singletons  (Haskell: SNat, SNatI)
    Data/Fin.agda           -- Fin, shiftN, weakenFin, weakenFinRight
    Data/Vec.agda           -- length-indexed lists
    Rebound/Lib.agda        -- re-exports
    Rebound/Classes.agda    -- Sized, TestEquality, PatEq, Strengthen, FV
    Rebound/Env.agda        -- the defunctionalized Env (Rebound.Env.Lazy)
    Rebound/Bind/Pat.agda   -- Bind, bind/getPat/getBody/instantiate
    Rebound/Bind/PatN.agda  -- PatN, Bind1/Bind2/BindN
    Rebound/Bind/Scoped.agda-- scoped patterns and telescopes
    Rebound/Bind/Single.agda-- the single-variable binder interface
    Rebound/Bind/Local.agda -- a binder that remembers the name
    Rebound/Context.agda    -- Ctx, emptyC, _+++_
    Rebound/MonadScoped.agda-- scope-indexed reader and state monads
    Data/LocalName.agda     -- user-supplied names, kept for printing
    Data/Scoped/List.agda   -- lists whose elements share a scope
    Rebound.agda            -- top-level re-export
  talks/
    Talk1.agda              -- environments as functions
    Talk2.agda              -- environments as shift lists (its own, local)
    Talk3.agda              -- using the library: patterns and branches
    Test.agda               -- runtime tests (compiled and run)
  examples/
    LC.agda                 -- untyped LC, several evaluation strategies
    LCLet.agda              -- let, letrec, telescopic and mutual let
    ScopeCheck.agda         -- named syntax to well-scoped syntax
    SystemF.agda            -- two scopes: type and term variables
    Pat.agda                -- constructor patterns, size not statically known
    PatGen.agda             -- the same, with the traversals Haskell derives
    PTS.agda                -- pure type system with Pi, Sigma and split
    DepMatch.agda           -- dependent types with nested pattern matching
    LinLC.agda              -- linear LC: usage tracked in scoped state
    PureSystemF.agda        -- System F, one scope, with a pretty printer
    TaggedSystemF.agda      -- System F, one scope, tagged types and terms
    LCWF.agda               -- substitution with a real termination proof
```

### Ported examples

Of the 14 examples tracked in the repository, eleven are ported and
exercised by `Test.agda`. The remaining three are listed with what each
would need. 

| Example | Status |
| --- | --- |
| `ScopeCheck`, `SystemF`, `LC`, `LCLet`, `Pat`, `PatGen`, `PTS`, `DepMatch`, `LinLC`, `PureSystemF`, `TaggedSystemF` | ported |
| `HOAS` | relies on overlapping instances and a functional dependency for its `⊆` class; Agda's instance search does neither |
| `LCQC` | QuickCheck properties — no Agda counterpart without porting a property-testing library |
| `FreeBound` | built on `GHC.TypeLits.TypeError` and type-level programming with no Agda analogue |

`examples/LCWF.agda` is not a port of anything: it is a standalone
demonstration that the termination pragma every other example carries can
be discharged. See "Discharging it, honestly" below.

Three of these are worth calling out.

`PatGen` is `Pat` again, except that in Haskell its `Subst`, `FV` and
`Strengthen` instances are *all* derived through `GHC.Generics` from a
one-line `isVar`. Agda has no comparable mechanism, so the port is
`Pat.agda` plus every one of those traversals written out — which is the
honest measure of what generic programming buys.

`Pat` and `PatGen` also show what Haskell's `SizeIndex` class is for.
Taking a branch apart needs both a `Sized (pat m)` instance and the
equation `Size (pat m) ~ m`, which Haskell supplies with a quantified
superclass. Agda has neither quantified constraints nor superclass
equations, so the `Branch` constructor stores both explicitly — the
dictionary, and an `@0` proof of the equation.

`LinLC`, `PureSystemF` and `TaggedSystemF` all run in scope-indexed
monads, and Haskell states those as classes:

```haskell
class (forall n. Monad (m n)) => MonadScopedReader e m | m -> e
class (forall n. Monad (m n)) => MonadScopedState  s m | m -> s
```

Both use a quantified superclass *and* a functional dependency, and Agda
has neither, so a faithful class port is impossible. `Rebound/MonadScoped.agda`
ports the two concrete transformers instead, specialized to the error
monad the examples actually use. The operations — `localS`, `asksS`,
`rescope`, `getsS` — and their meanings are the Haskell's; only the
class-level abstraction over them is gone.

`LCLet` turned up the sharpest Haskell-specific point in the set: its
`LetRec` and `LetMutRec` cases tie a knot,

```haskell
let v = instantiate (rec_rhs e) v in ...
```

which is meaningful only because Haskell is lazy — `v` is a cyclic value,
not a computation that runs forever. Agda has no recursive `let`, so the
port uses a recursive `where` definition under a pragma. It computes for
exactly the same reason the Haskell does: the GHC backend it compiles to
is lazy.

Built with **Agda 2.8.0** under `--erasure` (every file carries the
pragma). No standard library is required — only `Agda.Builtin.*`, which
ships with Agda.

`rebound/` passes `agda --safe` in full, as does `examples/LCWF.agda`.
The talks and the other examples do not, and for one reason only: the
termination pragmas discussed below.

```sh
cd agda
agda --compile --compile-dir=build talks/Test.agda   # checks talks + examples
./build/Test                                         # runs 38 checks
```

## Erasure

Scope indices are annotated `@0`, Agda's marker for data erased before
execution — the status those numbers already have in Haskell, where they
live at the type level. Agda enforces it:

```agda
bad : ∀ {@0 m} → Pat m → Nat
bad {m} _ = m
-- error: [VariableIsErased] Variable m is declared erased,
--        so it cannot be used here
```

One consequence is worth knowing, because it dictates a style choice:
**`rewrite` cannot be used over erased indices.** Every coercion in the
port therefore goes through `subst`, whose proof argument is declared
`@0`. Switching to `rewrite` fails twice over — it scrutinises the proof,
so an `@0` lemma is rejected outright:

```
error: [DefinitionIsErased] Identifier sym is declared erased,
       so it cannot be used here
```

and even given a non-erased proof layer, the with-abstraction has to
solve a relevant variable with a term built from erased data:

```
error: [SplitError.UnificationStuck] Cannot solve variable lhs of type
       Nat with solution S (m + k) because the solution cannot be used
       at relevant, unrestricted
```

The same definitions compile with `rewrite` as soon as the index is not
erased, so this is erasure's price, not a quirk of the encoding.

## Scoped patterns

`Rebound/Bind/Scoped.agda` ports `Rebound.Bind.Scoped`, whose patterns
bind variables *and* may refer to variables already in scope — what type
annotations and telescopes need. `examples/DepMatch.agda` is the port of
`examples/DepMatch.hs`, a dependently typed calculus with nested
dependent pattern matching for Sigma types, which exercises it.

Two places where the Agda is markedly shorter, both for the same reason —
Haskell is encoding a constraint that Agda states by construction:

- **`ScopedSized` needs no quantified-constraint trick.** The size of a
  scoped pattern must not depend on how many variables are in scope.
  Haskell says this with a quantified superclass plus a helper class
  (`EqSized`, and `EqScopedSized` again for the indexed version), the
  technique from [this post](https://blog.poisson.chat/posts/2022-09-21-quantified-constraint-trick.html).
  In Agda the independence is just where the field sits: `theScopedSize :
  Nat` mentions no scope, so there is nothing to constrain. Both helper
  classes disappear.

- **`TeleList` needs no constraints in its constructors.** Haskell stores
  `n + N0 ~ n` in `TNil` and `p2 + (p1 + n) ~ (p2 + p1) + n` in `TCons`
  so the equations are in scope when matching, with smart constructors to
  discharge them. Here the indices are as written, `nil`/`_<:>_` are the
  constructors, and the two equations are proved at the one place that
  needs them (`_<++>_`).

## Points of comparison

### Where Agda comes out ahead

- **Singletons.** The amounts stored in `Rebound.Env`'s
  `Weak` and `Inc` are not erased, so one `Nat` is both the index in
  the type and the number the code computes with. Haskell needs
  `Inc :: SNat m -> Env a n (m + n)`.

- **The arithmetic laws are proofs, not axioms, and can be erased.** `axiomPlusZ`,
  `axiomAssoc` and `axiomPlusS` in `Data/Nat.agda` are `@0` definitions:
  erased, so nothing runs; real proofs, so nothing is assumed. Haskell
  uses `unsafeCoerce`. 

- **Erased proofs need erased arguments.** Actually running a proof 
  in Haskell includes the overhead of running it, but also the overhead of 
  making those arguments available where the proof is needed. 

- **One generic singleton.** Recovering an erased number needs a runtime
  witness in both languages, but Haskell needs a bespoke singleton
  datatype per index type. The singletons library (not used here) can 
  automate this.

- **"Evidence is free" is stated in the type.** `testEquality` returns
  `Maybe (Erased _)`: the answer is data, the proof is not.
  GHC gets the same deal — `Refl` is a 0-bit value — but cannot say so.

### Where Agda costs more

- **Equational reasoning is explicit**. 
  Haskell writes `| Refl <- axiomAssoc @k @j @p` and
  lets GHC retype the branch silently; Agda names the motive and says
  where the rewrite happens.

- **Termination is asserted** — see below. Any nonterminating code in Agda
  can subvert Agda's entire type system. Proving that substitution terminates
  ranges from duplicative (must define a separate renaming) to difficult
  (delayed substitutions in bind require termination argument for ES 
  calculus).

- **No `deriving`,** so `Eq` for `Tm` (`eqTm`) is written out, and no
  `GHC.Generics`, so Talk 3 cannot replace `applyE` with a one-line
  `isVar`.


### Where the two agree

- **`Sized` is Haskell's class, field for field.** `Size` is only needed
  in types, so it is `@0`, and `size` must then reconstruct it and return
  a `Singleton` to tie the answer back to the index. Neither language
  needs a separate correctness lemma: `sizePat : Pat m → Singleton m`
  *is* the statement.
- **Appending needs the length at runtime** in both. Haskell takes it as
  an `SNatI` constraint and feeds it back with `withSNat`; `appendE`
  takes it as an ordinary argument. `patternMatch` threads the witness
  out of the recursive call in both, so the pattern is walked once.
- **The internally-verified core ports verbatim** — `Fin n` as a
  scope-safe index, `Env m n` as a scope-changing substitution, `Bind`
  with a suspended environment, `testEquality` producing index evidence
  as a by-product of a comparison we had to do anyway. 

## Termination

Haskell checks nothing here, and "non-termination by default" is on the
talk's list of what it gets right. Sixty-two definitions escape the
termination checker — 33 `TERMINATING` and 29 `NON_TERMINATING`. All of
them are in client code: `rebound/` needs none and passes `agda --safe`
in full, as does `examples/LCWF.agda`.

| What | Pragma | # | Why |
| --- | --- | --- | --- |
| every `eval` / `nf` / `whnf` / `norm`, and the type checkers that call them | `NON_TERMINATING` | 29 | genuinely partial — untyped or partially-typed calculi, and *should* be |
| every syntax's substitution traversal (`applyE`, `applyExp`, `applyTm`, `applyTy`, `applyAny`) | `TERMINATING` | 13 | mutually recursive with `comp`, which substitutes into terms stored in an environment |
| alpha-equivalence (`eqTm`, `eqExp`, `eqTy`) | `TERMINATING` | 5 | `getBody` applies the suspended substitution, so the body is not a subterm |
| `strengthenExp`, `appearsFreeExp` | `TERMINATING` | 5 | recurse through `Bind`, hence through `getBody` |
| small-step `step` | `TERMINATING` | 4 | calls `instantiate` / `findBranch`, whose results are subterms of nothing |
| bidirectional checkers (`ensureType`, `checkType`, `tc`) | `TERMINATING` | 4 | recurse on `getBody`, and `ensureType` is mutual with `inferType` |
| `DepMatch.patternMatch` | `TERMINATING` | 1 | the `PPair` case recurses on a *substituted* pattern |
| `PureSystemF.pp'` | `TERMINATING` | 1 | the pretty printer recurses under binders via `getBody` |

The count tracks the number of examples, not the difficulty: each ported
syntax contributes roughly one `TERMINATING` for its traversal plus one
`NON_TERMINATING` per evaluator it defines.

Most of them are honest. All 29 `NON_TERMINATING` sit on evaluators for
calculi that really do diverge, so the marker states a fact — and it is
the same fact the talk cites as a Haskell advantage. The 22
`TERMINATING`s are the unproven claims.

The two pragmas differ in what they cost. `TERMINATING` says "trust me,
this terminates" and Agda goes on unfolding the definition during
conversion checking; if the claim is wrong, type checking can loop and
the logic is unsound. `NON_TERMINATING` says "this may diverge" and Agda
refuses to unfold it at all while type checking — decidability survives,
but the function's results can then only be observed by running the
program, which is why `Test.agda` is a compiled test rather than a set of
`Refl` proofs.

Neither is logically safer: both still inhabit `⊥` (`loop : ⊥; loop =
loop` type-checks under either), and both are rejected by `--safe`. The
difference is purely operational.

Note that no *proof* in the port depends on one: every `_≡_`-producing
definition passes the checker on its own, and the pragmas sit only on
functions returning ordinary data (`Tm`, `Val`, `Env`, `Bool`, `Maybe`).

The `Talk1` and `Talk2` traversals could be discharged by giving renaming
and weakening their own passes, since the environments involved (`shift`,
`Shift k Id`) map variables to variables. The port keeps the Haskell's
definitions instead — those two parts of the talk are about what the code
looks like.

The rest are the real knot. `comp` recurses structurally on its first
argument and needs no pragma, but it substitutes into the terms stored
there, so a client's traversal and `comp` are mutually recursive through
a term that is a subterm of neither. No *structural* order sees that call
— but a *size* order does, and `examples/LCWF.agda` carries one through
and discharges the pragma outright.

### Where the knot actually is

`applyEnv` is now checked outright, with no instance in sight. The
library only ever suspends a composition with a `Weak` or an `Inc` on the
left — that is, a *renaming* — so the constructor records it:

```agda
data Ren : @0 Nat → @0 Nat → Set where
  RWeak : ∀ {@0 n} (m : Nat) → Ren n (m + n)
  RInc  : ∀ {@0 n} (m : Nat) → Ren n (m + n)

  _:<>_ : ∀ {@0 m n p} → Ren m n → Env a n p → Env a m p
```

A renaming can be pushed through a lookup without substituting, so

```agda
applyEnv (ρ :<> s) x = applyEnv s (applyRen ρ x)
```

is a plain structural recursion. `applyEnv` and `head` need no `Subst`
instance at all.

The remaining library functions that do take `Subst v v` — `comp` and
everything built on it — are checked *parametrically*: they call
`Subst.applyE` on an instance **variable**, so Agda records no call to
any particular definition and accepts them for any terminating `applyE`.
That is not a loophole; it is where the obligation gets handed to the
client. When the client supplies a concrete instance, Agda closes the
cycle and rejects it — which is exactly why the pragma sits on each
example's `applyE` and nowhere else. The assertion lands precisely where
the assumption is made.

That leaves exactly one place where the knot is real: `comp`'s cons case,

```agda
comp (Cons t s1) s2 = Cons (applyE s2 t) (comp s1 s2)
```

which substitutes into a term *stored in* the environment — a term that
is a subterm of neither argument. Client `applyE`s reach it through
`Subst v (Bind v c p)`, which composes the incoming environment with the
one suspended at the binder. So the `applyE` pragma in each example
survives, and it survives for a reason rather than an artifact.

Deferring the composition instead of performing it would discharge the
pragma, at the cost of the fusion that is the point of the
representation. Passing the traversal as an explicit argument does *not*
discharge it: Agda tracks a function passed by name, eta-expanded, or
wrapped in a record, and rejects all three. There is no laundering the
knot past the checker.

### Discharging it, honestly

`examples/LCWF.agda` proves it instead — no pragma in the file. The knot
has no structural order, but it has a size order:

```agda
size (Lam e body) = S (sizeE e + size body)
sizeE (Cons t s)  = S (size t + sizeE s)

applyA : (r : Env n m) (t : Exp n)     → Acc (sizeE r  + size t)   → Exp m
compA  : (s1 : Env m n) (s2 : Env n p) → Acc (sizeE s2 + sizeE s1) → Env m p
```

`size t < sizeE (Cons t s1)` is exactly what licenses the problem call.
One design detail halves the work: `compA`'s measure takes the *second*
environment first, which makes every obligation monotonicity in the right
summand — one lemma, and no commutativity or `subst` at any site.

The cost is ~50 lines of order and well-foundedness scaffolding (the port
depends on no standard library) plus the measure and the `Acc` threading.
So this is not the general λσ-calculus normalization problem: there,
composition is arbitrary; here it only ever pushes into stored terms, and
a plain size measure suffices.

Doing it for the library rather than a miniature would mean making the
measure a method of `Subst`, so that every instance owes both a measure
and its decrease proofs. `LCWF.agda` is the standalone demonstration
rather than that change.

A side benefit: because its substitution is *proved* terminating, Agda
will reduce it, so `LCWF`'s correctness checks are `Refl` proofs run by
the type checker. No other example can state its substitution results
that way — theirs are asserted, hence either unfoldable-but-untrusted or
(under `NON_TERMINATING`) not unfoldable at all.

## Naming and structural differences

Agda identifiers may not contain `.`, and a few Haskell operators clash
with Agda conventions:

| Haskell | Agda |
| --- | --- |
| `(.:)` | `_∷_` |
| `(.++)` | `_++_` |
| `(.>>)` | `_>>>_` |
| `(:~:)`, `Refl` | `_≡_`, `Refl` |
| `Vec n a` | `Vec a n` |
| `type Bind p n` (Talk 3) | `Bind p n`, with `Rebound.Bind.Pat` imported as `R` |

Two structural simplifications in the library, both flagged in the source:

- `applyOpt` resolves the `Subst` instance itself instead of taking the
  traversal as an argument (Haskell needs the extra parameter so the
  `GHC.Generics` path can share the optimization).
- `comp` reaches its two-argument optimizations by splitting the shift
  amount on the left first. Agda's coverage checker cannot split the
  second environment while the first leaves the shared scope index open,
  but once that index is `S _` the impossible cases on the right are
  ruled out by clash. Anything unmatched falls through to a suspended
  `_:<>_`, which is what that constructor is for.

Talk 2 defines `sym`, `cong` and `subst` itself rather than importing
them, since Part II is the section that is about them. It also keeps its
own shift-list `Env`, which is Part II's subject; the library uses the
defunctionalized representation that `Rebound.Env` imports by default.
