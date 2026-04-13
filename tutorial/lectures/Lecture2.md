# Lecture 2: Pattern Binding (plus scope checking)

## Modules referenced in this lecture

- [Tutorial.Scoped.Syntax](https://github.com/sweirich/rebound/blob/main/tutorial/main/src/Tutorial/Scoped/Syntax.hs)
- [Tutorial.Scoped.ScopeCheck](https://github.com/sweirich/rebound/blob/main/tutorial/main/src/Tutorial/Scoped/ScopeCheck.hs)
- [Tutorial.Named.Syntax](https://github.com/sweirich/rebound/blob/main/tutorial/main/src/Tutorial/Named/Syntax.hs)
- [Tutorial.Named.Parser](https://github.com/sweirich/rebound/blob/main/tutorial/main/src/Tutorial/Named/Parser.hs)
- [Tutorial.Named.PP](https://github.com/sweirich/rebound/blob/main/tutorial/main/src/Tutorial/Named/PP.hs)

## Overview and Goals

In Lecture 1 we represented terms in a simple language using de Bruijn indices
and implemented an evaluator.

But will this work at scale, for more sophisticated languages, which might
include, say, pattern matching?

And, when working on a real implementation, we want to be able to parse and
pretty-print our AST. While full parsing and pretty-printing is out of scope
(heh) for this tutorial, we do want to consider how well scoped terms interact
with these operations. In particular, if a user writes their code with
explicit names, we need to ensure that all names are in scope. Similarly, to
print code nicely, we want to preserve the names that the user originally
wrote.

The goals of this lecture are to:

- cover more practical aspects of working with de Bruijn indices: maintaining
  user-supplied variable names and generating well-scoped syntax trees

- demonstrate pattern binding and sophisticated use of the `rebound` library

## 1. Parsing and pretty-printing scoped syntax

The module `Tutorial.Scoped.ScopeCheck` provides a parser and pretty printer
for well-scoped abstract syntax trees defined in `Tutorial.Scoped.Syntax` (and
are similar to the AST from Lecture 1).

However, so that we can only talk about scoping, these operations are broken up 
into two steps, through the use of a parallel named AST.

In other words, to parse, we divide the work into parsing raw strings into a
representation that uses strings for variable names, and a separate
*projection* function that performs scope checking and produces well-scoped
syntax trees.

             parse                      project
    String ------------> Named Syntax --------------> Scoped Syntax 

In this process, two sorts of failures could occur: perhaps the string doesn't
parse, or perhaps one of the variables is out of scope.  This process also
resolves *shadowing*, where the name of one variable hides another.

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
printing.

When a user writes `\x. x` and we scope-check it, we produce:

```haskell
S.Lam (S.bind (S.LocalName "x") (S.Var FZ))
```

This way, the string `"x"` is stored inside the binder as a `LocalName`.  When
later printed, the output reads `\ x. x`.


A local name is just a wrapper for a string, but we want to make sure that the
strings do not interfere with alpha-equivalence.

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

### The `Pat.Bind` interface

In `Tutorial.Scoped.Syntax`, we define the single binder type `Bind1 n` as
`Pat.Bind Tm Tm LocalName n`, using a type defined in the `rebound` library.
For convenience, we abbreviate this type as `Bind11`.

This example is a specific instance of *pattern binding*: the pattern is a
single local name, stored alongside the body of the binder. The abstract type
enforces access to the body only through smart constructors and accessors.

| Function | Type | Description |
|---|---|---|
| `bind` | `LocalName -> Tm (S n) -> Bind1 n` | package a body under a binder |
| `getPat` | `Bind1 n -> LocalName` | retrieve the stored name |
| `getBody` | `Bind1 n -> Tm (S n)` | access the body of the binder |
| `instantiate1` | `Bind1 n -> Tm n -> Tm n` | open the binder by substituting a term |

However, pattern binding is a general construct and these operations are more generic than the types listed in the table above.


## 3. General pattern binding

In our simple language (from module `Tutorial.Scoped.Scratch`), we had
separate constructors for pattern matching unit, pair and sum values. We would
like to combine these into a single `Match` expression that allows nested
patterns. This requires a pattern datatype and a way to bind the variables
introduced by a pattern in the branch body.

### The `Pat` and `Branch` datatypes

```haskell
data Pat (m :: Nat) where
    PVar  :: LocalName -> Pat N1
    PUnit :: Pat N0
    PPair :: Pat m1 -> Pat m2 -> Pat (m2 + m1)
    PInj  :: Int -> Pat m -> Pat m
```

In the type `Pat m` index `m` is the number of variables *bound* by the pattern, tracked at
the type level.  `PVar` binds one variable, `PUnit` binds none, and `PPair`
binds the sum of its sub-pattern counts.  Note the order in the type of
`PPair`: variables from the *right* sub-pattern (`m2`) are innermost
(have the smaller de Bruijn indices), so they come first in the sum `m2 + m1`.
`PInj` is a tag for injection patterns and passes the binding count through
unchanged.

```haskell
data Branch (n :: Nat) where
    Branch :: Pat.Bind Tm Tm (Pat m) n -> Branch n
```

`Bind Tm Tm (Pat m) n` is the pattern-binding abstraction provided by
`Rebound.Bind.Pat`.  For simplicity, we use the type abbreviation 
`BindP m n` to stand for this type.

This type pairs a pattern of type `Pat m` with a body of type
`Tm (m + n)`, where the body's first `m` free variables are the ones the
pattern binds.  The existential over `m` is hidden inside `Branch`, so
callers do not need to know the pattern's arity statically.

As above, we can use the same operations for working with pattern binders, but this 
time the operations have the following type:

| Function | Type | Description |
|---|---|---|
| `bind` | `Pat m -> Tm (m + n) -> BindP m n` | construct a branch |
| `getPat` | `BindP m n -> Pat m` | extract the pattern |
| `getBody` | `BindP m n -> Tm (m + n)` | extract the body |
| `instantiate` | `BindP m n -> Env Tm m n -> Tm n` | open by substituting an environment |

### The `Sized` instance

To create the general types for these operations, `rebound` needs to know the number 
of variables bound in any type used as a pattern. For types such as `Pat m`, this 
is easy --- we just use `m`. However, it is less obvious that the type 
`LocalName` binds exactly one variable.

Therefore, `rebound` uses the `Sized` class to calculate this information, both in types 
and also dynamically, using a singleton.

```haskell

instance Sized LocalName where
    type Size LocalName = N1
    
    size :: LocalName -> SNat (Size (LocalName))
    size _ = s1


instance Sized (Pat m) where
    type Size (Pat m) = m

    size :: Pat m -> SNat (Size (Pat m))
    size (PVar _)      = s1
    size PUnit         = s0
    size (PPair p1 p2) = sPlus (size p2) (size p1)
    size (PInj _ p)    = size p
```



The type `SNat` and type class `SNatI` provide *runtime* access to 
type-level natural numbers. Haskell is not a full-spectrum 
dependently-typed language, so numbers that appear in types cannot 
be pattern matched at runtime.  

```
data SNat n where
   SZ :: SNat Z
   SS :: SNatI n1 => SNat (S n1)
```

The `SNatI n` acts as an implicit argument, and uses Haskell's type inference
to automatically supply runtime naturals when possible. The operations `snat`
and `withSNat` convert between implicit and explicit arguments.

```
>>> :t snat
snat :: SNatI n => SNat n

>>> :t withSNat
withSNat :: SNat n -> (SNatI n => r) -> r
```

There are singleton versions of various operations for 
natural numbers.  For example, we can add them:

```
>>> :t sPlus
sPlus :: SNat n1 -> SNat n2 -> SNat (n1 + n2)
```

Above, in the definition of `size` for the `Pat` type, 
`sPlus (size p2) (size p1)` mirrors the type `m2 + m1` from the `PPair`
constructor, keeping the runtime value and the type-level index in sync.


We can also test them for equality. The (overloaded) 
`testEquality` operation has a heterogenous type and 
produces a proof of equivalence for its *indices* when its 
arguments are equal.

```
>>> :t testEquality @SNat
testEquality @SNat :: TestEquality SNat => SNat a -> SNat b -> Maybe (a :~: b)
```

## 4. Alpha-equivalence for branches and patterns

We cannot derive `Eq` automatically for `Pat` or `Branch` because of the
dependent index `m`. 

When comparing branches, intuitively, we want to compare their patterns 
and their bodies. We would like to define an instance declaration like this:

```
-- Two branches are equal when their patterns are equal and their 
-- bodies are equal
instance Eq (Branch n) where
  Branch b1 == Branch b2 = 
      getPat b1 == getPat b2 && getBody b1 == getBody b2
```

However, this instance does not type check. The patterns in the two branches may 
bind different numbers of variables. Therefore, they have different types. So we need 
a heterogenous equality operation.

### `testEquality`: heterogeneous pattern equality

Instead, we can create an instance of the `TestEquality` class. This instance
compares the patterns for equality and also returns a *proof* that they bind
the same number of variables.

```haskell
instance TestEquality Pat where
  testEquality :: Pat a -> Pat b -> Maybe (a :~: b)
  testEquality (PVar x) (PVar y) = return Refl
  testEquality PUnit PUnit = return Refl
  testEquality (PInj i p) (PInj j p') | i == j = testEquality p p'
  testEquality (PPair p1 p2) (PPair p1' p2') = do
    Refl <- testEquality p1 p1'
    Refl <- testEquality p2 p2'
    return Refl
  testEquality _ _ = Nothing
```
  
Notice that `PVar` patterns are always considered equal regardless of the
stored name—consistent with `LocalName`'s trivial `Eq` instance.

The returned proof is exactly what we need to be able to compare the bodies 
of the pattern with the usual `Eq` type class.

```haskell
instance Eq (Branch n) where
  (==) :: Branch n -> Branch n -> Bool
  Branch b1 == Branch b2 = 
      case testEquality (getPat b1) (getPat b2) of
        Just Refl -> getBody b1 == getBody b2
        Nothing -> False
```


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

In particular, in the case of a `Match` expression, `findBranch` iterates
through the list of branches and comparing the value using the `patternMatch`
operation with each pattern. If this comparison is successful, it returns an
*environment* mapping each variable bound in the patter with a subterm of the 
matched value.

```haskell
findBranch :: Tm n -> [Branch n] -> Maybe (Tm n)
findBranch _ [] = Nothing
findBranch e (Branch b : rest) =
    case patternMatch (getPat b) e of
        Just r  -> Just (instantiate b r)
        Nothing -> findBranch e rest
```

More generally `patternMatch` compares a pattern against a value and, on
success, returns an *environment* `Env Tm m n` — a mapping from the `m`
pattern variables to `Tm n` values.


## 6. Historical Notes


**Scope checking as a compiler pass.** The idea of converting named surface syntax to an internal nameless or index-based form is standard in compiler design. Early Lisp interpreters used association lists (`alist`) to map symbol names to values at runtime — the direct ancestor of the `[(String, Fin n)]` context used in `projectTmWith`. In modern compilers this conversion is a distinct front-end pass, often called *name resolution* or *scope analysis*, that runs after parsing and before type checking, and uses a more efficient data structure.

**Singleton types and `SNatI`.** To use a type-level natural number `n :: Nat` at runtime — e.g., to enumerate `Fin n` — one needs a *singleton*: a runtime value that mirrors the type. Simulating this in Haskell was described by McBride (["Faking It: Simulating Dependent Types in Haskell"](https://www.cambridge.org/core/journals/journal-of-functional-programming/article/faking-it-simulating-dependent-types-in-haskell/A904B84CA962F2D75578445B703F199A), 2002) and later systematized in the [`singletons` library](https://hackage.haskell.org/package/singletons) ([Eisenberg and Weirich, "Dependently Typed Programming with Singletons", 2012](https://dl.acm.org/doi/10.1145/2430532.2364522)). The `SNatI` typeclass and `SNat` type used by `genTm` follow this pattern.


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

**2. Extending the conversions with `let`.** Extend `projectTmWith` and `injectTmWith` in `Tutorial.Scoped.ScopeCheck` to handle a `let`-expression.  Assume you have already added `Let :: Tm n -> Bind1 n -> Tm n` to `Tutorial.Scoped.Syntax` and `N.Let :: String -> N.Tm -> N.Tm -> N.Tm` to the named syntax.

- How does the treatment of `let` compare to `lam` in each direction?

- Does `prop_project_round_trip` still hold after this change?  Why or why not?






