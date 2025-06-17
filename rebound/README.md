# Rebound


`Rebound` is a variable binding library based on well-scoped de Bruijn indices
and environments.

This library is represents variables using the index type `Fin n`; a type of
bounded natural numbers. The key way to manipulate these indices is using an
*environment*, a simultaneous substitutions similar to a function of type `Fin n
-> Exp m`. Applying an environment converts an expression in scope `n` to one in
scope `m`.

## Design goals

The goal of this library is to be an effective tool for language
experimentation. Say you want to implement a new language idea that you have
read about in a PACMPL paper? This library will help you put together a
prototype implementation quickly.

1. *Correctness*: This library uses Dependent Haskell to statically track the
    scopes of bound variables. Because variables are represented by de Bruijn
    indices, scopes are represented by natural numbers, bounding the indices
    that can be used. If the scope is 0, then the term must be closed.

2. *Convenience*: The library is based on a type-directed approach to binding,
    where AST terms can indicate binding structure through the use of types
    defined in this library. As a result the library provides a clean, uniform,
    and automatic interface to common operations such as substitution,
    alpha-equality, and scope change.

3. *Efficiency*: Behind the scenes, the library uses explicit substitutions
    (environments) to delay the execution of operations such as shifting and
    substitution. However, these environments are accessible to library users
    who would like fine control over when these operations.

4. *Accessibility*: This library comes with several examples demonstrating how
    to use it effectively. Many of these are also examples of programming with
    Dependent Haskell.

## Examples

### Calculi

1. [Untyped lambda calculus](examples/LC.hs)

   Defines the syntax and substitution functions for the untyped lambda
   calculus. Uses these definitions to implement several interpreters.

2. [Untyped lambda calculus with let rec and nested lets](examples/LCLet.hs)

   Example of advanced binding forms: recursive definitions and sequenced
   definitions.

3. [Untyped lambda calculus with pattern matching](examples/Pat.hs)

   Extends the lambda calculus example with pattern matching.

4. [System F](examples/SystemF.hs)

   Working with two separate scopes (type and term variables) is tricky. This
   example shows one way to do it.

5. [Pure System F](examples/PureSystemF.hs)

   An alternative way of defining System F, using one single syntactic class.
   Also demonstrates how to use the `ScopedReader` monad for typechecking and
   pretty-printing.

6. [Simple implementation of dependent types](examples/PTS.hs)

   An implementation of a simple type checker for a dependent-type system.
   Language includes Pi and Sigma types.

7. [Dependent Pattern Matching](examples/DepMatch.hs)

   A dependent type system with nested, dependent pattern matching. Patterns may
   also include scoped terms.

8. [Linear Lambda Calculus](examples/LinLC.hs)

   A linear version of the (simply typed) lambda calculus. Demonstrates how to
   thread a typing context using the `ScopedState` monad.

### Working with well-scoped expressions

1. [Scope checking](examples/ScopeCheck.hs)

   Demonstrates how to convert a "named" (or _nominal_) expression to a
   well-scoped expression.

2. [QuickCheck](examples/LCQC.hs)

   Demonstrates the use of well-scoped terms with
   [QuickCheck](https://hackage.haskell.org/package/QuickCheck).

3. [HOAS](examples/HOAS.hs)

   Demonstrates how to layer a HOAS representation on top of a de Bruijn
   representation. Based on Conor McBride's ["Classy
   Hack"](https://mazzo.li/epilogue/index.html%3Fp=773.html).

4. [PatGen](examples/PatGen.hs)

   A variant of the [Pat](examples/Pat.hs) example, which demonstrates how
   generic programming can be used to derive some definitions.

## Related libraries

- [Bound](https://hackage.haskell.org/package/bound)

  `Bound` is the most closely related library. Like `Rebound`, it is a
  scope-safe approach to de Bruijn indices in Haskell. The key difference is
  that `bound` requires fewer language extensions by using nested datatypes
  instead of GADTs. Use this library if you would like to avoid extensions such
  as `GADTs`, `DataKinds`, and `TypeFamilies`.

- [Unbound-Generics](https://hackage.haskell.org/package/unbound-generics)

  The `Unbound` library uses a locally-nameless reprsentation. `Rebound` draws
  inspiration for its design from the type-directed approach to the binding
  interface found in `Unbound`. However, `Unbound` is not not-scope safe. As a
  result it is easier to get started. However, working with a locally nameless
  representation requires a monad for fresh name generation. It also can be
  slow.

- [Foil and Free Foil](https://hackage.haskell.org/package/free-foil)

  GHC internally uses a *nominal* representation of binding, where both bound
  and free variables are represented by names. In this approach, users must
  rename the bound variable in abstraction if it is already in the current
  scope.

- [binder](https://hackage.haskell.org/package/binder)

  Uses HOAS.
