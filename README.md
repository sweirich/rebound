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

4. *Accessibility*: This library comes with several examples demonstrating
    how to use it effectively. Many of these are also examples of programming
    with Dependent Haskell.

## Organization of this repository

Each sub-directory contains a README with additional instructions, but here is a
high-level overview:
- [`rebound`](./rebound/README.md) contains the Haskell library itself, as well
  as some short [examples](./rebound/examples) showing how to use the library.
- [`piforall`](./piforall/README.md) contains two implementations of the
  `pi-forall` language. These implementations are the original one (using
  `unbound-generics`) and new one based on `rebound`.
- [`benchmark`](./benchmark/README.md) contains many implementation of the
  lambda-calculus, using different libraries and techniques. It also contains
  code to benchmark the normalization of lambda-terms in each of these
  implementations.