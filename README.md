# Rebound

`Rebound` is a variable binding library based on well-scoped de Bruijn indices.

This library is represents variables using the index type `Fin n`; a type of
(finite) bounded natural numbers. The key way to manipulate these indices is
using an *environment*, a parallel substitution similar to a function of
type `Fin n -> Exp m`. Applying an environment converts an expression that 
contains indices in scope `n` to one in scope `m`.

## Draft paper

See: [rebound-paper.pdf](./rebound-paper.pdf)

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
    where AST terms indicate binding structure through the use of types
    defined in this library. As a result the library provides a clean, uniform,
    and automatic interface to common operations such as substitution,
    alpha-equality, and scope change.

3. *Efficiency*: Behind the scenes, the library uses explicit substitutions
    (environments) to delay the execution of operations such as shifting and
    substitution. However, these environments are also accessible to library
    users who would like fine control over these operations.

4. *Accessibility*: This library comes with examples demonstrating how to use
    it effectively, for a number of different object languages that differ in
    their binding structure. Many of these are also examples of programming
    with Dependent Haskell.

## Organization of this repository

Each sub-directory contains a README with additional instructions, but here is a
high-level overview:
- [`rebound`](./rebound/README.md) contains the Haskell library itself, as well
  as some short [examples](./rebound/examples) showing how to use the library.
- [`piforall`](./piforall/README.md) contains two implementations of the
  `pi-forall` language. These implementations are the original one (using
  `unbound-generics`) and new one based on `rebound`.
- [`benchmark`](./benchmark/README.md) contains many implementations of the
  lambda-calculus, using different libraries and techniques. It also contains
  code to benchmark the normalization of lambda-terms in each of these
  implementations.

## Benchmarks

### Table 1

**To run**: Consult this [file](./benchmark/README.md) for instructions.

The implementations mentioned in the paper are:
- [Env.Strict.BindV](benchmark/lib/Rebound/Env/Strict/BindV.hs)
- [Env.Strict.EnvV](benchmark/lib/Rebound/Env/Strict/EnvV.hs)
- [Env.Strict.EnvGenV](benchmark/lib/Rebound/Env/Strict/EnvGenV.hs)
- [Env.Strict.Bind](benchmark/lib/Rebound/Env/Strict/Bind.hs)
- [Env.Strict.Env](benchmark/lib/Rebound/Env/Strict/Env.hs)
- [Env.Strict.EnvGen](benchmark/lib/Rebound/Env/Strict/EnvGen.hs)
- [NBE.KovacsScoped](benchmark/lib/NBE/KovacsScoped.hs)
- [DeBruijn.BoundV](benchmark/lib/DeBruijn/BoundV.hs)
- [DeBruijn.Bound](benchmark/lib/DeBruijn/Bound.hs)
- [Named.Foil](benchmark/lib/Named/Foil.hs)
- [Unbound.Gen](benchmark/lib/Unbound/Gen.hs)
- [Unbound.NonGen](benchmark/lib/Unbound/NonGen.hs)

### Table 2 (partial)

**To run**: Consult this [file](./benchmark/README.md) for instructions.

The implementation of the main environments are:
- [Functional](rebound/src/Rebound/Env/Functional.hs)
- [Lazy](rebound/src/Rebound/Env/Lazy.hs)
- [LazyA](rebound/src/Rebound/Env/LazyA.hs)
- [LazyB](rebound/src/Rebound/Env/LazyB.hs)
- [Strict](rebound/src/Rebound/Env/Strict.hs)
- [StrictA](rebound/src/Rebound/Env/StrictA.hs)
- [StrictB](rebound/src/Rebound/Env/StrictB.hs)

### Table 3

**To run**: Consult this [file](./piforall/README.md) for instructions.

The pi-forall files used are:
- [AVL](piforall/pi/examples/AVL_F.pi)
- [DepAvl](piforall/pi/examples/AVL.pi)
- [Compiler](piforall/pi/examples/Compiler.pi)
- [Lennart](piforall/pi/examples/Lennart.pi)
- [CompCk](piforall/pi/examples/cCompiler.pi)
