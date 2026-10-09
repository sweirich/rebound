# Rebound

`Rebound` is a variable binding library based on well-scoped de Bruijn indices.

This library is represents variables using the index type `Fin n`; a type of
(finite) bounded natural numbers. The key way to manipulate these indices is
using an *environment*, a parallel substitution similar to a function of
type `Fin n -> Exp m`. Applying an environment converts an expression that 
contains indices in scope `n` to one in scope `m`.

## Paper

Noé De Santo and Stephanie Weirich. 2025. Rebound: Efficient, Expressive, and
Well-Scoped Binding. In *Proceedings of the 18th ACM SIGPLAN International
Haskell Symposium (Haskell '25)*, October 12–18, 2025, Singapore. ACM, New
York, NY, USA, 38–52. <https://doi.org/10.1145/3759164.3759348>

A draft of the paper is included in this repository as
[rebound-paper.pdf](./rebound-paper.pdf), and a preprint is available as
[arXiv:2509.13261](https://arxiv.org/abs/2509.13261).

```bibtex
@inproceedings{desanto2025rebound,
  author    = {De Santo, No{\'e} and Weirich, Stephanie},
  title     = {Rebound: Efficient, Expressive, and Well-Scoped Binding},
  booktitle = {Proceedings of the 18th ACM SIGPLAN International Haskell
               Symposium},
  series    = {Haskell '25},
  year      = {2025},
  pages     = {38--52},
  publisher = {ACM},
  address   = {New York, NY, USA},
  doi       = {10.1145/3759164.3759348}
}
```

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
  as many short [examples](./rebound/examples) showing how to use the library.
- [`piforall`](./piforall/README.md) contains two implementations of the
  `pi-forall` language. These implementations are the original one (using
  `unbound-generics`) and new one based on `rebound`.
- [`benchmark`](./benchmark/README.md) contains many implementations of the
  lambda-calculus, using different libraries and techniques, including 
  `rebound`. It also contains code to benchmark the normalization of 
  lambda-terms using each of these implementations.
- [`tutorial`](./tutorial/README.md) contains the companion code and lecture
  notes for the four-lecture tutorial "Implement your POPL paper (in
  Haskell)". The rendered tutorial website is at
  <https://sweirich.github.io/rebound/>.
- [`talks`](./talks/README.md) contains the Haskell source for talks about
  `rebound`, one directory per talk.
- [`agda`](./agda/README.md) contains an Agda translation of the library,
  several of its examples, and the Haskell Symposium 2026 talk.
