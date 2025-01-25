# Autoenv

*NOTE: this library is a work in progress. The interface is still under active 
development and will change.*

This is a variable binding library based on well-scoped de Bruijn indices and environments.

This library is designed to represent variables using the type `Fin n`; a type of 
bounded natural numbers. It represents simultaneous substitutions (also called 
*environments*) as functions of type `Fin n -> Exp m`. This type is a parallel substitution 
mapping all indices smaller than n to expressions with free variables smaller than m.

## Design goals 

The goal of this library is to be an effective tool for language experimentation. Say you 
want to implement a new language idea that you have read about in a PACMPL paper? This library
will help you put together a prototype implementation quickly.

1. *Correctness*: This library uses Dependent Haskell to statically track the scopes of 
    bound variables. Because variables are represented by de Bruijn indices, scopes are 
    represented by natural numbers, bounding the indices that can be used. If the scope
    is 0, then the term must be closed. 
    

2. *Convenience*: The library is based on a type-directed approach to binding, where 
    AST terms can indicate binding structure through the use of types defined in this library. 
    As a result the library provides a clean, uniform, and automatic interface to 
    common operations such as substitution, alpha-equality, and scope change. 
    (TODO: Use datatype generic programming to automate type class instances).

3. *Efficiency*: Behind the scenes, the library uses explicit substitutions (environments) 
    to delay the execution of operations such as shifting and substitution. However, 
    these environments are accessible to library users who would like fine control over 
    when these operations.
    (TODO: improve efficiency by changing the representation of environments and natural 
    numbers.)

3. *Accessibility*: This library comes with tutorials and examples demonstrating 
    how to use it effectively. Many of these tutorials are also examples of programming
    with Dependent Haskell.

## Tutorials and Examples

1. [Untyped lambda calculus](examples/LC.hs)

Defines the syntax and substitution functions for the untyped lambda calculus. Uses these definitions to implement several interpreters.

2. [Scope checking](examples/ScopeCheck.hs)

Demonstrates how to convert a "named" expression to a well-scoped expression.

3. [Untyped lambda calculus with pattern matching](examples/Pat.hs)

Extends the lambda calculus example with pattern matching. 

4. [Untyped lambda calculus with let rec and nested lets](examples/LCLet.hs)

Example of advanced binding forms: recursive definitions and sequenced definitions.
(TODO: mutual recursion?)

4. [Simple implementation of dependent types](examples/PTS.hs)

An implementation of a simple type checker for a dependent-type system. Language includes Pi and Sigma types.

5. [PiForall](examples/PiForall.hs)

A simplification of the [pi-forall](https://github.com/sweirich/pi-forall) language, which includes dependent pattern matching.

## Related libraries

- [Bound](https://hackage.haskell.org/package/bound) 

Another scope-safe approach to de Bruijn indices in Haskell. Uses few language extensions by encoding type indices using nested datatypes. Efficiency comes from the addition of an explicit "shift" operator for terms. 

- [Unbound](https://hackage.haskell.org/package/unbound-generics)

Uses locally-nameless reprsentation. Inspiration for the type-direct approach to the binding interface found here. Not-scope safe so easy to get started. Working with this version requires a monad for fresh name generation. Can be slow. 

- [binder](https://hackage.haskell.org/package/binder)

Uses HOAS. 
