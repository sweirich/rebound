# Autoenv

A variable binding library based on well-scoped de Bruijn indices and environments.

This library is designed to represent variables using the type `Fin n`; a type of 
bounded natural numbers. It represents simultaneous substitutions (also called 
*environments*) as functions of type `Fin n -> Exp m`. This type is a parallel substitution 
mapping all indices smaller than n to expressions with free variables smaller than m.

## Tutorials and Examples

1. [Untyped lambda calculus](examples/LC.hs)

Defines the syntax and substitution functions for the untyped lambda calculus. Uses these definitions to implement several interpreters.

2. [Scope checking](examples/ScopeCheck.hs)

3. [Untyped lambda calculus with pattern matching](examples/Pat.hs)

4. [Partial implementation of dependent types](examples/PTS.hs)






