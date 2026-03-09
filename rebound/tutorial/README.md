Implement your POPL paper

Four lectures on using well-scoped de Bruijn indices in a simple implementation of an untyped 
lambda calculus. 

The target audience for these lectures are begining PhD students and researchers who are familiar 
with functional programming in Haskell, OCaml, Rocq, or Agda. They are also familiar with simple dependently typed programming (i.e. using length-indexed vectors and fin).

1. Basic definitions: abstract syntax (Simple.Syntax) and interpreter (Simple.Eval)

The first lecture starts with an empty buffer and defines the abstract syntax for a well-scoped 
term and type representation from scratch. It doesn't use the rebound library, but develops the appropriate definitions using a simple env type based on functions. 

At the end of the lecture, it replaces the hand rolled definitions with functions and type class definitions from the Rebound library. 

The goal of the lecture is to introduce the basic definitions with the simplest implementation to provide a model.

2. Working with well-scoped indices: scope checker (Simple.ScopeCheck), random generation (Simple.Gen)
3. Advanced usage: scope-preserving translation (Simple.CPS)
4. Efficient implementation: delayed & reified substitutions (Rebound.Bind.Simple, Rebound.Env.Internal)