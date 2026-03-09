# Implement your POPL paper

Four lectures on using well-scoped de Bruijn indices in a simple implementation of an untyped 
lambda calculus. 

The target audience for these lectures are 
begining PhD students and researchers who are familiar 
with functional programming in Haskell, OCaml, Rocq, or Agda. They are also familiar with simple dependently typed programming (i.e. using length-indexed vectors and fin).

1. Basic definitions: abstract syntax (Scoped.Syntax) and interpreter (Scoped.Eval)
2. Where do well-scoped terms come from? scope checker (Scoped.ScopeCheck), random generation (Scoped.Gen)
3. CPS: A look at scope-preserving translation (Scoped.CPS)
4. Efficient implementation: delayed & reified substitutions (Rebound.Bind.Simple, Rebound.Env.Internal)