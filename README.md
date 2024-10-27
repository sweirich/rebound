# Autoenv

A variable binding library based on well-scoped indices and environments.

Variables are represented by de Bruijn indices, of type `Fin n`. Substitutions
are represented by functions of type `Fin n -> Exp m`. This is a parallel substitution 
mapping all indices smaller than n to expressions in scope m.

See (LC)[src/LC.hs] for an example of this library in action. 




