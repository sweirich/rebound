# TODOs and Design decisions

(In no particular order.)

- Replace axioms about natural numbers with type checker nat plugin

- Use datatype generic programming to automate type class instances
  (a la unbound-generics)

- Make type class for strengthening, free variable calculation, alpha-equivalence

- Improve efficiency by changing the representations of environments and nats

- Add benchmarks

- Add testsuite for correctness

- More examples:  mutual recursion, MLTT, DOT, OO language? 

- Change name from `autoenv` to something else? rebound? 

- Rationalize naming and use of implicit/explicit singleton nats

- Simple interface for pattern binding when patterns do not include embedded terms

- More binding types (Rebind, Rec, etc) to hide index operations in library
  (See PiForall)

- Add GHC pragmas for unboxing, inlining, strictness, fusion based on profiling

