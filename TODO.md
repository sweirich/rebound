# TODOs and Design decisions

(In no particular order.)

- Replace axioms about natural numbers with type checker nat plugin
- Improve efficiency by changing the representations of nats

- Use datatype generic programming to automate type class instances
  (a la unbound-generics)

- Make type class for alpha-equivalence, comparison

- Improve efficiency by changing the representations of environments and nats

- Add benchmarks
   - make new entries in lambda-n-ways for this library

- Add testsuite for correctness

- Extend PiForall example to include arbitrary datatype definitions and exhaustivity checking to further stress the library
- Update PiForall example to take advantage of explicit substitutions

- More examples:  mutual recursion, MLTT, DOT, OO language? 

- Change name from `autoenv` to something else? rebound? 

- Rationalize naming and use of implicit/explicit singleton nats

- Rationalize order of arguments for unbindWith like operations

- Simplified interface for pattern binding when patterns do not include embedded terms

- More binding types (Rec, etc) to hide index operations in library
  (See Unbound library)

- Improve efficiency by adding GHC pragmas for unboxing, inlining, strictness, fusion based on profiling


