# Implement your POPL paper (in Haskell)

This series of four 50-minute lectures covers how to represent and manipulate
lambda-calculus terms using well-scoped de Bruijn indices in Haskell. The goal
is to provide a practical basis for implementation, suitable for experimenting
with language and logic design.

The four lectures are:

1. The well-scoped lambda calculus from scratch
2. Where do well-scoped terms come from?
3. CPS: A scope-preserving translation
4. Efficient implementation using delayed and defunctionalized substitutions

The target audience is students and researchers who are familiar with lambda
calculi and functional programming (in Haskell, OCaml, Rocq, or Agda). Some
prior exposure to dependently typed programming (e.g. length-indexed vectors)
is helpful. Although some lectures make use of the
[rebound](https://hackage.haskell.org/package/rebound) Haskell library and
rely on Haskell-specific features, the key ideas apply to implementation in
any functional programming language.