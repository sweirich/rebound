# Lambda-Calculus cooked **n**-ways

This repository is focussed on capture-avoiding substitution and
alpha-equivalence for the untyped lambda calculus.  It contains benchmarks and
implementations of many different implementation strategies and existing
libraries for binding support.

History: The repo was inspired by and initially derived from Lennart
Augustsson's unpublished draft paper "Lambda-calculus Cooked Four Ways" and was
originally forked from https://github.com/steshaw/lennart-lambda.

## Compiling the library

This library can be compiled using the stack tool.

The command:
```
stack build
```
will compile the library and produce the executable that can be used for
benchmarking.

## Selecting the implementations to run

The source module [Suite](lib/Suite.hs) imports all of the implementations and
creates the test/benchmark suite. Modify the variable `impls` in this file to
include or exclude various implementations from testing and benchmarking.

## Running the test suite

The correctness of the implementations is ensured through quickcheck and unit
testing. The module [Main](test/Main.hs) in the `test/` subdirectory defines
these tests. To run them:

    stack test

The directory `lams/` contains files of non-normalized lambda-calculus terms
that can be used for testing and for benchmarking. In each case, if the file is
`test.lam` then a matching file `test.nf.lam` contains the normalized version of
the term.

Unit tests based on normalization:
- a single large term (lennart.lam).
- random terms with a small number of substitutions during normalization (onesubst, twosubst...)
- random terms with a large number of substitutions during normalization (random15, random20)
- specially constructed terms (capture10, constructed20)
- terms that reveal a bug in some implementation (tX, tests, regression)

QuickChecks:
- conversion from/to named representation is identity on lambda terms
- freshened version of random lambda term is alpha-equivalent to original
- normalization on randomly-generated lambda term matches a reference version

## Running the benchmarks from the paper

### Table 1

In [Suite.hs](lib/Suite.hs), change `impls` as follows:
```
impls = rebound_comparison
```
To ensure the implementations' correctness, run
```
stack test
```
To benchmark the implementations, run
```
make normalize
```
The result are in `results/<MACHINENAME>/rebound_comparison/output.txt`

### Table 2 (partial)

In [Suite.hs](lib/Suite.hs), change `impls` as follows:
```
impls = rebound_strict_envV
```
To ensure the implementations' correctness, run
```
stack test
```
To benchmark the implementations, run
```
./bencheval.sh
```
The result are in `results/ablate/rebound_strict_envV/main`

This will benchmark all `main/...` implementations.

## Anatomy of an implementation:

Every implementation in this suite matches the following interface:
```
data LambdaImpl = forall a. NFData a =>
  LambdaImpl
    { impl_name :: String,               -- module name
      impl_fromLC :: LC IdInt -> a,
      impl_toLC :: a -> LC IdInt,
      impl_nf :: a -> a,
      impl_nfi :: Int -> a -> Maybe a,
      impl_aeq :: a -> a -> Bool,
      impl_eval :: a -> a  (optional)
    }
```
Given some type for the implementation `a`, we need to be able to convert
to and from that type to a "fully named" representation of lambda-terms.
(Where the names are just represented by integers).
```
data LC v = Var v | Lam v (LC v) | App (LC v) (LC v)
```
Furthermore, we need to be able to normalize it, using the algorithm specified
above, and limited by some amount of fuel (for testing). We also need a
definition of alpha-equivalence.

### Evaluation with booleans

Optionally, *some* implementations have been extended with two additional
constructs: boolean constants and an if expression. This addition of an
observable base type allow the benchmarking with evaluation instead of
normalization. The lambda calculus terms in the `lambs` subdirectory include
boolean constants, with `eval` marking their final answer.
