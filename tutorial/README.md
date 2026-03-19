# Implement your POPL paper (in Haskell) — Tutorial Code

This repository contains the companion code for the four-lecture tutorial on
representing and manipulating lambda-calculus terms using well-scoped de Bruijn
indices in Haskell.

The goal of these lectures is to provide familiarity with dependently-typed programming 
and well-scoped de Bruijn indices. While all of the examples are presented using the 
Haskell language, and take advantage of many Haskell features, the *ideas* presented in these
lectures should translate to programming in any typed-functional programming language, 
such as OCaml, Rocq, Lean or Agda. 

## Lectures

| Lecture | Topic |
|---------|-------|
| [Lecture 1](lectures/Lecture1.md) | Working with well-scoped De Bruijn terms |
| [Lecture 2](lectures/Lecture2.md) | Where do well-scoped terms come from? |
| [Lecture 3](lectures/Lecture3.md) | CPS: A scope-preserving translation |
| [Lecture 4](lectures/Lecture4.md) | Efficient implementation using delayed and defunctionalized substitutions |

The tutorial website is at: https://sweirich.github.io/rebound/

## Getting started

You need GHC and Cabal installed. The easiest way is via
[GHCup](https://www.haskell.org/ghcup/).

```
git clone https://github.com/sweirich/rebound
cd rebound/tutorial
cabal build
cabal test
```

To explore the code interactively:

```
cabal repl
```

## Source layout

```
src/
  Tutorial/
    Lib.hs                  -- shared utilities
    Named/
      Syntax.hs             -- named (surface) syntax
      PP.hs                 -- pretty-printer
      Parser.hs             -- parser
    Scoped/
      Scratch.hs            -- hand-written de Bruijn infrastructure (Lecture 1)
      Syntax.hs             -- syntax using the rebound library
      Eval.hs               -- big-step evaluator (Lecture 1)
      Gen.hs                -- QuickCheck term generator (Lecture 2)
      ScopeCheck.hs         -- named ↔ scoped conversion (Lecture 2)
      TestEval.hs           -- QuickCheck properties for the evaluator
      CPS.hs                -- CPS translation (Lecture 3)
test/
  TutorialTests.hs          -- tasty test suite
lectures/
  Lecture1.md … Lecture4.md -- lecture notes
```

## Dependencies

This project depends on the
[rebound](https://hackage.haskell.org/package/rebound) library, available on
Hackage.
