# Rebound talks

Source code for talks about the [rebound](../rebound) library. Each talk lives
in its own directory under `src/`.

| Directory | Talk |
|-----------|------|
| [src/Bristol](src/Bristol) | Bristol, July 2026: "What have we learned about Dependently Typed Programming from Haskell?" |
| [src/Hs26](src/Hs26) | Haskell Symposium 2026: "What have we learned about Dependently Typed Programming from Haskell?" |
| [src/Lambdaworld](src/Lambdaworld) | Lambda World 2026: "Adventures in Dependent Haskell: Well-scoped expressions" |

## Building

You need GHC and Cabal installed, for example via
[GHCup](https://www.haskell.org/ghcup/). This package depends on the sibling
`rebound` and `rebound-tutorial` packages, which `cabal.project` already
points to.

```
cd rebound/talks
cabal build
```

To explore the code interactively:

```
cabal repl
```

Then load a talk by its module name, for example `:m + Hs26.Talk1`
or `:l Hs26.Talk1`.
