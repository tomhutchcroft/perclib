# perclib

Mathematical formalisations in Lean 4 using mathlib.

## Plan

The current plan is in [docs/ROADMAP.md](docs/ROADMAP.md), the decisions behind it in [docs/DECISIONS.md](docs/DECISIONS.md), and the working rules in [docs/COORDINATION.md](docs/COORDINATION.md). The other files in `docs/` are background reference.

## Build

Install [Lean using elan](https://lean-lang.org/install/), then run:

```sh
lake exe cache get
lake build --wfail
```

The project pins Lean **4.35.0**, mathlib **4.35.0**, and all dependency revisions.
Keep `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json` in sync when deliberately updating dependencies.

## Layout

- `PercLib/`: definitions and proofs.
- `PercLib.lean`: imports every project module that the default build should check.
- `PercLib/Basic.lean`: a small initial theorem, `PercLib.two_mul_le_add_sq`, proving `2 * a * b ≤ a ^ 2 + b ^ 2` for real numbers.

Add each new proof module to `PercLib.lean` so `lake build` checks it.

## Automated verification

This public repository has no GitHub Actions workflows yet; continuous integration will be added in a separate pull request. This snapshot was checked before publication: it builds with warnings treated as errors, and an audit of the axioms of declarations in namespace `PercLib` allows only Lean's standard `propext`, `Classical.choice`, and `Quot.sound` axioms. This rejects `sorry`/`admit` placeholders and additional axioms in completed proofs.

The library proves the BK inequality for increasing events on a countable index set, for inhomogeneous Bernoulli parameters and for iterated disjoint occurrence (`countable_bk`, `countable_profile_bk` and `countable_profile_bk_foldl` in [`PercLib/Probability/CountableBK.lean`](PercLib/Probability/CountableBK.lean)). Its main areas are `PercLib/Probability/` (product Bernoulli measures, Harris–FKG, BK, Russo's formula, mass transport, and moment and tail estimates), `PercLib/Percolation/Bond/` (bond percolation with a general edge-parameter profile: clusters, connection kernels, susceptibility, sharpness and spatial moments), `PercLib/Models/` (trees, lattices, hierarchical and long-range models, site percolation and counterexamples), `PercLib/Analysis/` (regular variation, Tauberian theorems and comparison results for ordinary differential equations), `PercLib/Combinatorics/` (splitting and counting for finite trees and forests) and `PercLib/Meta/` (the `tag` attribute that records a declaration's assertion tag). [`PercLib.lean`](PercLib.lean) is the module index, and [`docs/FRONTIER.md`](docs/FRONTIER.md) lists open targets.

## Licence

Lean code and tooling are licensed under the Apache License, Version 2.0 (see [`LICENSE`](LICENSE)). The wiki prose in [`wiki/`](wiki/) is © Tom Hutchcroft and the PercLib contributors, licensed under [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/). See [`NOTICE`](NOTICE) and [`wiki/NOTICE`](wiki/NOTICE).
