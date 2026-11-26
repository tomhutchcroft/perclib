---
id: event-entropy-comparison
title: Event-level entropy comparison
difficulty: medium
kind: interface
labels: []
---

# Event-level entropy comparison

Being done by the project's own agents; do not start it.

## Goal
Prove and tag wiki assertion **58HC** (article `entropy-comparison`).

## Target
For countable probability laws `μ, ν` and an event `A`, with `a = μ(A)`, `b = ν(A)`:
`d(a‖b) ≤ D(μ‖ν)` (data processing, with mathlib's `klDiv`) and
`|a − b|² ≤ 2 max{a, b} d(a‖b)`, including the endpoint cases.

## Owned files
- `PercLib/Probability/BernoulliDivergence.lean` (append only).
- New `PercLib/Probability/Tags/EntropyComparison.lean`.
- Its import line in `PercLib.lean`.
