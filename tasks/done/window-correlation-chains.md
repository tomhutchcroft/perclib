---
id: window-correlation-chains
title: Distinct-cluster functional chains and finite-window root moments
difficulty: medium
kind: interface
labels: []
---

# Distinct-cluster functional chains and finite-window root moments

Being done by the project's own agents; do not start it.

## Goal
Prove and tag wiki assertions **UXBN** (article `countable-reimer`) and **OB0A** (article
`critical-exponents`).

## Target
1. UXBN: for cluster functionals `F, G` with values in `[0, ∞]`, `G` increasing, the chain
   `E[F(K_x)G(K_y)1{x↮y}] ≤ E[F(K_x)1{x↮y}] E G(K_y) ≤ E F(K_x) E G(K_y)`, and with `F` also
   increasing the two-sided product bound and the covariance form, as the article states them.
2. OB0A: for any probability measure on configurations and a nonempty finite window, the
   sampled-root moment identity for real `m ≥ 0` and the two-sided window bound through `E N`.

## Owned files
- New `PercLib/Percolation/Bond/ClusterCorrelation/FunctionalChain.lean`.
- `PercLib/Percolation/Bond/Tightness/Hyperscaling.lean` (append only).
- New `PercLib/Percolation/Bond/Tags/WindowAndCorrelation.lean`.
- Their import lines in `PercLib.lean`.
