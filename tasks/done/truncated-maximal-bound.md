---
id: truncated-maximal-bound
title: Maximal martingale bound with truncated predictable variance
difficulty: medium
kind: interface
labels: []
---

# Maximal martingale bound with truncated predictable variance

Being done by the project's own agents; do not start it.

## Goal
Prove and tag wiki assertion **HXNR** (article `stopped-exploration`), and if time allows the
next assertion **4GBV**.

## Target
For a square-integrable real martingale with `X_0 = 0`, predictable variance `Q`, a stopping
time `T` (possibly infinite) and finite `λ ≥ 0`:
`E[M_T² 1{Q_T ≤ λ}] ≤ 4 E[Q_T ∧ λ]`, where `M_T = sup_{n ≤ T} |X_n|`.

## Owned files
- `PercLib/Probability/TruncatedMaximal.lean` (append only).
- New `PercLib/Probability/Tags/StoppedExploration.lean`.
- Its import line in `PercLib.lean`.

Done: merged in the round-13 batch gated at `e0ae3ec` (HXNR, 4GBV). A second, independent proof of HXNR (`work/frontier-maximal-martingale`, `e9ec3b0`) duplicated this target and was not merged.
