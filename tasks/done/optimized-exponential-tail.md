---
id: optimized-exponential-tail
title: Optimised exponential cluster tail with the inverse-square-root prefactor
difficulty: medium
kind: interface
labels: []
---

# Optimised exponential cluster tail with the inverse-square-root prefactor

## Goal
Prove wiki assertion **4A0G** (article `finite-graph-criticality`) and tag it. The library has
the weighted exponential moment `E[|K_o| e^{t|K_o|}] ≤ χ_o / √(1 − 2tM²)` for
`0 ≤ t < (2M²)^{−1}` (part of the tagged `XLWI`); optimising Markov's inequality over `t` gives a
tail bound with prefactor `k^{−1/2}`, which the finite-graph largest-component bounds use.

## Target
Independent bond percolation (`law q`) on a nonempty countable `V`, with
`M = sup_v χ(v) < ∞` and `χ_o = χ(o)`. For every real `k ≥ M²`,
`P(|K_o| ≥ k) ≤ (χ_o / M) · √(e/k) · exp(−k/(2M²))`.
If moreover `χ(v) = χ(o)` for all `v` (the transitive case, `M = χ_o`), the prefactor is
`√(e/k)`.

The input is `lintegral_mul_exp_encard_cluster_le` in
`PercLib/Percolation/Bond/UniformVolumeTail.lean` (the cluster volume enters through
`(cluster ω o).encard.toNat`, which agrees with `|K_o|` almost surely:
`law_ofReal_le_encard_cluster_le`, same file), and Markov in the form `measure_le_ofReal_div`
(`PercLib/Probability/ExponentialMoments.lean`). Choose `t* = 1/(2M²) − 1/(2k)`; it is allowed
at `k = M²` (then `t* = 0`). Note `M ≥ 1` (`one_le_chi`). Sketch:
```lean
theorem law_encard_cluster_ge_le_sqrt_exp [Countable V] [Nonempty V]
    (q : Sym2 V → unitInterval) (hM : (⨆ x, chi q x) ≠ ⊤) (o : V) {k : ℝ}
    (hk : (⨆ x, chi q x).toReal ^ 2 ≤ k) :
    law q {ω | ENNReal.ofReal k ≤ ((cluster ω o).encard : ℝ≥0∞)} ≤
      ENNReal.ofReal ((chi q o).toReal / (⨆ x, chi q x).toReal * sqrt (exp 1 / k) *
        exp (-(k / (2 * (⨆ x, chi q x).toReal ^ 2))))
```
Tagged statement: the general bound and the transitive corollary.

## Owned files
- New `PercLib/Percolation/Bond/OptimizedVolumeTail.lean` (area lemmas).
- New `PercLib/Percolation/Bond/Tags/OptimizedVolumeTail.lean` (the tagged statement only).
- Their import lines in `PercLib.lean`.

## Allowed inputs
`PercLib/Percolation/Bond/UniformVolumeTail.lean`, `PercLib/Probability/ExponentialMoments.lean`,
`PercLib/Percolation/Bond/RowSum.lean`, `PercLib/Models/Tags/FiniteRangeExit.lean` (to see how
`XLWI` is stated), mathlib; wiki assertions 4A0G and XLWI.

## Stop condition
4A0G tagged and proved, modules built with `--wfail`; or the statement is found false as written
(report it).

## Hand-off
Pull request description: the tagged statement in full, the area lemmas, what was searched,
build result.
