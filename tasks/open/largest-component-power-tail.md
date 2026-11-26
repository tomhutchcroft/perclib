---
id: largest-component-power-tail
title: A uniform power tail at each root bounds the largest component
difficulty: medium
kind: interface
labels: []
---

# A uniform power tail at each root bounds the largest component

## Goal
Prove wiki assertion **JZ89** (article `quotient-cluster-bounds`) and tag it. It turns a
uniform polynomial tail for root clusters into a tail and moment bound for the largest
component of a random graph on `N` vertices, with no independence or transitivity assumption.
Its proof uses no other wiki assertion.

## Target
Let `V` be finite with `N = |V| ≥ 1`, and let `μ` be **any** probability measure on
`Config V` (every random simple graph on `V` is the open graph of such a law). Suppose that for
some `α > 0` and `C ≥ 1`,
`μ(|K(v)| ≥ k) ≤ C k^{−α}` for every vertex `v` and integer `k ≥ 1`.
With `L₁(ω) = max_v |K_ω(v)|`:
1. `μ(L₁ ≥ A N^{1/(1+α)}) ≤ C A^{−(1+α)}` for every real `A ≥ 1`;
2. `E_μ L₁^q ≤ (1 + qC/(1+α−q)) N^{q/(1+α)}` for every `0 < q < 1+α`.

Sketch:
```lean
theorem measure_le_sup_ncard_cluster_le [Fintype V] [Nonempty V] (μ : Measure (Config V))
    [IsProbabilityMeasure μ] {α C : ℝ} (hα : 0 < α) (hC : 1 ≤ C)
    (htail : ∀ v (k : ℕ), 1 ≤ k →
      μ {ω | k ≤ (cluster ω v).ncard} ≤ ENNReal.ofReal (C * (k : ℝ) ^ (-α)))
    {A : ℝ} (hA : 1 ≤ A) :
    μ {ω | A * (Fintype.card V : ℝ) ^ (1 / (1 + α)) ≤
        ((Finset.univ.sup fun v => (cluster ω v).ncard : ℕ) : ℝ)} ≤
      ENNReal.ofReal (C * A ^ (-(1 + α)))
```
and the moment bound with `∫ ω, (L₁ ω : ℝ) ^ q ∂μ` (or `∫⁻`). Intended proof (article): the
count `Z_{≥k}` of vertices in clusters of size at least `k` is at least `k` when `L₁ ≥ k`, so
Markov and the tail bound give `μ(L₁ ≥ k) ≤ C N k^{−(1+α)}`; then the layer-cake formula
(mathlib `lintegral_rpow_eq_lintegral_meas_lt_mul`, `meas_ge_le_lintegral_div`). Integer
rounding at `k = ⌈A N^{1/(1+α)}⌉` needs care; the event is empty when that exceeds `N`.

State the area lemmas for any finite measure if that is free. Tagged statement: the conjunction
of 1 and 2.

## Owned files
- New `PercLib/Percolation/Bond/LargestComponentTail.lean` (area lemmas).
- New `PercLib/Percolation/Bond/Tags/LargestComponentTail.lean` (the tagged statement only).
- Their import lines in `PercLib.lean`.

## Allowed inputs
`PercLib/Percolation/Bond/Basic.lean`, `PercLib/Percolation/Bond/ClusterPartition.lean`,
`PercLib/Probability/LayerCake.lean`, `PercLib/Probability/DiscreteLayerCake.lean`, mathlib;
wiki assertion JZ89.

## Stop condition
JZ89 tagged and proved, modules built with `--wfail`; or the statement is found false or
under-hypothesised as written (report it with the counterexample).

## Hand-off
Pull request description: the tagged statement in full, the area lemmas, what was searched,
build result.
