---
id: uniform-root-volume
title: Cluster volume at a uniform root is the second component moment
difficulty: easy
kind: interface
labels: [good-first-task]
---

# Cluster volume at a uniform root is the second component moment

## Goal
Prove wiki assertion **CY0D** (article `finite-random-graphs`) and tag it. It is the
deterministic step behind the averaged susceptibility of a finite graph: once the configuration
is fixed, a uniformly chosen root lands in a component with probability proportional to its
size, so the mean root-cluster volume is the normalised sum of squared component sizes. Its
dependant `XCGS` (and through it `PXP9`) becomes startable once it is tagged.

## Target
Let `V` be finite and nonempty with `n = |V|`, and fix a configuration `ω` with open components
`C_1, …, C_m`.
1. (new) The proportion of roots `v` whose cluster is the component `C_i` is `|C_i| / n`.
2. (new) `(1/n) Σ_{v ∈ V} |K_ω(v)| = (1/n) Σ_i |C_i|²`.

Item 2 is the real-valued, normalised form of the existing
`tsum_cluster_ncard_eq_tsum_component_sq` (`PercLib/Percolation/Bond/ClusterPartition.lean`),
which is stated with `tsum` over `ℕ`. Sketch of the area lemmas (names and spelling free):
```lean
theorem card_filter_connectedComponentMk_eq [Fintype V] (ω : Config V)
    (C : (openGraph ω).ConnectedComponent) :
    ((Finset.univ.filter fun v => (openGraph ω).connectedComponentMk v = C).card : ℝ) =
      C.supp.ncard

theorem sum_ncard_cluster_div_eq [Fintype V] (ω : Config V) :
    (∑ v, ((cluster ω v).ncard : ℝ)) / Fintype.card V =
      (∑' C : (openGraph ω).ConnectedComponent, (C.supp.ncard : ℝ) ^ 2) / Fintype.card V
```
Tagged statement (Tags file): the conjunction of 1 (as a ratio `/ Fintype.card V`, with
`[Nonempty V]`) and 2, by a term from the area lemmas. The cluster of a root is the support of
its component (`cluster_eq_component_supp`, same file).

## Owned files
- New `PercLib/Percolation/Bond/UniformRootVolume.lean` (area lemmas).
- New `PercLib/Percolation/Bond/Tags/UniformRootVolume.lean` (the tagged statement only).
- Their import lines in `PercLib.lean`.

## Allowed inputs
`PercLib/Percolation/Bond/ClusterPartition.lean`, `PercLib/Percolation/Bond/ClusterCount.lean`,
`PercLib/Percolation/Bond/Basic.lean`, mathlib; wiki assertions CY0D and 6WC8 (the root cluster
as the component containing the root, already tagged in
`PercLib/Percolation/Bond/Tags/CoreConnectivity.lean`).

## Stop condition
CY0D tagged and proved, both modules built with `--wfail`; or the statement is found false or
in need of a hypothesis it does not state (report it, do not change it).

## Hand-off
Pull request description: the tagged statement in full, the area lemmas added, what was
searched in mathlib and `PercLib`, build result.
