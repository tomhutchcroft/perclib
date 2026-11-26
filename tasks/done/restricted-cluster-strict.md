---
id: restricted-cluster-strict
title: Restricted clusters lie in full-cluster intersections, not always with equality
difficulty: easy
kind: interface
labels: [good-first-task]
---

# Restricted clusters lie in full-cluster intersections, not always with equality

## Goal
Prove wiki assertion **HQ6X** (article `connectivity`) in full and tag it. The library proves the
inclusion (`conn_of_localConn`, `PercLib/Percolation/Bond/LocalConnectivity.lean`); the assertion
also says that equality can fail, which needs a concrete counterexample.

## Target
For a region `Λ ⊆ V` containing `v`, let `K_v^Λ = {w ∈ Λ : v ↔ w by an open path inside Λ}`.
1. For every configuration, `K_v^Λ ⊆ K_v ∩ Λ`.
2. Equality need not hold: on the path `v − a − w` with `Λ = {v, w}` and both edges open, `w`
   belongs to `K_v ∩ Λ` but not to `K_v^Λ`.

Sketch:
```lean
theorem localCluster_subset_cluster_inter (ω : Config V) (Λ : Set V) (v : Λ) :
    {w : V | ∃ hw : w ∈ Λ, ((openGraph ω).induce Λ).Reachable v ⟨w, hw⟩} ⊆ cluster ω v ∩ Λ
theorem exists_localCluster_ne_cluster_inter :
    ∃ (ω : Config (Fin 3)) (Λ : Set (Fin 3)) (v : Λ),
      {w : Fin 3 | ∃ hw : w ∈ Λ, ((openGraph ω).induce Λ).Reachable v ⟨w, hw⟩} ≠
        cluster ω v ∩ Λ
```
(write the restricted cluster in whatever spelling the library already uses: search
`LocalConnectivity.lean` and the tagged OG96 definition, if any, before choosing). Tagged
statement: the conjunction of 1 (for all `V`, `ω`, `Λ`, `v`) and 2. Use `decide` only where it
does not need `native_decide`.

## Owned files
- `PercLib/Percolation/Bond/LocalConnectivity.lean` (append only).
- New `PercLib/Percolation/Bond/Tags/RestrictedCluster.lean` (the tagged statement only).
- Its import line in `PercLib.lean`.

## Allowed inputs
`PercLib/Percolation/Bond/{Basic,LocalConnectivity}.lean`, mathlib's `SimpleGraph.induce` API;
wiki assertions HQ6X, OG96.

## Stop condition
HQ6X tagged and proved, modules built with `--wfail`.

## Hand-off
Pull request description: the tagged statement, the area lemmas, searches, build result.
