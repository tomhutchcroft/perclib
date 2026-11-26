---
id: finite-edge-change-infinite-component
title: Finitely many edge changes do not affect the existence of an infinite component
difficulty: easy
kind: interface
labels: [good-first-task]
---

# Finitely many edge changes do not affect the existence of an infinite component

## Goal
Prove wiki assertion **D106** (article `infinite-cluster-zero-one`) in full and tag it. The
library has the one-pair, configuration version (`exists_cluster_infinite_insert_iff`,
`PercLib/Percolation/Bond/ZeroOne.lean`); the assertion is for two graphs differing in finitely
many edges, on an arbitrary vertex set.

## Target
Let `G, H` be simple graphs on the same vertex type `V` (not necessarily countable or locally
finite) whose edge sets differ in finitely many edges. Then `G` has an infinite connected
component if and only if `H` does. Sketch:
```lean
theorem exists_infinite_connectedComponent_iff_of_finite_symmDiff {G H : SimpleGraph V}
    (h : (symmDiff G.edgeSet H.edgeSet).Finite) :
    (∃ C : G.ConnectedComponent, C.supp.Infinite) ↔ ∃ C : H.ConnectedComponent, C.supp.Infinite
```
Proof: reduce to adding one edge (deleting is the converse direction of adding), and induct on
the finite set of changed edges (`Set.Finite.induction_on`). Relate to the configuration form
through `openGraph` and `cluster` if that is shorter, and also state the configuration
corollary (configurations differing in finitely many pairs). Search mathlib for edge
insertion and connected components (`SimpleGraph.ConnectedComponent`, `SimpleGraph.sup_edge`,
`SimpleGraph.Reachable.mono`) first. Tagged statement: the graph form.

## Owned files
- `PercLib/Percolation/Bond/ZeroOne.lean` (append only), or, if the graph lemma does not mention
  percolation, a new file under `PercLib/Combinatorics/` with a module docstring.
- New `PercLib/Percolation/Bond/Tags/FiniteEdgeChange.lean` (the tagged statement only).
- Import lines in `PercLib.lean`.

## Allowed inputs
`PercLib/Percolation/Bond/ZeroOne.lean`, `Basic.lean`, mathlib; wiki assertion D106.

## Stop condition
D106 tagged and proved, modules built with `--wfail`.

## Hand-off
Pull request description: the tagged statement, the area lemmas, searches, build result.
