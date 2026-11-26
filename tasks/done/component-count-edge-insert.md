---
id: component-count-edge-insert
title: Opening one pair changes the component count by exactly the non-connection indicator
difficulty: medium
kind: interface
labels: []
---

# Opening one pair changes the component count by exactly the non-connection indicator

## Goal
Prove wiki assertion **NW8B** (article `cluster-partitions`) in full and tag it. The library proves
that opening a pair decreases the number of components by at most one
(`card_connectedComponent_le_insert_add_one`) and the expected monotonicity in the profile; the
exact formula is missing.

## Target
For finite `V`, let `κ(ω)` be the number of connected components of the open graph.
1. For every configuration `ω` and pair `{a, b}` (loops and already open pairs allowed),
   `κ(ω ∪ {{a,b}}) + 1{a ≁ b in ω} = κ(ω)`.
2. `ω ⊆ ω'` implies `κ(ω') ≤ κ(ω)` (`card_connectedComponent_anti`, exists).
3. For profiles `q ≤ q'` on the same finite vertex set, `E_{q'} κ ≤ E_q κ`
   (`integral_card_connectedComponent_anti`, exists).

Sketch:
```lean
theorem card_connectedComponent_insert_add_indicator [Finite V] (ω : Config V) (a b : V) :
    Nat.card (openGraph (insert s(a, b) ω)).ConnectedComponent +
      (if (openGraph ω).Reachable a b then 0 else 1) =
    Nat.card (openGraph ω).ConnectedComponent
```
Search mathlib for the effect of adding an edge on `ConnectedComponent`
(`SimpleGraph.ConnectedComponent`, `SimpleGraph.sup_edge`, `Subgraph`) before proving the
formula from scratch. Tagged statement: the conjunction of 1-3.

## Owned files
- `PercLib/Percolation/Bond/ClusterCount.lean` (append only).
- New `PercLib/Percolation/Bond/Tags/ComponentCount.lean` (the tagged statement only).
- Its import line in `PercLib.lean`.

If `cluster-count-any-law` is open at the same time, coordinate: both append to
`ClusterCount.lean`.

## Allowed inputs
`PercLib/Percolation/Bond/ClusterCount.lean` and its imports, mathlib; wiki assertion NW8B.

## Stop condition
NW8B tagged and proved, modules built with `--wfail`; or the statement is found false as written
(report it).

## Hand-off
Pull request description: the tagged statement, the area lemmas, searches (mathlib in
particular), build result.
