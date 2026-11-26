---
id: tree-shape-count
title: The number of leaf-labelled trivalent tree shapes is (2k−5)!!
difficulty: hard
kind: interface
labels: []
---

# The number of leaf-labelled trivalent tree shapes is (2k−5)!!

## Goal
Prove wiki assertion **SO5J** (article `multipoint-trees`) in full and tag it. The library
defines the shapes (`TreeShape k`, `PercLib/Percolation/Bond/Multipoint/Defs.lean`) and counts
them for `k = 2, 3` only.

## Target
For `k ≥ 2`, `TreeShape k` is the set of isomorphism classes (fixing leaf labels) of trees on
`Fin k ⊕ Fin (k − 2)` whose leaves `Sum.inl i` have degree one and whose internal vertices
`Sum.inr j` have degree three. Then
- every such tree has `2k − 3` edges (`card_edgeFinset_trivalentTree`, exists in
  `PercLib/Percolation/Bond/Multipoint/ShapeCount.lean`; check the exact statement), and
- `Nat.card (TreeShape k) = (2k − 5)!!` with `(−1)!! = 1`, i.e. in Lean
  `Nat.card (TreeShape k) = Nat.doubleFactorial (2 * k - 5)` for `k ≥ 2` (note that
  `2 * 2 - 5 = 0` in `ℕ` and `Nat.doubleFactorial 0 = 1`, which matches `(−1)!! = 1`).

Sketch:
```lean
theorem card_treeShape (k : ℕ) (hk : 2 ≤ k) :
    Nat.card (TreeShape k) = Nat.doubleFactorial (2 * k - 5)
```
Proof (article): for `k ≥ 3`, removing the leaf labelled `k` and suppressing its degree-two
neighbour gives a bijection between `TreeShape k` and pairs (shape in `TreeShape (k − 1)`, edge
of that shape), so `|T_k| = (2k − 5) |T_{k−1}|`; start from `card_treeShape_two`. The hard part is
making the bijection precise on the quotient: consider working with a rigid representation
(for example trees whose internal vertices are labelled canonically) and transporting. The base
cases `card_treeShape_two`, `card_treeShape_three` exist.

Tagged statement: the conjunction of the edge count and the shape count for every `k ≥ 2`. The
definitions `TreeShape`, `IsTrivalentTree` must not be changed; if the count is false for them as
defined, stop and report.

## Owned files
- `PercLib/Percolation/Bond/Multipoint/ShapeCount.lean` (append only), or a new
  `PercLib/Percolation/Bond/Multipoint/ShapeRecursion.lean` for the bijection.
- New `PercLib/Percolation/Bond/Tags/TreeShapeCount.lean` (the tagged statement only).
- Import lines in `PercLib.lean`.

## Allowed inputs
`PercLib/Percolation/Bond/Multipoint/*`, mathlib (`SimpleGraph.IsTree`, `Nat.doubleFactorial`,
`Equiv`, `Quotient`); wiki assertion SO5J.

## Stop condition
SO5J tagged and proved, modules built with `--wfail`; or the statement is found false for the
library's definition (report the counterexample).

## Hand-off
Pull request description: the tagged statement, the bijection and its supporting lemmas,
searches, build result.
