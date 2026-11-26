/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrapper for marked splitting of an infinite locally finite connected graph,
proved from `TreeSplitting.lean`. Mathematical reference: T. Hutchcroft, arXiv:2008.11197v2,
Lemma 2.4. No new definitions.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Combinatorics.TreeSplitting

/-!
# Marked splitting of an infinite connected graph

Restates `PercLib.exists_connected_set_split_of_connected` in the form of the wiki assertion,
for a connected locally finite graph.

## Main results

* `PercLib.exists_connected_set_split_of_connected_of_locallyFinite`: a connected locally finite
  graph with `N ≥ 3^k` marks, `k ≥ 1`, carries at least `3^(k-1) + 1` pairwise disjoint nonempty
  connected edge sets (possibly infinite) whose endpoints cover every vertex, each with at least
  `3^(-k) N` and fewer than `3^(1-k) N` marked endpoints; for a tree they cover every edge.
-/

@[expose] public section
noncomputable section

open SimpleGraph

namespace PercLib

variable {V : Type*}

open Classical in
/-- **Marked splitting with vertex coverage on an infinite locally finite graph.** Let `G` be a
connected locally finite graph, `A` a finite set of `N = |A|` vertices, `k ≥ 1` and `N ≥ 3^k`.
There are finitely many, `m ≥ 3^(k-1) + 1`, pairwise disjoint nonempty sets of edges of `G`
(possibly infinite), each connected on its endpoints, whose endpoint sets `V_i` cover every
vertex and satisfy `3^(-k) N ≤ |A ∩ V_i| < 3^(1-k) N`. If `G` is a tree they cover, hence
partition, every edge.

Local finiteness is not used: the area lemma holds for every connected graph. -/
@[tag "RZSW"]
theorem exists_connected_set_split_of_connected_of_locallyFinite {G : SimpleGraph V}
    [G.LocallyFinite] (hG : G.Connected) (A : Finset V) (k : ℕ) (hk : 1 ≤ k)
    (hN : 3 ^ k ≤ A.card) :
    ∃ C : Finset (Set (Sym2 V)),
      3 ^ (k - 1) + 1 ≤ C.card ∧
      (∀ P ∈ C, P ⊆ G.edgeSet) ∧
      (C : Set (Set (Sym2 V))).PairwiseDisjoint id ∧
      (∀ P ∈ C, P.Nonempty ∧
        (∀ u v, (∃ e ∈ P, u ∈ e) → (∃ e ∈ P, v ∈ e) → (fromEdgeSet P).Reachable u v) ∧
        (A.card : ℝ) / 3 ^ k ≤ ((A.filter fun a => ∃ e ∈ P, a ∈ e).card : ℝ) ∧
        ((A.filter fun a => ∃ e ∈ P, a ∈ e).card : ℝ) < 3 * (A.card : ℝ) / 3 ^ k) ∧
      (∀ v, ∃ P ∈ C, ∃ e ∈ P, v ∈ e) ∧
      (G.IsTree → ∀ e ∈ G.edgeSet, ∃ P ∈ C, e ∈ P) :=
  exists_connected_set_split_of_connected hG A k hk hN

end PercLib
