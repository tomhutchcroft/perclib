/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-16. Wiki tag SO5J (article `multipoint-trees`). No upstream proof is
copied and no definition is added.
-/
module

public import PercLib.Percolation.Bond.Multipoint.Defs
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Tree shapes: finiteness, vertex and edge counts

* `finite_treeShape` (item 1): `𝒯_k` is finite for every `k`.
* `isEmpty_treeShape_of_lt_two`: there is no trivalent tree with fewer than two leaves.
* `card_vertices_trivalentTree`, `card_edgeFinset_trivalentTree` (item 5): a trivalent tree
  with `k ≥ 2` leaves has `k` leaves, `k - 2` internal vertices, `2k - 2` vertices and
  `2k - 3` edges.
-/

@[expose] public section

noncomputable section

open SimpleGraph

namespace PercLib.Percolation.Bond

/-- **Item 1.** There are finitely many tree shapes with `k` leaves. -/
theorem finite_treeShape (k : ℕ) : Finite (TreeShape k) := by
  classical
  unfold TreeShape
  infer_instance

/-- There is no trivalent tree with fewer than two leaves: with no leaf the vertex type is
empty and a tree is nonempty; with one leaf the leaf has no neighbour. -/
theorem not_isTrivalentTree_of_lt_two {k : ℕ} (hk : k < 2)
    (G : SimpleGraph (Fin k ⊕ Fin (k - 2))) : ¬ IsTrivalentTree k G := by
  intro hG
  interval_cases k
  · obtain ⟨v⟩ := hG.isTree.connected.nonempty
    rcases v with i | j
    · exact i.elim0
    · exact j.elim0
  · have h := hG.ncard_leaf 0
    have hempty : G.neighborSet (Sum.inl 0) = ∅ := by
      ext w
      simp only [mem_neighborSet, Set.mem_empty_iff_false, iff_false]
      intro hadj
      rcases w with i | j
      · exact G.irrefl (by rwa [Subsingleton.elim i 0] at hadj)
      · exact j.elim0
    rw [hempty, Set.ncard_empty] at h
    exact zero_ne_one h

/-- There is no tree shape with fewer than two leaves. -/
theorem isEmpty_treeShape_of_lt_two {k : ℕ} (hk : k < 2) : IsEmpty (TreeShape k) :=
  ⟨fun T => Quotient.inductionOn T fun G => not_isTrivalentTree_of_lt_two hk G.1 G.2⟩

/-- **Item 5, vertices.** A trivalent tree with `k ≥ 2` leaves has `k` leaves and `k - 2`
internal vertices, so `2k - 2` vertices. -/
theorem card_vertices_trivalentTree {k : ℕ} (hk : 2 ≤ k) :
    Fintype.card (Fin k ⊕ Fin (k - 2)) = 2 * k - 2 := by
  simp only [Fintype.card_sum, Fintype.card_fin]
  omega

/-- **Item 5, edges.** A trivalent tree with `k ≥ 2` leaves has `2k - 3` edges. -/
theorem card_edgeFinset_trivalentTree {k : ℕ} {G : SimpleGraph (Fin k ⊕ Fin (k - 2))}
    [Fintype G.edgeSet] (hG : IsTrivalentTree k G) : G.edgeFinset.card = 2 * k - 3 := by
  have hk : 2 ≤ k := by
    by_contra h
    exact not_isTrivalentTree_of_lt_two (by omega) G hG
  have h := hG.isTree.card_edgeFinset
  rw [card_vertices_trivalentTree hk] at h
  omega

/-! ### Witnesses -/

/-- With two leaves the single edge `{0, 1}` (the star at leaf `0`) has `2·2 - 3 = 1` edge. -/
example : (starGraph (Sum.inl 0 : Fin 2 ⊕ Fin (2 - 2))).edgeFinset.card = 1 := by
  classical
  exact card_edgeFinset_trivalentTree isTrivalentTree_two

/-- With three leaves the star at the internal vertex has `2·3 - 3 = 3` edges. -/
example : (starGraph (Sum.inr 0 : Fin 3 ⊕ Fin (3 - 2))).edgeFinset.card = 3 := by
  classical
  exact card_edgeFinset_trivalentTree isTrivalentTree_three

/-- `𝒯_4` is finite and `𝒯_1` is empty. -/
example : Finite (TreeShape 4) ∧ IsEmpty (TreeShape 1) :=
  ⟨finite_treeShape 4, isEmpty_treeShape_of_lt_two (by norm_num)⟩

end PercLib.Percolation.Bond
