/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, using mathlib's connected components, `SimpleGraph.fromEdgeSet` and finite-set
induction. Mathematical reference: the finite-modification step of the zero-one law for the
existence of an infinite cluster (e.g. T. Hutchcroft's lecture notes on percolation). No source
text or code is copied.
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Order.SymmDiff

/-! # Infinite components under finite edge changes

Adding one edge to a simple graph joins at most two connected components, so it creates an
infinite component only if one already exists; adding edges never destroys one. Iterating over
a finite set of added edges and writing `G ⊔ H` in two ways shows that two simple graphs on the
same vertex type whose edge sets differ in finitely many edges either both have an infinite
connected component or both have none. No countability or local finiteness is assumed.

## Main results

* `SimpleGraph.reachable_sup_fromEdgeSet_singleton`: a vertex reachable from `a` after one
  edge `s(u, v)` is added was already reachable from `a`, `u` or `v`.
* `SimpleGraph.exists_supp_infinite_sup_fromEdgeSet_iff`: adding finitely many edges does not
  change whether an infinite component exists.
* `SimpleGraph.exists_supp_infinite_iff_of_finite_symmDiff`: two graphs whose edge sets have
  finite symmetric difference either both have an infinite component or both have none.

The statement is about the existence of an infinite component somewhere: deleting one edge
can separate a given vertex from the only infinite component (see the example at the end).
-/

@[expose] public section

open Set
open scoped symmDiff

namespace SimpleGraph

variable {V : Type*}

/-- A graph has an infinite connected component exactly when some vertex reaches infinitely
many vertices. -/
theorem exists_supp_infinite_iff_exists_reachable (G : SimpleGraph V) :
    (∃ c : G.ConnectedComponent, c.supp.Infinite) ↔ ∃ v, {w | G.Reachable v w}.Infinite := by
  have h (v : V) : (G.connectedComponentMk v).supp = {w | G.Reachable v w} := by
    ext w
    rw [ConnectedComponent.mem_supp_iff, ConnectedComponent.eq, mem_ofPred_eq]
    exact ⟨Reachable.symm, Reachable.symm⟩
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨v, rfl⟩ := c.exists_rep
    exact ⟨v, h v ▸ hc⟩
  · rintro ⟨v, hv⟩
    exact ⟨G.connectedComponentMk v, (h v).symm ▸ hv⟩

/-- **Adding one edge joins at most two components.** A vertex reachable from `a` after the
edge `s(u, v)` is added was already reachable from `a`, from `u` or from `v`. -/
theorem reachable_sup_fromEdgeSet_singleton (G : SimpleGraph V) {a w : V} (u v : V)
    (h : (G ⊔ fromEdgeSet {s(u, v)}).Reachable a w) :
    G.Reachable a w ∨ G.Reachable u w ∨ G.Reachable v w := by
  rw [reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact Or.inl Reachable.rfl
  | @tail b c _ hadj ih =>
    rw [sup_adj, fromEdgeSet_adj, mem_singleton_iff] at hadj
    rcases hadj with hadj | ⟨he, -⟩
    · rcases ih with h | h | h
      · exact Or.inl (h.trans hadj.reachable)
      · exact Or.inr (Or.inl (h.trans hadj.reachable))
      · exact Or.inr (Or.inr (h.trans hadj.reachable))
    · rcases Sym2.eq_iff.1 he with ⟨-, rfl⟩ | ⟨-, rfl⟩
      · exact Or.inr (Or.inr Reachable.rfl)
      · exact Or.inr (Or.inl Reachable.rfl)

/-- Adding one edge does not change whether an infinite component exists. -/
theorem exists_supp_infinite_sup_fromEdgeSet_singleton_iff (G : SimpleGraph V) (e : Sym2 V) :
    (∃ c : (G ⊔ fromEdgeSet {e}).ConnectedComponent, c.supp.Infinite) ↔
      ∃ c : G.ConnectedComponent, c.supp.Infinite := by
  rw [exists_supp_infinite_iff_exists_reachable, exists_supp_infinite_iff_exists_reachable]
  constructor
  · rintro ⟨a, ha⟩
    induction e using Sym2.ind with
    | _ u v =>
      have hsub : {w | (G ⊔ fromEdgeSet {s(u, v)}).Reachable a w} ⊆
          {w | G.Reachable a w} ∪ {w | G.Reachable u w} ∪ {w | G.Reachable v w} :=
        fun w hw => by
          rcases reachable_sup_fromEdgeSet_singleton G u v hw with h | h | h
          · exact Or.inl (Or.inl h)
          · exact Or.inl (Or.inr h)
          · exact Or.inr h
      rcases infinite_union.1 (ha.mono hsub) with h | h
      · rcases infinite_union.1 h with h | h
        · exact ⟨a, h⟩
        · exact ⟨u, h⟩
      · exact ⟨v, h⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, ha.mono fun w hw => hw.mono le_sup_left⟩

/-- **Adding finitely many edges** does not change whether an infinite component exists. -/
theorem exists_supp_infinite_sup_fromEdgeSet_iff (G : SimpleGraph V) {s : Set (Sym2 V)}
    (hs : s.Finite) :
    (∃ c : (G ⊔ fromEdgeSet s).ConnectedComponent, c.supp.Infinite) ↔
      ∃ c : G.ConnectedComponent, c.supp.Infinite := by
  induction s, hs using Set.Finite.induction_on with
  | empty => rw [fromEdgeSet_empty, sup_bot_eq]
  | @insert e s _ _ ih =>
    rw [← ih, ← exists_supp_infinite_sup_fromEdgeSet_singleton_iff (G ⊔ fromEdgeSet s) e,
      sup_assoc, ← fromEdgeSet_union, union_singleton]

/-- Adding to `G` the edges of `H` that `G` lacks gives `G ⊔ H`. -/
theorem sup_fromEdgeSet_edgeSet_diff (G H : SimpleGraph V) :
    G ⊔ fromEdgeSet (H.edgeSet \ G.edgeSet) = G ⊔ H := by
  ext a b
  simp only [sup_adj, fromEdgeSet_adj, mem_sdiff, mem_edgeSet]
  constructor
  · rintro (h | ⟨⟨h, -⟩, -⟩)
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl h
    · by_cases hG : G.Adj a b
      · exact Or.inl hG
      · exact Or.inr ⟨⟨h, hG⟩, h.ne⟩

/-- **Finite edge changes.** If the edge sets of two simple graphs on the same vertex type
differ in finitely many edges, one has an infinite connected component if and only if the
other does. Neither countability nor local finiteness is assumed. -/
theorem exists_supp_infinite_iff_of_finite_symmDiff {G H : SimpleGraph V}
    (h : (G.edgeSet ∆ H.edgeSet).Finite) :
    (∃ c : G.ConnectedComponent, c.supp.Infinite) ↔
      ∃ c : H.ConnectedComponent, c.supp.Infinite := by
  have hHG : (H.edgeSet \ G.edgeSet).Finite :=
    h.subset fun e he => by rw [symmDiff_def]; exact Or.inr he
  have hGH : (G.edgeSet \ H.edgeSet).Finite :=
    h.subset fun e he => by rw [symmDiff_def]; exact Or.inl he
  rw [← exists_supp_infinite_sup_fromEdgeSet_iff G hHG,
    ← exists_supp_infinite_sup_fromEdgeSet_iff H hGH, sup_fromEdgeSet_edgeSet_diff,
    sup_fromEdgeSet_edgeSet_diff, sup_comm]

/-! ### Non-vacuity -/

/-- On `ℕ`, deleting the edge `s(0, 1)` from the complete graph leaves an infinite
component. -/
example : ∃ c : ((⊤ : SimpleGraph ℕ) \ fromEdgeSet {s(0, 1)}).ConnectedComponent,
    c.supp.Infinite := by
  refine (exists_supp_infinite_iff_of_finite_symmDiff (G := ⊤) ?_).1
    ⟨(⊤ : SimpleGraph ℕ).connectedComponentMk 0,
      (ConnectedComponent.top_supp_eq_univ _).symm ▸ infinite_univ⟩
  refine (finite_singleton s(0, 1)).subset fun e he => ?_
  rw [edgeSet_sdiff, edgeSet_fromEdgeSet, symmDiff_def] at he
  rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · simp only [mem_sdiff, not_and, not_not] at h2
    by_contra hne
    exact h2 h1 fun h => absurd h hne
  · exact absurd h1.1 h2

end SimpleGraph
