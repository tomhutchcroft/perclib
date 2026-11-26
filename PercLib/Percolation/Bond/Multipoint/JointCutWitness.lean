/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Combinatorial lemma behind the joint-cut estimate of T. Hutchcroft, *Critical long-range
percolation III* (Lemma III.6.16): a connection destroyed only by deleting two vertex sets
together yields two edge-disjoint finite three-point witnesses. The proof is a minimal vertex
separator argument in the finite union of two avoiding walks.
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
public import Mathlib.Combinatorics.SimpleGraph.Walk.Decomp
public import Mathlib.Combinatorics.SimpleGraph.Walk.Maps

/-!
# Joint vertex cuts and disjoint three-point witnesses

Let `G` be a simple graph on an arbitrary vertex type, `A, B` vertex sets, and suppose `y` is
joined to `a` by a walk avoiding `A` and by a walk avoiding `B`, while every walk from `y` to
`a` meets `A ∪ B`. Then there are `b ∈ A`, `c ∈ B` and finite connected subgraphs `H_y ∋ y, b, c`
and `H_a ∋ a, b, c` sharing exactly the vertices `b, c` and no edge.

The proof chooses a separator `T ⊆ A ∪ B` of minimal cardinality inside the finite union of
the two avoiding walks; `T` meets both `A` and `B`, and every vertex of `T` has a neighbour
on each side of the separation.

## Main results

* `SimpleGraph.exists_walks_of_finset_separates`: the statement for a finite separating set,
  in the form of two walks from `b` to `c`.
* `SimpleGraph.exists_subgraphs_of_joint_cut`: two finite connected subgraphs through
  `y, b, c` and `a, b, c` meeting exactly in `{b, c}`, with disjoint edge sets.
-/

@[expose] public section

namespace SimpleGraph

open Walk

variable {V : Type*} {G : SimpleGraph V}

/-- If a walk from `y` meets `T` at most in `t ∈ T`, passes through `t`, and `y ∉ T`, then some
neighbour `u` of `t` is reachable from `y` by a walk avoiding `T`. -/
theorem Walk.exists_adj_walk_of_mem_support [DecidableEq V] {T : Finset V} {t y v : V}
    (ht : t ∈ T) (hy : y ∉ T) (w : G.Walk y v) (hw : ∀ x ∈ w.support, x ∉ T.erase t)
    (htw : t ∈ w.support) :
    ∃ u, G.Adj u t ∧ ∃ q : G.Walk y u, ∀ x ∈ q.support, x ∉ T := by
  set p := w.takeUntil t htw with hp
  have hcount : p.support.count t = 1 := w.count_support_takeUntil_eq_one htw
  have hsub : ∀ x ∈ p.support, x ∈ w.support := fun x hx =>
    w.support_takeUntil_subset_support htw hx
  have hne : t ≠ y := fun h => hy (h ▸ ht)
  have key : ∀ r : G.Walk t y, r = p.reverse →
      ∃ u, G.Adj u t ∧ ∃ q : G.Walk y u, ∀ x ∈ q.support, x ∉ T := by
    intro r hr
    cases r with
    | nil => exact absurd rfl hne
    | @cons _ u _ hadj q =>
      refine ⟨u, hadj.symm, q.reverse, fun x hx hxT => ?_⟩
      rw [support_reverse, List.mem_reverse] at hx
      have hxp : x ∈ p.support := by
        rw [← List.mem_reverse, ← support_reverse, ← hr, support_cons]
        exact List.mem_cons_of_mem _ hx
      have hxt : x ≠ t := by
        rintro rfl
        have h1 : p.reverse.support.count x = 1 := by
          rw [support_reverse, List.count_reverse, hcount]
        rw [← hr, support_cons, List.count_cons_self] at h1
        have : 0 < q.support.count x := List.count_pos_iff.2 hx
        omega
      exact hw x (hsub x hxp) (Finset.mem_erase.2 ⟨hxt, hxT⟩)
  exact key _ rfl

/-- A walk from `y` avoiding `T` reaches every vertex of its support by a walk avoiding `T`. -/
theorem Walk.exists_walk_avoid_of_mem_support [DecidableEq V] {T : Finset V} {y u x : V}
    (q : G.Walk y u) (hq : ∀ z ∈ q.support, z ∉ T) (hx : x ∈ q.support) :
    ∃ r : G.Walk y x, ∀ z ∈ r.support, z ∉ T :=
  ⟨q.takeUntil x hx, fun z hz => hq z (q.support_takeUntil_subset_support hx hz)⟩

/-- **Joint cut, finite separator form.** If `y` is joined to `a` by a walk avoiding `A` and by
one avoiding `B`, and a finite set `T₀ ⊆ A ∪ B` meets every walk from `y` to `a`, then there are
`b ∈ A`, `c ∈ B` and walks `W_y, W_a` from `b` to `c` through `y` and `a` respectively whose
supports meet only in `b, c` and which share no edge. -/
theorem exists_walks_of_finset_separates {A B : Set V} {y a : V} (T₀ : Finset V)
    (hT₀ : ∀ x ∈ T₀, x ∈ A ∪ B) (hsep : ∀ p : G.Walk y a, ∃ x ∈ p.support, x ∈ T₀)
    (hA : ∃ p : G.Walk y a, ∀ x ∈ p.support, x ∉ A)
    (hB : ∃ p : G.Walk y a, ∀ x ∈ p.support, x ∉ B) :
    ∃ b ∈ A, ∃ c ∈ B, ∃ Wy Wa : G.Walk b c, y ∈ Wy.support ∧ a ∈ Wa.support ∧
      (∀ x ∈ Wy.support, x ∈ Wa.support → x = b ∨ x = c) ∧ ∀ e ∈ Wy.edges, e ∉ Wa.edges := by
  classical
  obtain ⟨pA, hpA⟩ := hA
  obtain ⟨pB, hpB⟩ := hB
  -- a separator of minimal cardinality
  set S := T₀.powerset.filter (fun T => ∀ p : G.Walk y a, ∃ x ∈ p.support, x ∈ T) with hS
  have hT₀S : T₀ ∈ S := Finset.mem_filter.2 ⟨Finset.mem_powerset_self _, hsep⟩
  obtain ⟨T, hTS, hTmin⟩ := S.exists_min_image Finset.card ⟨T₀, hT₀S⟩
  obtain ⟨hTT₀, hTsep⟩ := Finset.mem_filter.1 hTS
  rw [Finset.mem_powerset] at hTT₀
  have hTAB : ∀ x ∈ T, x ∈ A ∪ B := fun x hx => hT₀ x (hTT₀ hx)
  have hyA : y ∉ A := hpA y pA.start_mem_support
  have hyB : y ∉ B := hpB y pB.start_mem_support
  have haA : a ∉ A := hpA a pA.end_mem_support
  have haB : a ∉ B := hpB a pB.end_mem_support
  have hyT : y ∉ T := fun h => (hTAB y h).elim hyA hyB
  have haT : a ∉ T := fun h => (hTAB a h).elim haA haB
  -- `T` meets both `A` and `B`
  obtain ⟨b, hbT, hbA⟩ : ∃ b ∈ T, b ∈ A := by
    obtain ⟨x, hx, hxT⟩ := hTsep pB
    exact ⟨x, hxT, (hTAB x hxT).resolve_right (hpB x hx)⟩
  obtain ⟨c, hcT, hcB⟩ : ∃ c ∈ T, c ∈ B := by
    obtain ⟨x, hx, hxT⟩ := hTsep pA
    exact ⟨x, hxT, (hTAB x hxT).resolve_left (hpA x hx)⟩
  -- minimality: deleting `T \ {t}` leaves a connection, which passes through `t`
  have hmin : ∀ t ∈ T, ∃ w : G.Walk y a, (∀ x ∈ w.support, x ∉ T.erase t) ∧ t ∈ w.support := by
    intro t ht
    have hnot : T.erase t ∉ S := by
      intro hmem
      have := hTmin _ hmem
      have := Finset.card_erase_lt_of_mem ht
      omega
    have hnsep : ¬ ∀ p : G.Walk y a, ∃ x ∈ p.support, x ∈ T.erase t := fun h =>
      hnot (Finset.mem_filter.2 ⟨Finset.mem_powerset.2 ((T.erase_subset t).trans hTT₀), h⟩)
    push Not at hnsep
    obtain ⟨w, hw⟩ := hnsep
    refine ⟨w, hw, ?_⟩
    by_contra htw
    obtain ⟨x, hx, hxT⟩ := hTsep w
    exact hw x hx (Finset.mem_erase.2 ⟨fun h => htw (h ▸ hx), hxT⟩)
  -- neighbours of `t` on the `y` side and on the `a` side
  have hside : ∀ t ∈ T, (∃ u, G.Adj u t ∧ ∃ q : G.Walk y u, ∀ x ∈ q.support, x ∉ T) ∧
      ∃ u, G.Adj u t ∧ ∃ q : G.Walk a u, ∀ x ∈ q.support, x ∉ T := by
    intro t ht
    obtain ⟨w, hw, htw⟩ := hmin t ht
    refine ⟨w.exists_adj_walk_of_mem_support ht hyT hw htw,
      w.reverse.exists_adj_walk_of_mem_support ht haT ?_ ?_⟩
    · simpa [support_reverse] using hw
    · simpa [support_reverse] using htw
  obtain ⟨⟨ub, hub, qb, hqb⟩, ⟨vb, hvb, rb, hrb⟩⟩ := hside b hbT
  obtain ⟨⟨uc, huc, qc, hqc⟩, ⟨vc, hvc, rc, hrc⟩⟩ := hside c hcT
  -- the two sides cannot share a vertex outside `T`
  have hdisj : ∀ x, (∃ r : G.Walk y x, ∀ z ∈ r.support, z ∉ T) →
      (∃ r : G.Walk a x, ∀ z ∈ r.support, z ∉ T) → False := by
    rintro x ⟨r, hr⟩ ⟨r', hr'⟩
    obtain ⟨z, hz, hzT⟩ := hTsep (r.append r'.reverse)
    rw [mem_support_append_iff, support_reverse, List.mem_reverse] at hz
    exact hz.elim (fun h => hr z h hzT) (fun h => hr' z h hzT)
  let Wy : G.Walk b c := cons hub.symm (qb.reverse.append (qc.append (cons huc nil)))
  let Wa : G.Walk b c := cons hvb.symm (rb.reverse.append (rc.append (cons hvc nil)))
  -- vertices of the two walks
  have hWy : ∀ x ∈ Wy.support, x = b ∨ x = c ∨ ∃ r : G.Walk y x, ∀ z ∈ r.support, z ∉ T := by
    intro x hx
    simp only [Wy, support_cons, List.mem_cons, mem_support_append_iff, support_reverse,
      List.mem_reverse, support_nil, List.not_mem_nil, or_false] at hx
    rcases hx with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (qb.exists_walk_avoid_of_mem_support hqb h))
    · exact Or.inr (Or.inr (qc.exists_walk_avoid_of_mem_support hqc h))
    · rcases h with rfl | h
      · exact Or.inr (Or.inr (qc.exists_walk_avoid_of_mem_support hqc qc.end_mem_support))
      · exact Or.inr (Or.inl h)
  have hWa : ∀ x ∈ Wa.support, x = b ∨ x = c ∨ ∃ r : G.Walk a x, ∀ z ∈ r.support, z ∉ T := by
    intro x hx
    simp only [Wa, support_cons, List.mem_cons, mem_support_append_iff, support_reverse,
      List.mem_reverse, support_nil, List.not_mem_nil, or_false] at hx
    rcases hx with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (rb.exists_walk_avoid_of_mem_support hrb h))
    · exact Or.inr (Or.inr (rc.exists_walk_avoid_of_mem_support hrc h))
    · rcases h with rfl | h
      · exact Or.inr (Or.inr (rc.exists_walk_avoid_of_mem_support hrc rc.end_mem_support))
      · exact Or.inr (Or.inl h)
  have hinter : ∀ x ∈ Wy.support, x ∈ Wa.support → x = b ∨ x = c := by
    intro x hx hx'
    rcases hWy x hx with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    rcases hWa x hx' with h' | h' | h'
    · exact Or.inl h'
    · exact Or.inr h'
    exact (hdisj x h h').elim
  -- every edge of `W_y` has an endpoint outside `T`
  have hedge : ∀ e ∈ Wy.edges, ∃ x ∈ e, x ∉ T := by
    intro e he
    simp only [Wy, edges_cons, List.mem_cons, edges_append, List.mem_append, edges_reverse,
      List.mem_reverse, edges_nil, List.not_mem_nil, or_false] at he
    rcases he with rfl | he | he | rfl
    · exact ⟨ub, Sym2.mem_mk_right _ _, hqb ub qb.end_mem_support⟩
    · induction e using Sym2.ind with
      | _ x z => exact ⟨x, Sym2.mem_mk_left _ _, hqb x (qb.fst_mem_support_of_mem_edges he)⟩
    · induction e using Sym2.ind with
      | _ x z => exact ⟨x, Sym2.mem_mk_left _ _, hqc x (qc.fst_mem_support_of_mem_edges he)⟩
    · exact ⟨uc, Sym2.mem_mk_left _ _, hqc uc qc.end_mem_support⟩
  refine ⟨b, hbA, c, hcB, Wy, Wa, ?_, ?_, hinter, ?_⟩
  · simp [Wy, mem_support_append_iff, support_reverse]
  · simp [Wa, mem_support_append_iff, support_reverse]
  · intro e he he'
    obtain ⟨x, hxe, hxT⟩ := hedge e he
    induction e using Sym2.ind with
    | _ p q =>
      have hx : x ∈ Wy.support ∧ x ∈ Wa.support := by
        rcases Sym2.mem_iff.1 hxe with rfl | rfl
        · exact ⟨Wy.fst_mem_support_of_mem_edges he, Wa.fst_mem_support_of_mem_edges he'⟩
        · exact ⟨Wy.snd_mem_support_of_mem_edges he, Wa.snd_mem_support_of_mem_edges he'⟩
      rcases hinter x hx.1 hx.2 with rfl | rfl
      · exact hxT hbT
      · exact hxT hcT

/-- **A joint vertex cut supplies two disjoint three-point witnesses.** If `y` is joined to `a`
by a walk avoiding `A` and by a walk avoiding `B`, but every walk from `y` to `a` meets `A ∪ B`,
then there are `b ∈ A`, `c ∈ B` and finite connected subgraphs `H_y ⊇ {y, b, c}` and
`H_a ⊇ {a, b, c}` of `G` with `V(H_y) ∩ V(H_a) = {b, c}` and no common edge. -/
theorem exists_subgraphs_of_joint_cut {A B : Set V} {y a : V}
    (hA : ∃ p : G.Walk y a, ∀ x ∈ p.support, x ∉ A)
    (hB : ∃ p : G.Walk y a, ∀ x ∈ p.support, x ∉ B)
    (hAB : ∀ p : G.Walk y a, ∃ x ∈ p.support, x ∈ A ∪ B) :
    ∃ b ∈ A, ∃ c ∈ B, ∃ Hy Ha : G.Subgraph,
      Hy.Connected ∧ Ha.Connected ∧ Hy.verts.Finite ∧ Ha.verts.Finite ∧
      {y, b, c} ⊆ Hy.verts ∧ {a, b, c} ⊆ Ha.verts ∧
      Hy.verts ∩ Ha.verts = {b, c} ∧ Disjoint Hy.edgeSet Ha.edgeSet := by
  classical
  obtain ⟨pA, hpA⟩ := hA
  obtain ⟨pB, hpB⟩ := hB
  -- the finite union graph of the two avoiding walks
  let G₀ : SimpleGraph V := pA.toSubgraph.spanningCoe ⊔ pB.toSubgraph.spanningCoe
  have hle : G₀ ≤ G := sup_le pA.toSubgraph.spanningCoe_le pB.toSubgraph.spanningCoe_le
  have hsupp : ∀ {u v : V} (p : G₀.Walk u v), v = a → ∀ x ∈ p.support,
      x = a ∨ x ∈ pA.support ∨ x ∈ pB.support := by
    intro u v p
    induction p with
    | nil =>
      intro hv x hx
      simp only [support_nil, List.mem_singleton] at hx
      exact Or.inl (hx.trans hv)
    | cons h q ih =>
      intro hv x hx
      rw [support_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · rcases h with h | h
        · exact Or.inr (Or.inl (by simpa using (Subgraph.Adj.fst_mem h)))
        · exact Or.inr (Or.inr (by simpa using (Subgraph.Adj.fst_mem h)))
      · exact ih hv x hx
  let T₀ : Finset V := (pA.support ++ pB.support).toFinset.filter (· ∈ A ∪ B)
  have hT₀ : ∀ x ∈ T₀, x ∈ A ∪ B := fun x hx => (Finset.mem_filter.1 hx).2
  have hsep : ∀ p : G₀.Walk y a, ∃ x ∈ p.support, x ∈ T₀ := by
    intro p
    obtain ⟨x, hx, hxAB⟩ := hAB (p.mapLe hle)
    rw [support_mapLe_eq_support] at hx
    refine ⟨x, hx, Finset.mem_filter.2 ⟨?_, hxAB⟩⟩
    rw [List.mem_toFinset, List.mem_append]
    rcases hsupp p rfl x hx with rfl | h | h
    · exact Or.inl pA.end_mem_support
    · exact Or.inl h
    · exact Or.inr h
  have hA₀ : ∃ p : G₀.Walk y a, ∀ x ∈ p.support, x ∉ A :=
    ⟨pA.transfer G₀ (fun e he => by
      rw [edgeSet_sup]; exact Or.inl (by simpa using he)), by
      simpa [support_transfer] using hpA⟩
  have hB₀ : ∃ p : G₀.Walk y a, ∀ x ∈ p.support, x ∉ B :=
    ⟨pB.transfer G₀ (fun e he => by
      rw [edgeSet_sup]; exact Or.inr (by simpa using he)), by
      simpa [support_transfer] using hpB⟩
  obtain ⟨b, hbA, c, hcB, Wy, Wa, hy, ha, hinter, hedge⟩ :=
    exists_walks_of_finset_separates T₀ hT₀ hsep hA₀ hB₀
  refine ⟨b, hbA, c, hcB, (Wy.mapLe hle).toSubgraph, (Wa.mapLe hle).toSubgraph,
    Walk.toSubgraph_connected _, Walk.toSubgraph_connected _, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp
  · simp
  · intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    simp only [verts_toSubgraph, support_mapLe_eq_support, Set.mem_ofPred_eq]
    rcases hx with rfl | rfl | rfl
    · exact hy
    · exact Wy.start_mem_support
    · exact Wy.end_mem_support
  · intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    simp only [verts_toSubgraph, support_mapLe_eq_support, Set.mem_ofPred_eq]
    rcases hx with rfl | rfl | rfl
    · exact ha
    · exact Wa.start_mem_support
    · exact Wa.end_mem_support
  · ext x
    simp only [verts_toSubgraph, support_mapLe_eq_support, Set.mem_inter_iff, Set.mem_ofPred_eq,
      Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨h, h'⟩; exact hinter x h h'
    · rintro (rfl | rfl)
      · exact ⟨Wy.start_mem_support, Wa.start_mem_support⟩
      · exact ⟨Wy.end_mem_support, Wa.end_mem_support⟩
  · rw [Set.disjoint_left]
    intro e he he'
    simp only [edgeSet_toSubgraph, Walk.mem_edgeSet, edges_mapLe_eq_edges] at he he'
    exact hedge e he he'

end SimpleGraph
