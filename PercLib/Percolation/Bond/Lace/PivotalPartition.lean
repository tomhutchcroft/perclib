/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

New proofs for this project; no upstream Lean code is copied.
The cutting-event decomposition follows Heydenreich and van der Hofstad,
Progress in High-Dimensional Percolation and Random Graphs (2017), Section 6.2,
Lemma 6.5. The proof below minimizes distance to the initial endpoint of an
eligible pivotal pair, so it does not assume a finite underlying graph.
-/
module

public import PercLib.Percolation.Bond.Lace.ThroughSet
public import PercLib.Percolation.Bond.Pivotal

/-!
# Cutting a through-set connection at its first eligible pivotal pair

## Main results

The deterministic decomposition uses directed pivotal pairs with their
direction tested after deletion. No equivalence between absence of pivotal
pairs and double connection is assumed.
-/

@[expose] public section
noncomputable section

open Set

namespace PercLib.Percolation.Bond.Lace

variable {V : Type*}

/-- Every connecting subconfiguration reaches the initial endpoint of a
pivotal pair. -/
theorem conn_prefix_of_pivotal {ω η : Config V} {x y u v : V}
    (hηω : η ⊆ ω) (hp : ω \ {s(u, v)} ∉ conn x y)
    (hη : η ∈ conn x y) : η ∈ conn x u := by
  classical
  obtain ⟨p⟩ := hη
  have hpη : η \ {s(u, v)} ∉ conn x y :=
    fun h => hp (conn_mono (sdiff_subset_sdiff_left hηω) h)
  exact ⟨p.takeUntil u (p.fst_mem_support_of_mem_edges (mem_edges_of_pivotal hpη p))⟩

/-- A directed pivotal for the prefix ending at a pivotal pair is also a
directed pivotal for the full connection. -/
theorem orientedPivotal_of_prefix {ω : Config V} {x y u v a b : V}
    (hxy : ω ∈ conn x y) (he : ω ∈ orientedPivotal x y u v)
    (hf : ω ∈ orientedPivotal x u a b) : ω ∈ orientedPivotal x y a b := by
  classical
  have hn : ω \ {s(a, b)} ∉ conn x y := by
    intro h
    exact hf.2.1 (conn_prefix_of_pivotal sdiff_subset he.2.1 h)
  have hi : insert s(a, b) ω ∈ conn x y := conn_mono (subset_insert _ _) hxy
  refine ⟨hi, hn, hf.2.2.1, ?_⟩
  rcases ((pivotal_conn_iff ω x y a b (orientedPivotal_ne hf)).mp ⟨hi, hn⟩).2 with
    h | h
  · exact h.2.symm
  · exact (hf.2.1 (conn_trans h.1 hf.2.2.2)).elim

/-- The initial endpoint of an occupied directed pivotal is strictly closer
to the source than the endpoint of the connection. -/
theorem dist_lt_of_orientedPivotal {ω : Config V} {x y u v : V}
    (hxy : ω ∈ conn x y) (h : ω ∈ orientedPivotal x y u v) :
    (openGraph ω).dist x u < (openGraph ω).dist x y := by
  classical
  have huy : u ≠ y := fun huy => h.2.1 (huy ▸ h.2.2.1)
  obtain ⟨p, hp⟩ := hxy.exists_walk_length_eq_dist
  have hu := p.fst_mem_support_of_mem_edges (mem_edges_of_pivotal h.2.1 p)
  calc
    (openGraph ω).dist x u ≤ (p.takeUntil u hu).length := SimpleGraph.dist_le _
    _ < p.length := SimpleGraph.Walk.length_takeUntil_lt_length hu huy
    _ = (openGraph ω).dist x y := hp

/-- A through-set prefix remains through the set when continued across an
occupied pivotal pair. -/
theorem throughSet_of_prefix_orientedPivotal {A : Set V} {ω : Config V}
    {x y u v : V} (ha : ω ∈ throughSet A x u)
    (hp : ω ∈ orientedPivotal x y u v) (he : s(u, v) ∈ ω) :
    ω ∈ throughSet A x y := by
  classical
  refine ⟨by simpa only [insert_eq_of_mem he] using hp.1, ?_⟩
  rintro ⟨hx, hy, ⟨p⟩⟩
  let p' := p.map (SimpleGraph.Embedding.induce Aᶜ).toHom
  have hu : u ∈ p'.support :=
    p'.fst_mem_support_of_mem_edges (mem_edges_of_pivotal hp.2.1 p')
  rw [SimpleGraph.Walk.support_map, List.mem_map] at hu
  obtain ⟨a, ha', hau⟩ := hu
  have hua : u ∈ Aᶜ := hau ▸ a.property
  apply ha.2
  refine ⟨hx, hua, ?_⟩
  have heq : a = (⟨u, hua⟩ : ↥(Aᶜ : Set V)) := Subtype.ext hau
  subst a
  exact ⟨p.takeUntil _ ha'⟩

theorem cuttingEvent_subset_throughSet (A : Set V) (x y u v : V) :
    cuttingEvent A x y u v ⊆ throughSet A x y :=
  fun _ h => throughSet_of_prefix_orientedPivotal h.1.1.1 h.1.2 h.2

/-- If a through-set connection is not in `E'`, it has a cutting pair.
Minimizing distance to its initial endpoint terminates even on infinite graphs. -/
theorem exists_cuttingEvent_of_not_laceEPrime {A : Set V} {ω : Config V} {x y : V}
    (h : ω ∈ throughSet A x y) (hn : ω ∉ laceEPrime A x y) :
    ∃ u v, ω ∈ cuttingEvent A x y u v := by
  classical
  have hex : ∃ n : ℕ, ∃ u v, (openGraph ω).dist x u = n ∧
      ω ∈ orientedPivotal x y u v ∧ ω ∈ throughSet A x u := by
    have hu : ω ∈ ⋃ u, ⋃ v, orientedPivotal x y u v ∩ throughSet A x u := by
      by_contra hu
      exact hn ⟨h, hu⟩
    obtain ⟨u, v, hp, ha⟩ := by simpa only [mem_iUnion, mem_inter_iff] using hu
    exact ⟨_, u, v, rfl, hp, ha⟩
  obtain ⟨u, v, hdist, hp, ha⟩ := Nat.find_spec hex
  refine ⟨u, v, ⟨⟨ha, ?_⟩, hp⟩, mem_of_pivotal h.1 hp.2.1⟩
  intro hbad
  obtain ⟨a, b, hf, hb⟩ := by simpa only [mem_iUnion, mem_inter_iff] using hbad
  have hsmall := dist_lt_of_orientedPivotal ha.1 hf
  have hmin := Nat.find_min' hex
    (show ∃ u v, (openGraph ω).dist x u = (openGraph ω).dist x a ∧
        ω ∈ orientedPivotal x y u v ∧ ω ∈ throughSet A x u from
      ⟨a, b, rfl, orientedPivotal_of_prefix h.1 hp hf, hb⟩)
  exact (not_lt_of_ge hmin) (hdist ▸ hsmall)

/-- The first-pivotal decomposition of a connection through a set. -/
@[tag "VXRP"]
theorem throughSet_eq_laceEPrime_union_cuttingEvent (A : Set V) (x y : V) :
    throughSet A x y = laceEPrime A x y ∪ ⋃ u, ⋃ v, cuttingEvent A x y u v := by
  classical
  ext ω
  constructor
  · intro h
    by_cases he : ω ∈ laceEPrime A x y
    · exact Or.inl he
    · obtain ⟨u, v, hc⟩ := exists_cuttingEvent_of_not_laceEPrime h he
      exact Or.inr (mem_iUnion.mpr ⟨u, mem_iUnion.mpr ⟨v, hc⟩⟩)
  · rintro (h | h)
    · exact h.1
    · obtain ⟨u, v, hc⟩ := by simpa only [mem_iUnion] using h
      exact cuttingEvent_subset_throughSet A x y u v hc

theorem disjoint_laceEPrime_cuttingEvent (A : Set V) (x y u v : V) :
    Disjoint (laceEPrime A x y) (cuttingEvent A x y u v) := by
  classical
  apply Set.disjoint_left.mpr
  intro ω he hc
  exact he.2 (mem_iUnion.mpr ⟨u, mem_iUnion.mpr ⟨v, hc.1.2, hc.1.1.1⟩⟩)

/-- Deleting a pair outside the component of the source preserves a connection. -/
theorem conn_sdiff_of_not_conn_endpoint {ω : Config V} {x y u v : V}
    (hxy : ω ∈ conn x y) (hxu : ω ∉ conn x u) :
    ω \ {s(u, v)} ∈ conn x y := by
  classical
  obtain ⟨p⟩ := hxy
  have hn : s(u, v) ∉ p.edges := by
    intro he
    exact hxu ⟨p.takeUntil u (p.fst_mem_support_of_mem_edges he)⟩
  refine ⟨p.transfer (openGraph (ω \ {s(u, v)})) fun e he => ?_⟩
  have h1 := p.edges_subset_edgeSet he
  rw [openGraph, SimpleGraph.edgeSet_fromEdgeSet] at h1 ⊢
  exact ⟨⟨h1.1, fun h => hn (mem_singleton_iff.mp h ▸ he)⟩, h1.2⟩

/-- When a directed pivotal also separates the source from a prefix endpoint,
its direction on that prefix agrees with its direction on the full connection. -/
theorem orientedPivotal_prefix_of_not_conn {ω : Config V} {x y u v a : V}
    (hp : ω ∈ orientedPivotal x y u v) (ha : ω ∈ conn x a)
    (hn : ω \ {s(u, v)} ∉ conn x a) : ω ∈ orientedPivotal x a u v := by
  classical
  have hi : insert s(u, v) ω ∈ conn x a := conn_mono (subset_insert _ _) ha
  refine ⟨hi, hn, hp.2.2.1, ?_⟩
  rcases ((pivotal_conn_iff ω x a u v (orientedPivotal_ne hp)).mp ⟨hi, hn⟩).2 with
    h | h
  · exact h.2.symm
  · exact (hp.2.1 (conn_trans h.1 hp.2.2.2)).elim

/-- Distinct pivotal pairs on a realised connection are ordered: one is
pivotal for the prefix ending at the initial endpoint of the other. -/
theorem orientedPivotal_prefix_or_prefix {ω : Config V} {x y u v a b : V}
    (hxy : ω ∈ conn x y) (he : ω ∈ orientedPivotal x y u v)
    (hf : ω ∈ orientedPivotal x y a b) (hne : s(u, v) ≠ s(a, b)) :
    ω ∈ orientedPivotal x u a b ∨ ω ∈ orientedPivotal x a u v := by
  classical
  by_cases hxu : ω \ {s(a, b)} ∈ conn x u
  · right
    apply orientedPivotal_prefix_of_not_conn he (conn_mono sdiff_subset hf.2.2.1)
    intro hxa
    have hnva : ω \ {s(u, v)} ∉ conn v a := by
      intro hva
      exact he.2.1 (conn_trans (conn_trans hxa hva.symm) he.2.2.2)
    have hsub : (ω \ {s(u, v)}) \ {s(a, b)} ⊆ ω \ {s(a, b)} :=
      fun _ h => ⟨h.1.1, h.2⟩
    have hvy : ω \ {s(a, b)} ∈ conn v y :=
      conn_mono hsub
        (conn_sdiff_of_not_conn_endpoint he.2.2.2 hnva :
          (ω \ {s(u, v)}) \ {s(a, b)} ∈ conn v y)
    have huv : ω \ {s(a, b)} ∈ conn u v :=
      mem_conn_of_mem (orientedPivotal_ne he) ⟨mem_of_pivotal hxy he.2.1, hne⟩
    exact hf.2.1 (conn_trans (conn_trans hxu huv) hvy)
  · exact Or.inl (orientedPivotal_prefix_of_not_conn hf
      (conn_mono sdiff_subset he.2.2.1) hxu)

/-- A through-set connection has at most one directed cutting pair. -/
theorem cuttingEvent_unique {A : Set V} {ω : Config V} {x y u v a b : V}
    (he : ω ∈ cuttingEvent A x y u v) (hf : ω ∈ cuttingEvent A x y a b) :
    u = a ∧ v = b := by
  classical
  by_cases hne : s(u, v) = s(a, b)
  · rcases Sym2.eq_iff.mp hne with h | ⟨hua, hvb⟩
    · exact h
    · subst a
      subst b
      exact (not_reverse_orientedPivotal he.1.2 hf.1.2).elim
  · rcases orientedPivotal_prefix_or_prefix (cuttingEvent_subset_conn A x y u v he)
      he.1.2 hf.1.2 hne with h | h
    · exact (he.1.1.2
        (mem_iUnion.mpr ⟨a, mem_iUnion.mpr ⟨b, h, hf.1.1.1⟩⟩)).elim
    · exact (hf.1.1.2
        (mem_iUnion.mpr ⟨u, mem_iUnion.mpr ⟨v, h, he.1.1.1⟩⟩)).elim

theorem pairwiseDisjoint_cuttingEvent (A : Set V) (x y : V) :
    Pairwise fun e f : V × V =>
      Disjoint (cuttingEvent A x y e.1 e.2) (cuttingEvent A x y f.1 f.2) := by
  classical
  intro e f hef
  apply Set.disjoint_left.mpr
  intro ω he hf
  exact hef (Prod.ext (cuttingEvent_unique he hf).1 (cuttingEvent_unique he hf).2)

/-- The first-pivotal decomposition is an exact probability identity. The
summation runs over directed pairs, with coefficient one and no overcounting. -/
@[tag "HU0W"]
theorem law_throughSet_eq_add_tsum_cuttingEvent [Countable V]
    (q : Sym2 V → unitInterval) (A : Set V) (x y : V) :
    law q (throughSet A x y) = law q (laceEPrime A x y) +
      ∑' u, ∑' v, law q (cuttingEvent A x y u v) := by
  classical
  have hU : (⋃ u, ⋃ v, cuttingEvent A x y u v) =
      ⋃ e : V × V, cuttingEvent A x y e.1 e.2 := by
    ext ω
    simp only [mem_iUnion, Prod.exists]
  have hD : Disjoint (laceEPrime A x y)
      (⋃ e : V × V, cuttingEvent A x y e.1 e.2) := by
    apply Set.disjoint_left.mpr
    intro ω he hc
    obtain ⟨e, hc⟩ := mem_iUnion.mp hc
    exact Set.disjoint_left.mp (disjoint_laceEPrime_cuttingEvent A x y e.1 e.2) he hc
  rw [throughSet_eq_laceEPrime_union_cuttingEvent, hU,
    MeasureTheory.measure_union hD (MeasurableSet.iUnion fun e =>
      measurableSet_cuttingEvent A x y e.1 e.2),
    MeasureTheory.measure_iUnion (pairwiseDisjoint_cuttingEvent A x y)
      (fun e => measurableSet_cuttingEvent A x y e.1 e.2)]
  exact congrArg (law q (laceEPrime A x y) + ·)
    (ENNReal.tsum_prod (f := fun u v => law q (cuttingEvent A x y u v)))

end PercLib.Percolation.Bond.Lace
