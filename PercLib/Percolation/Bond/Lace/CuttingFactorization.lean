/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

New proofs for this project; no upstream Lean code is copied.
The cutting-bond factorization follows Heydenreich and van der Hofstad,
Progress in High-Dimensional Percolation and Random Graphs (2017), Section 6.2,
Lemma 6.4. Its deterministic ingredient is deletion of a separating bridge.
-/
module

public import PercLib.Percolation.Bond.Lace.PivotalPartition
public import PercLib.Percolation.Bond.Lace.ClusterLocalization
public import PercLib.Percolation.Bond.ClusterLaw
public import PercLib.Percolation.Bond.Susceptibility
public import PercLib.Probability.Coordinate

/-!
# The cutting-bond factorization

## Main results

Connections within one component of the deleted graph cannot use the separating
edge on a simple path. This remains true after further edges are removed and
when the path is restricted to avoid a vertex set.
-/

@[expose] public section
noncomputable section

open Set MeasureTheory PercLib.Probability
open scoped ENNReal

namespace PercLib.Percolation.Bond.Lace

variable {V : Type*}

theorem openGraph_sdiff_eq_deleteEdges (ω : Config V) (E : Set (Sym2 V)) :
    openGraph (ω \ E) = (openGraph ω).deleteEdges E := by
  classical
  ext a b
  simp only [openGraph_adj_iff, SimpleGraph.deleteEdges_adj, mem_sdiff]
  tauto

/-- A trail within a component of a deleted graph does not traverse the
separating pair, even when drawn in a smaller configuration. -/
theorem not_mem_edges_of_same_deleted_cluster {ω η : Config V} {o a b u v : V}
    (hη : η ⊆ ω) (ha : ω \ {s(u, v)} ∈ conn o a)
    (hb : ω \ {s(u, v)} ∈ conn o b) (hv : ω \ {s(u, v)} ∉ conn o v)
    {p : (openGraph η).Walk a b} (hp : p.IsTrail) : s(u, v) ∉ p.edges := by
  classical
  apply hp.notMem_edges_of_not_reachable
  · rw [← openGraph_sdiff_eq_deleteEdges]
    intro h
    exact hv (conn_trans ha (conn_mono (sdiff_subset_sdiff_left hη) h))
  · rw [← openGraph_sdiff_eq_deleteEdges]
    intro h
    exact hv (conn_trans hb (conn_mono (sdiff_subset_sdiff_left hη) h))

/-- Deleting a separating pair preserves connections inside its source
component, including connections in arbitrary subconfigurations. -/
theorem conn_sdiff_iff_of_same_deleted_cluster {ω η : Config V} {o a b u v : V}
    (hη : η ⊆ ω) (ha : ω \ {s(u, v)} ∈ conn o a)
    (hb : ω \ {s(u, v)} ∈ conn o b) (hv : ω \ {s(u, v)} ∉ conn o v) :
    η ∈ conn a b ↔ η \ {s(u, v)} ∈ conn a b := by
  classical
  constructor
  · intro h
    obtain ⟨p, hp, -⟩ := h.exists_path_of_dist
    have hn := not_mem_edges_of_same_deleted_cluster hη ha hb hv hp.isTrail
    refine ⟨p.transfer (openGraph (η \ {s(u, v)})) fun e he => ?_⟩
    have h1 := p.edges_subset_edgeSet he
    rw [openGraph, SimpleGraph.edgeSet_fromEdgeSet] at h1 ⊢
    exact ⟨⟨h1.1, fun heq => hn (mem_singleton_iff.mp heq ▸ he)⟩, h1.2⟩
  · exact conn_mono sdiff_subset

/-- The same bridge deletion preserves induced-domain connections. -/
theorem localConn_sdiff_iff_of_same_deleted_cluster (S : Set V)
    {ω η : Config V} {o u v : V} (a b : S)
    (hη : η ⊆ ω) (ha : ω \ {s(u, v)} ∈ conn o a)
    (hb : ω \ {s(u, v)} ∈ conn o b) (hv : ω \ {s(u, v)} ∉ conn o v) :
    ((openGraph η).induce S).Reachable a b ↔
      ((openGraph (η \ {s(u, v)})).induce S).Reachable a b := by
  classical
  constructor
  · intro h
    obtain ⟨p, hp, -⟩ := h.exists_path_of_dist
    let w := p.map (SimpleGraph.Embedding.induce S).toHom
    have hw : w.IsPath := hp.map Subtype.val_injective
    have hn := not_mem_edges_of_same_deleted_cluster hη ha hb hv hw.isTrail
    let w' := w.transfer (openGraph (η \ {s(u, v)})) fun e he => by
      have h1 := w.edges_subset_edgeSet he
      rw [openGraph, SimpleGraph.edgeSet_fromEdgeSet] at h1 ⊢
      exact ⟨⟨h1.1, fun heq => hn (mem_singleton_iff.mp heq ▸ he)⟩, h1.2⟩
    have hS : ∀ z ∈ w'.support, z ∈ S := by
      intro z hz
      simp only [w', SimpleGraph.Walk.support_transfer, w,
        SimpleGraph.Walk.support_map, List.mem_map] at hz
      obtain ⟨z, _, rfl⟩ := hz
      exact z.property
    exact ⟨w'.induce S hS⟩
  · exact localConn_mono_config S a b sdiff_subset

/-- Through-set events within a deleted component are unaffected by the
separating edge. This does not assert configuration monotonicity. -/
theorem throughSet_sdiff_iff_of_same_deleted_cluster (A : Set V)
    {ω η : Config V} {o a b u v : V}
    (hη : η ⊆ ω) (ha : ω \ {s(u, v)} ∈ conn o a)
    (hb : ω \ {s(u, v)} ∈ conn o b) (hv : ω \ {s(u, v)} ∉ conn o v) :
    η ∈ throughSet A a b ↔ η \ {s(u, v)} ∈ throughSet A a b := by
  classical
  rw [mem_throughSet_iff, mem_throughSet_iff]
  apply and_congr (conn_sdiff_iff_of_same_deleted_cluster hη ha hb hv)
  apply not_congr
  exact exists_congr fun hx => exists_congr fun hy =>
    localConn_sdiff_iff_of_same_deleted_cluster Aᶜ ⟨a, hx⟩ ⟨b, hy⟩ hη ha hb hv

/-- Pivotal pairs for a connection inside the deleted component are unchanged
by the separating edge, with the same orientation. -/
theorem orientedPivotal_sdiff_iff_of_same_deleted_cluster
    {ω : Config V} {x z u v a b : V}
    (hz : ω \ {s(u, v)} ∈ conn x z) (hv : ω \ {s(u, v)} ∉ conn x v) :
    ω ∈ orientedPivotal x z a b ↔ ω \ {s(u, v)} ∈ orientedPivotal x z a b := by
  classical
  have hcomm : (ω \ {s(a, b)}) \ {s(u, v)} =
      (ω \ {s(u, v)}) \ {s(a, b)} := by ext e; simp only [mem_sdiff]; tauto
  constructor
  · intro h
    have ha := conn_prefix_of_pivotal sdiff_subset h.2.1 hz
    have hb : ω \ {s(u, v)} ∈ conn x b :=
      conn_prefix_of_pivotal (u := b) (v := a) sdiff_subset
        (by simpa only [Sym2.eq_swap] using h.2.1) hz
    refine ⟨conn_mono (subset_insert _ _) hz, ?_, ?_, ?_⟩
    · exact fun hh => h.2.1 (conn_mono (sdiff_subset_sdiff_left sdiff_subset) hh)
    · rw [← hcomm]
      exact (conn_sdiff_iff_of_same_deleted_cluster sdiff_subset
        (SimpleGraph.Reachable.refl x) ha hv).mp h.2.2.1
    · rw [← hcomm]
      exact (conn_sdiff_iff_of_same_deleted_cluster sdiff_subset hb hz hv).mp h.2.2.2
  · intro h
    refine ⟨conn_mono (fun _ he => mem_insert_of_mem _ he.1) hz, ?_,
      conn_mono (sdiff_subset_sdiff_left sdiff_subset) h.2.2.1,
      conn_mono (sdiff_subset_sdiff_left sdiff_subset) h.2.2.2⟩
    intro hh
    apply h.2.1
    rw [← hcomm]
    exact (conn_sdiff_iff_of_same_deleted_cluster sdiff_subset
      (SimpleGraph.Reachable.refl x) hz hv).mp hh

/-- `E'` for the cutting prefix is unchanged when the separating pair is
declared closed. -/
theorem laceEPrime_sdiff_iff_of_same_deleted_cluster (A : Set V)
    {ω : Config V} {x z u v : V}
    (hz : ω \ {s(u, v)} ∈ conn x z) (hv : ω \ {s(u, v)} ∉ conn x v) :
    ω ∈ laceEPrime A x z ↔ ω \ {s(u, v)} ∈ laceEPrime A x z := by
  classical
  have ht := throughSet_sdiff_iff_of_same_deleted_cluster A (η := ω) Subset.rfl
    (SimpleGraph.Reachable.refl x) hz hv
  have he : (ω ∈ ⋃ a, ⋃ b, orientedPivotal x z a b ∩ throughSet A x a) ↔
      ω \ {s(u, v)} ∈ ⋃ a, ⋃ b, orientedPivotal x z a b ∩ throughSet A x a := by
    simp only [mem_iUnion, mem_inter_iff]
    apply exists_congr
    intro a
    apply exists_congr
    intro b
    have hp := orientedPivotal_sdiff_iff_of_same_deleted_cluster (a := a) (b := b) hz hv
    constructor
    · rintro ⟨h, ha⟩
      have hxa := conn_prefix_of_pivotal sdiff_subset h.2.1 hz
      exact ⟨hp.mp h, (throughSet_sdiff_iff_of_same_deleted_cluster A Subset.rfl
        (SimpleGraph.Reachable.refl x) hxa hv).mp ha⟩
    · rintro ⟨h, ha⟩
      have hxa := conn_mono sdiff_subset h.2.2.1
      exact ⟨hp.mpr h, (throughSet_sdiff_iff_of_same_deleted_cluster A Subset.rfl
        (SimpleGraph.Reachable.refl x) hxa hv).mpr ha⟩
  exact and_congr ht (not_congr he)

/-- On the source cluster of the graph with the cutting pair removed, the
cutting event separates into `E'`, occupation, and a connection outside that
cluster. The avoiding connection retains its endpoint membership conditions. -/
theorem mem_cuttingEvent_iff_deleted_cluster (A : Set V) (ω : Config V)
    (x y u v : V) :
    ω ∈ cuttingEvent A x y u v ↔ s(u, v) ∈ ω ∧
      ω \ {s(u, v)} ∈ laceEPrime A x u ∧
      ∃ hv : v ∈ (cluster (ω \ {s(u, v)}) x)ᶜ,
        ∃ hy : y ∈ (cluster (ω \ {s(u, v)}) x)ᶜ,
          ((openGraph ω).induce (cluster (ω \ {s(u, v)}) x)ᶜ).Reachable
            ⟨v, hv⟩ ⟨y, hy⟩ := by
  classical
  constructor
  · intro h
    have hp := h.1.2
    have hv : ω \ {s(u, v)} ∉ conn x v :=
      fun hv => hp.2.1 (conn_trans hv hp.2.2.2)
    refine ⟨h.2, (laceEPrime_sdiff_iff_of_same_deleted_cluster A hp.2.2.1 hv).mp h.1.1,
      hv, hp.2.1, ?_⟩
    obtain ⟨p⟩ := hp.2.2.2
    have hS : ∀ z ∈ p.support, z ∈ (cluster (ω \ {s(u, v)}) x)ᶜ := by
      intro z hz hzx
      exact hv (conn_trans hzx (p.takeUntil z hz).reachable.symm)
    exact localConn_mono_config _ _ _ sdiff_subset ⟨p.induce _ hS⟩
  · rintro ⟨he, hE, hv, hy, hloc⟩
    have hxu : ω \ {s(u, v)} ∈ conn x u := hE.1.1
    have hloc' : ((openGraph (ω \ {s(u, v)})).induce
        (cluster (ω \ {s(u, v)}) x)ᶜ).Reachable ⟨v, hv⟩ ⟨y, hy⟩ := by
      apply (localConn_iff_of_agree _ ⟨v, hv⟩ ⟨y, hy⟩ (ω := ω)
        (ω' := ω \ {s(u, v)}) ?_).mp hloc
      intro a ha b hb
      have hn : s(a, b) ≠ s(u, v) := by
        intro hab
        rcases Sym2.eq_iff.mp hab with ⟨rfl, _⟩ | ⟨_, rfl⟩
        · exact ha hxu
        · exact hb hxu
      simp only [mem_sdiff, mem_singleton_iff, hn, not_false_eq_true, and_true]
    have hvy : ω \ {s(u, v)} ∈ conn v y := conn_of_localConn _ _ _ _ hloc'
    have huv : u ≠ v := fun huv => hv (huv ▸ hxu)
    have hsub : ω \ {s(u, v)} ⊆ insert s(u, v) ω :=
      fun _ he => mem_insert_of_mem _ he.1
    have hi : insert s(u, v) ω ∈ conn x y :=
      conn_trans (conn_trans (conn_mono hsub hxu)
        (mem_conn_of_mem huv (mem_insert _ _))) (conn_mono hsub hvy)
    exact ⟨⟨(laceEPrime_sdiff_iff_of_same_deleted_cluster A hxu hv).mpr hE,
      hi, hy, hxu, hvy⟩, he⟩

/-- Deterministic slicing at a specified deleted cluster. -/
theorem cuttingEvent_inter_deleted_cluster_eq (A C : Set V) (x y u v : V) :
    cuttingEvent A x y u v ∩ {ω | cluster (ω \ {s(u, v)}) x = C} =
      {ω | s(u, v) ∈ ω} ∩
        ({ω | ω \ {s(u, v)} ∈ laceEPrime A x u ∧
          cluster (ω \ {s(u, v)}) x = C} ∩
          {ω | ∃ hv : v ∈ Cᶜ, ∃ hy : y ∈ Cᶜ,
            ((openGraph ω).induce Cᶜ).Reachable ⟨v, hv⟩ ⟨y, hy⟩}) := by
  classical
  ext ω
  constructor
  · rintro ⟨h, hC⟩
    obtain ⟨he, hE, hout⟩ := (mem_cuttingEvent_iff_deleted_cluster A ω x y u v).mp h
    exact ⟨he, ⟨hE, hC⟩, hC ▸ hout⟩
  · rintro ⟨he, ⟨hE, hC⟩, hout⟩
    exact ⟨(mem_cuttingEvent_iff_deleted_cluster A ω x y u v).mpr
      ⟨he, hE, hC.symm ▸ hout⟩, hC⟩

/-- Countable slicing of a cutting probability by its finite deleted cluster.
The finiteness condition is explicit and is only required almost surely. -/
theorem law_cuttingEvent_eq_tsum_deleted_cluster [Countable V]
    (q : Sym2 V → unitInterval) (A : Set V) (x y u v : V)
    (hfin : ∀ᵐ ω ∂law q, (cluster (ω \ {s(u, v)}) x).Finite) :
    law q (cuttingEvent A x y u v) =
      ∑' C : Finset V, law q (cuttingEvent A x y u v ∩
        {ω | cluster (ω \ {s(u, v)}) x = (C : Set V)}) := by
  classical
  have hm (C : Finset V) : MeasurableSet (cuttingEvent A x y u v ∩
      {ω | cluster (ω \ {s(u, v)}) x = (C : Set V)}) :=
    (measurableSet_cuttingEvent A x y u v).inter
      ((measurableSet_singleton (C : Set V)).preimage
        ((measurable_cluster x).comp (measurable_diff_singleton s(u, v))))
  have hd : Pairwise fun C D : Finset V =>
      Disjoint (cuttingEvent A x y u v ∩ {ω | cluster (ω \ {s(u, v)}) x = (C : Set V)})
        (cuttingEvent A x y u v ∩ {ω | cluster (ω \ {s(u, v)}) x = (D : Set V)}) := by
    intro C D hCD
    exact Set.disjoint_left.mpr fun _ hC hD =>
      hCD (Finset.coe_injective (hC.2.symm.trans hD.2))
  rw [← measure_iUnion hd hm]
  apply measure_congr
  filter_upwards [hfin] with ω hω
  apply propext
  simp only [mem_iUnion, mem_inter_iff, mem_ofPred_eq]
  constructor
  · intro h
    exact ⟨hω.toFinset, h, by simp⟩
  · rintro ⟨_, h, _⟩
    exact h

/-- Exact cutting-bond factorization on one specified deleted cluster.
The prefix, the cutting coordinate, and the exterior connection use disjoint
sets of Bernoulli coordinates. -/
theorem law_cuttingEvent_inter_deleted_cluster [Countable V]
    (q : Sym2 V → unitInterval) (A C : Set V) (x y u v : V) :
    law q (cuttingEvent A x y u v ∩ {ω | cluster (ω \ {s(u, v)}) x = C}) =
      (unitInterval.toNNReal (q s(u, v)) : ℝ≥0∞) *
        law q {ω | ω \ {s(u, v)} ∈ laceEPrime A x u ∧
          cluster (ω \ {s(u, v)}) x = C} *
        law q {ω | ∃ hv : v ∈ Cᶜ, ∃ hy : y ∈ Cᶜ,
          ((openGraph ω).induce Cᶜ).Reachable ⟨v, hv⟩ ⟨y, hy⟩} := by
  classical
  by_cases hu : u ∈ C
  · let R : Set (Config V) := {ω | ω \ {s(u, v)} ∈ laceEPrime A x u ∧
        cluster (ω \ {s(u, v)}) x = C}
    let B : Set (Config V) := {ω | ∃ hv : v ∈ Cᶜ, ∃ hy : y ∈ Cᶜ,
        ((openGraph ω).induce Cᶜ).Reachable ⟨v, hv⟩ ⟨y, hy⟩}
    let P : Set (Sym2 V) := {e | ∃ z ∈ e, z ∈ C} \ {s(u, v)}
    let Q : Set (Sym2 V) := {e | ∀ z ∈ e, z ∉ C}
    have hR : MeasurableSet R :=
      ((measurableSet_laceEPrime A x u).preimage (measurable_diff_singleton s(u, v))).inter
        ((measurableSet_singleton C).preimage
          ((measurable_cluster x).comp (measurable_diff_singleton s(u, v))))
    have hB : MeasurableSet B := measurableSet_conn_avoiding C v y
    have hRd : ∀ ω η : Config V, ω ∩ P = η ∩ P → (ω ∈ R ↔ η ∈ R) := by
      intro ω η hag
      apply laceEPrime_cluster_iff_of_eqOn_touch
      intro e he
      by_cases heq : e = s(u, v)
      · simp [heq]
      · have hP : e ∈ P := ⟨he, heq⟩
        have h := congrArg (e ∈ ·) hag
        simpa only [mem_sdiff, mem_singleton_iff, heq, not_false_eq_true, and_true,
          mem_inter_iff, hP, eq_iff_iff] using h
    have hBd : ∀ ω η : Config V, ω ∩ Q = η ∩ Q → (ω ∈ B ↔ η ∈ B) := by
      intro ω η hag
      apply exists_congr
      intro hv
      apply exists_congr
      intro hy
      apply localConn_iff_of_agree
      intro a ha b hb
      have hQ : s(a, b) ∈ Q := by
        intro z hz
        rcases Sym2.mem_iff.mp hz with rfl | rfl <;> assumption
      have h := congrArg (s(a, b) ∈ ·) hag
      simpa only [mem_inter_iff, hQ, and_true, eq_iff_iff] using h
    have hPQ : Disjoint P Q := by
      apply Set.disjoint_left.mpr
      rintro e ⟨⟨z, hze, hzC⟩, _⟩ hQ
      exact hQ z hze hzC
    have hRBd : ∀ ω η : Config V, ω ∩ {s(u, v)}ᶜ = η ∩ {s(u, v)}ᶜ →
        (ω ∈ R ∩ B ↔ η ∈ R ∩ B) := by
      intro ω η hag
      have hd : ω \ {s(u, v)} = η \ {s(u, v)} := hag
      have hRi : ω ∈ R ↔ η ∈ R := by change (_ ∧ _) ↔ (_ ∧ _); rw [hd]
      apply and_congr hRi
      apply hBd
      ext e
      by_cases he : e ∈ Q
      · have hne : e ≠ s(u, v) := by
          rintro rfl
          exact he u (Sym2.mem_mk_left u v) hu
        have h := congrArg (e ∈ ·) hag
        simpa only [mem_inter_iff, mem_compl_iff, mem_singleton_iff, hne,
          not_false_eq_true, he, and_true, eq_iff_iff] using h
      · simp only [mem_inter_iff, he, and_false]
    rw [cuttingEvent_inter_deleted_cluster_eq]
    change prodBernoulli q ({ω | s(u, v) ∈ ω} ∩ (R ∩ B)) =
      (unitInterval.toNNReal (q s(u, v)) : ℝ≥0∞) * prodBernoulli q R * prodBernoulli q B
    rw [prodBernoulli_inter_of_determined q (P := {s(u, v)}) (Q := {s(u, v)}ᶜ)
      disjoint_compl_right (measurableSet_mem _) (hR.inter hB)
      (fun ω η h => by
        have hh := congrArg (s(u, v) ∈ ·) h
        simpa only [mem_ofPred_eq, mem_inter_iff, mem_singleton_iff, and_true,
          eq_iff_iff] using hh) hRBd,
      prodBernoulli_setOf_mem,
      prodBernoulli_inter_of_determined q hPQ hR hB hRd hBd]
    exact (mul_assoc _ _ _).symm
  · have hR : {ω : Config V | ω \ {s(u, v)} ∈ laceEPrime A x u ∧
        cluster (ω \ {s(u, v)}) x = C} = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      rintro ω ⟨hE, hC⟩
      exact hu (hC ▸ hE.1.1)
    rw [cuttingEvent_inter_deleted_cluster_eq, hR]
    simp

/-- The cutting-bond factorization, with the random deleted cluster summed
explicitly. Almost-sure finiteness is the only cluster-size hypothesis. -/
theorem law_cuttingEvent_eq_tsum_factorization [Countable V]
    (q : Sym2 V → unitInterval) (A : Set V) (x y u v : V)
    (hfin : ∀ᵐ ω ∂law q, (cluster (ω \ {s(u, v)}) x).Finite) :
    law q (cuttingEvent A x y u v) =
      (unitInterval.toNNReal (q s(u, v)) : ℝ≥0∞) *
        ∑' C : Finset V,
          law q {ω | ω \ {s(u, v)} ∈ laceEPrime A x u ∧
            cluster (ω \ {s(u, v)}) x = (C : Set V)} *
          law q {ω | ∃ hv : v ∈ (C : Set V)ᶜ, ∃ hy : y ∈ (C : Set V)ᶜ,
            ((openGraph ω).induce (C : Set V)ᶜ).Reachable ⟨v, hv⟩ ⟨y, hy⟩} := by
  classical
  rw [law_cuttingEvent_eq_tsum_deleted_cluster q A x y u v hfin]
  simp_rw [law_cuttingEvent_inter_deleted_cluster, mul_assoc]
  exact ENNReal.tsum_mul_left

/-- The cutting-bond factorization on two independent layers. The first layer
supplies `E'` and its deleted cluster; the second supplies the exterior connection.
This is the resampling form used to iterate the lace expansion. -/
theorem law_cuttingEvent_eq_prod [Countable V]
    (q : Sym2 V → unitInterval) (A : Set V) (x y u v : V)
    (hfin : ∀ᵐ ω ∂law q, (cluster (ω \ {s(u, v)}) x).Finite) :
    law q (cuttingEvent A x y u v) =
      (unitInterval.toNNReal (q s(u, v)) : ℝ≥0∞) *
        ((law q).prod (law q)) {p : Config V × Config V |
          p.1 \ {s(u, v)} ∈ laceEPrime A x u ∧
          ∃ hv : v ∈ (cluster (p.1 \ {s(u, v)}) x)ᶜ,
            ∃ hy : y ∈ (cluster (p.1 \ {s(u, v)}) x)ᶜ,
              ((openGraph p.2).induce (cluster (p.1 \ {s(u, v)}) x)ᶜ).Reachable
                ⟨v, hv⟩ ⟨y, hy⟩} := by
  classical
  rw [law_cuttingEvent_eq_tsum_factorization q A x y u v hfin]
  congr 1
  let R : Finset V → Set (Config V) := fun C =>
    {ω | ω \ {s(u, v)} ∈ laceEPrime A x u ∧
      cluster (ω \ {s(u, v)}) x = (C : Set V)}
  let B : Finset V → Set (Config V) := fun C =>
    {ω | ∃ hv : v ∈ (C : Set V)ᶜ, ∃ hy : y ∈ (C : Set V)ᶜ,
      ((openGraph ω).induce (C : Set V)ᶜ).Reachable ⟨v, hv⟩ ⟨y, hy⟩}
  have hmR (C : Finset V) : MeasurableSet (R C) :=
    ((measurableSet_laceEPrime A x u).preimage (measurable_diff_singleton s(u, v))).inter
      ((measurableSet_singleton (C : Set V)).preimage
        ((measurable_cluster x).comp (measurable_diff_singleton s(u, v))))
  have hmB (C : Finset V) : MeasurableSet (B C) :=
    measurableSet_conn_avoiding (C : Set V) v y
  have hd : Pairwise fun C D : Finset V => Disjoint (R C ×ˢ B C) (R D ×ˢ B D) := by
    intro C D hCD
    exact Set.disjoint_left.mpr fun _ hC hD =>
      hCD (Finset.coe_injective (hC.1.2.symm.trans hD.1.2))
  have hprod : ∀ᵐ p : Config V × Config V ∂(law q).prod (law q),
      (cluster (p.1 \ {s(u, v)}) x).Finite :=
    Measure.quasiMeasurePreserving_fst.ae hfin
  calc
    (∑' C : Finset V, law q (R C) * law q (B C)) =
        ∑' C : Finset V, ((law q).prod (law q)) (R C ×ˢ B C) := by
      simp only [Measure.prod_prod]
    _ = ((law q).prod (law q)) (⋃ C : Finset V, R C ×ˢ B C) :=
      (measure_iUnion hd fun C => (hmR C).prod (hmB C)).symm
    _ = _ := by
      apply measure_congr
      filter_upwards [hprod] with p hp
      apply propext
      simp only [mem_iUnion, mem_prod, R, B, mem_ofPred_eq]
      constructor
      · rintro ⟨C, ⟨hE, hC⟩, hout⟩
        exact ⟨hE, hC.symm ▸ hout⟩
      · rintro ⟨hE, hout⟩
        refine ⟨hp.toFinset, ⟨hE, by simp⟩, ?_⟩
        rw [hp.coe_toFinset]
        exact hout

/-- When the far endpoint is outside the deleted source cluster, `E'` for
the near endpoint is independent of the state of the separating pair. -/
theorem laceEPrime_sdiff_iff_of_not_conn (A : Set V) {ω : Config V} {x u v : V}
    (hv : ω \ {s(u, v)} ∉ conn x v) :
    ω ∈ laceEPrime A x u ↔ ω \ {s(u, v)} ∈ laceEPrime A x u := by
  classical
  constructor
  · intro hE
    have hxu : ω \ {s(u, v)} ∈ conn x u := by
      rcases reachable_sdiff_or_of_reachable_insert
        (conn_mono (subset_insert s(u, v) ω) hE.1.1) with h | ⟨h, _⟩ | ⟨h, _⟩
      · exact h
      · exact h
      · exact (hv h).elim
    exact (laceEPrime_sdiff_iff_of_same_deleted_cluster A hxu hv).mp hE
  · intro hE
    exact (laceEPrime_sdiff_iff_of_same_deleted_cluster A hE.1.1 hv).mpr hE

/-- The usual independent-layer cutting-bond identity: `E'` is evaluated on
the unmodified first layer, as in the positive lace coefficients. -/
@[tag "ONAY"]
theorem law_cuttingEvent_eq_prod_laceEPrime [Countable V]
    (q : Sym2 V → unitInterval) (A : Set V) (x y u v : V)
    (hfin : ∀ᵐ ω ∂law q, (cluster (ω \ {s(u, v)}) x).Finite) :
    law q (cuttingEvent A x y u v) =
      (unitInterval.toNNReal (q s(u, v)) : ℝ≥0∞) *
        ((law q).prod (law q)) {p : Config V × Config V |
          p.1 ∈ laceEPrime A x u ∧
          ∃ hv : v ∈ (cluster (p.1 \ {s(u, v)}) x)ᶜ,
            ∃ hy : y ∈ (cluster (p.1 \ {s(u, v)}) x)ᶜ,
              ((openGraph p.2).induce (cluster (p.1 \ {s(u, v)}) x)ᶜ).Reachable
                ⟨v, hv⟩ ⟨y, hy⟩} := by
  classical
  rw [law_cuttingEvent_eq_prod q A x y u v hfin]
  congr 2
  ext p
  constructor
  · rintro ⟨hE, hv, hy, hout⟩
    exact ⟨(laceEPrime_sdiff_iff_of_not_conn A hv).mpr hE, hv, hy, hout⟩
  · rintro ⟨hE, hv, hy, hout⟩
    exact ⟨(laceEPrime_sdiff_iff_of_not_conn A hv).mp hE, hv, hy, hout⟩

end PercLib.Percolation.Bond.Lace
