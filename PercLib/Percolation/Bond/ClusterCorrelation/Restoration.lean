/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
The restoration map preserves the product law (the coupling in the proof of Lemma I.4.12 of T.
Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1). The statements are ported from
the repository `yujinhkim/lrp`, branch `critical-lrp-1`, commit
`d382e4c28d92dd4e698ebf4f2aaf0bc932ae73fc`, files
`PercLib/CriticalLRP/CountableProduct/RandomRestoration.lean`,
`PercLib/CriticalLRP/CountableProduct/EdgeTouch.lean` and
`PercLib/CriticalLRP/Correlation/TwoClusterGap.lean` (`cluster_eq_of_eqOn_touchSet`,
`map_restoreMap`); licence Apache-2.0 as declared in those file headers and
`third_party/critical-lrp/NOTICE.md`; upstream `yujinhkim/Critical-Long-range-percolation` at
`3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf` (not independently verified). Contributor: yujinhkim. The
proofs are new: law preservation is proved by restoring along truncated clusters (finite, hence
countably many values, each a stopping set) and passing to the limit on the generating cylinders.
-/
module

public import PercLib.Percolation.Bond.ClusterCorrelation.Defs
public import PercLib.Percolation.Bond.ClusterTails
public import PercLib.Percolation.Bond.ProfileRegularity
public import PercLib.Percolation.Bond.Susceptibility
public import PercLib.Probability.Coordinate
public import PercLib.Probability.Cylinder
public import PercLib.Probability.DeterminedIndependence
public import PercLib.Probability.OpenEventHarris
public import PercLib.Probability.Superposition
public import Mathlib.MeasureTheory.Integral.Indicator
public import Mathlib.MeasureTheory.Measure.Prod

/-! # The restoration map preserves the law

Write `T(ω) = {e | ∃ v ∈ e, v ∈ cluster ω o}` for the pairs touching the cluster of `o`.

* `cluster_eq_of_eqOn_touch` (item 1): a configuration that agrees with `ω` on
  `T(ω)` has the same cluster of `o`; in particular `cluster_restoreMap`.
* `map_restoreMap` (item 2): `(μ ⊗ μ).map (restoreMap o) = μ` for `μ = law q`, every
  profile `q` and countable `V`.
* `restoreMap_eq_snd_off_touch`, `cluster_restoreMap_subset_snd` (items 3 and 4): off
  `T(ω)` the restored configuration is `ω'`, and a cluster of `ω̃` that avoids `K_o(ω)` is
  contained in the cluster of `ω'`.
-/

@[expose] public section
noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology
open PercLib.Probability

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-! ### Clusters are determined by the pairs touching them -/

/-- **Cluster agreement.** If `ω'` agrees with `ω` on the pairs touching the cluster of `o`
in `ω`, the two configurations have the same cluster of `o`. -/
theorem cluster_eq_of_eqOn_touch {ω ω' : Config V} {o : V}
    (h : ∀ e, (∃ v ∈ e, v ∈ cluster ω o) → (e ∈ ω' ↔ e ∈ ω)) :
    cluster ω' o = cluster ω o := by
  have hmem : ∀ {z w : V}, z ∈ cluster ω o → (s(z, w) ∈ ω' ↔ s(z, w) ∈ ω) :=
    fun hz => h _ ⟨_, Sym2.mem_mk_left _ _, hz⟩
  ext y
  constructor
  · intro hy
    change (openGraph ω').Reachable o y at hy
    rw [SimpleGraph.reachable_iff_reflTransGen] at hy
    induction hy with
    | refl => exact mem_cluster_self ω o
    | @tail z w _ hadj ih =>
      rw [openGraph_adj_iff] at hadj
      exact (show (openGraph ω).Reachable o z from ih).trans
        (SimpleGraph.Adj.reachable ((openGraph_adj_iff ω z w).2 ⟨(hmem ih).1 hadj.1, hadj.2⟩))
  · intro hy
    change (openGraph ω).Reachable o y at hy
    rw [SimpleGraph.reachable_iff_reflTransGen] at hy
    induction hy with
    | refl => exact mem_cluster_self ω' o
    | @tail z w hz hadj ih =>
      rw [openGraph_adj_iff] at hadj
      have hzω : z ∈ cluster ω o := (SimpleGraph.reachable_iff_reflTransGen _ _).2 hz
      exact (show (openGraph ω').Reachable o z from ih).trans
        (SimpleGraph.Adj.reachable ((openGraph_adj_iff ω' z w).2 ⟨(hmem hzω).2 hadj.1, hadj.2⟩))

/-- The restored configuration has the cluster of `o` of its first argument. -/
theorem cluster_restoreMap (o : V) (p : Config V × Config V) :
    cluster (restoreMap o p) o = cluster p.1 o :=
  cluster_eq_of_eqOn_touch fun _ he => mem_restoreMap_of_touch he

/-- **Item 3.** Off the pairs touching `K_o(ω)`, the restored configuration is `ω'`. -/
theorem restoreMap_eq_snd_off_touch (o : V) (p : Config V × Config V) :
    restoreMap o p ∩ {e | ¬∃ v ∈ e, v ∈ cluster p.1 o} =
      p.2 ∩ {e | ¬∃ v ∈ e, v ∈ cluster p.1 o} := by
  ext e
  simp only [mem_inter_iff, mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨(mem_restoreMap_of_not_touch h2).1 h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨(mem_restoreMap_of_not_touch h2).2 h1, h2⟩

/-- **Fresh clusters (item 4).** If `y` is not in `K_o(ω)`, the cluster of `y` in the
restored configuration avoids `K_o(ω)` and is contained in the cluster of `y` in `ω'`. -/
theorem cluster_restoreMap_subset_snd {o y : V} {p : Config V × Config V}
    (hy : y ∉ cluster p.1 o) :
    cluster (restoreMap o p) y ⊆ cluster p.2 y ∩ (cluster p.1 o)ᶜ := by
  intro w hw
  change (openGraph (restoreMap o p)).Reachable y w at hw
  rw [SimpleGraph.reachable_iff_reflTransGen] at hw
  induction hw with
  | refl => exact ⟨mem_cluster_self _ _, hy⟩
  | @tail z w hz hadj ih =>
    rw [openGraph_adj_iff] at hadj
    have hzw : (openGraph (restoreMap o p)).Reachable z w :=
      SimpleGraph.Adj.reachable ((openGraph_adj_iff _ z w).2 hadj)
    have hwK : w ∉ cluster p.1 o := by
      intro hw
      rw [← cluster_restoreMap o p] at hw
      have : y ∈ cluster (restoreMap o p) o :=
        (show (openGraph (restoreMap o p)).Reachable o w from hw).trans
          ((SimpleGraph.reachable_iff_reflTransGen _ _).2 hz |>.trans hzw).symm
      exact hy (by rwa [cluster_restoreMap] at this)
    have hnt : ¬∃ v ∈ s(z, w), v ∈ cluster p.1 o := by
      rintro ⟨v, hv, hvK⟩
      rcases Sym2.mem_iff.1 hv with rfl | rfl
      · exact ih.2 hvK
      · exact hwK hvK
    exact ⟨(show (openGraph p.2).Reachable y z from ih.1).trans
      (SimpleGraph.Adj.reachable ((openGraph_adj_iff _ z w).2
        ⟨(mem_restoreMap_of_not_touch hnt).1 hadj.1, hadj.2⟩)), hwK⟩

/-! ### Law preservation -/

/-- The cluster of a finite set of pairs is finite. -/
theorem finite_cluster_inter_finset (ω : Config V) (E : Finset (Sym2 V)) (o : V) :
    (cluster (ω ∩ E) o).Finite := by
  have hfin : ∀ e : Sym2 V, {v : V | v ∈ e}.Finite := by
    intro e
    induction e using Sym2.ind with
    | _ a b =>
      refine (Set.toFinite ({a, b} : Set V)).subset fun v hv => ?_
      rcases Sym2.mem_iff.1 hv with rfl | rfl <;> simp
  refine ((Set.finite_singleton o).union (E.finite_toSet.biUnion fun e _ => hfin e)).subset ?_
  intro y hy
  change (openGraph (ω ∩ E)).Reachable o y at hy
  rw [SimpleGraph.reachable_iff_reflTransGen] at hy
  induction hy with
  | refl => exact Or.inl rfl
  | @tail z w _ hadj _ =>
    rw [openGraph_adj_iff] at hadj
    exact Or.inr (mem_biUnion hadj.1.2 (Sym2.mem_mk_right z w))

/-- The event that a cluster equals a given set is determined by the pairs touching it. -/
theorem cluster_eq_iff_of_inter_eq {ω η : Config V} {o : V} {S : Set V}
    (h : ω ∩ {e | ∃ v ∈ e, v ∈ S} = η ∩ {e | ∃ v ∈ e, v ∈ S}) :
    cluster ω o = S ↔ cluster η o = S := by
  have key : ∀ {ω η : Config V},
      ω ∩ {e | ∃ v ∈ e, v ∈ S} = η ∩ {e | ∃ v ∈ e, v ∈ S} →
        cluster ω o = S → cluster η o = S := fun {ω η} h hω => by
    rw [← hω]
    refine cluster_eq_of_eqOn_touch fun e he => ?_
    rw [hω] at he
    have := congrArg (e ∈ ·) h
    simp only [mem_inter_iff, mem_ofPred_eq, he, and_true, eq_iff_iff] at this
    exact this.symm
  exact ⟨key h, key h.symm⟩

/-- The restoration along a cluster read through a measurable map is measurable. -/
theorem measurable_restore_comp [Countable V] (o : V) {T : Config V → Config V}
    (hT : Measurable T) :
    Measurable fun p : Config V × Config V =>
      {e | e ∈ p.1 ∧ ∃ v ∈ e, v ∈ cluster (T p.1) o} ∪
        {e | e ∈ p.2 ∧ ¬∃ v ∈ e, v ∈ cluster (T p.1) o} := by
  refine Measurable.of_mem fun e => measurableSet_setOfPred.1 ?_
  have hTo : MeasurableSet {p : Config V × Config V | ∃ v ∈ e, v ∈ cluster (T p.1) o} := by
    have : {p : Config V × Config V | ∃ v ∈ e, v ∈ cluster (T p.1) o} =
        ⋃ v ∈ {v | v ∈ e}, (fun p : Config V × Config V => T p.1) ⁻¹' conn o v := by
      ext p; simp [cluster, conn]
    rw [this]
    exact MeasurableSet.biUnion (to_countable _) fun v _ =>
      (hT.comp measurable_fst) (measurableSet_conn o v)
  have h1 : MeasurableSet {p : Config V × Config V | e ∈ p.1} :=
    measurable_fst (measurableSet_setOfPred.2 (measurable_set_mem e))
  have h2 : MeasurableSet {p : Config V × Config V | e ∈ p.2} :=
    measurable_snd (measurableSet_setOfPred.2 (measurable_set_mem e))
  exact (h1.inter hTo).union (h2.inter hTo.compl)

/-- Restoring along the cluster of a finite window preserves the law. -/
theorem prod_restore_window_finset_subset [Countable V] (q : Sym2 V → unitInterval) (o : V)
    (E : Finset (Sym2 V)) (F : Finset (Sym2 V)) :
    ((law q).prod (law q)) {p | (F : Set (Sym2 V)) ⊆
        {e | e ∈ p.1 ∧ ∃ v ∈ e, v ∈ cluster (p.1 ∩ E) o} ∪
          {e | e ∈ p.2 ∧ ¬∃ v ∈ e, v ∈ cluster (p.1 ∩ E) o}} =
      law q {ω | (F : Set (Sym2 V)) ⊆ ω} := by
  classical
  set μ := law q
  have hE : Measurable fun ω : Config V => ω ∩ (E : Set (Sym2 V)) :=
    Measurable.of_mem fun f => by
      by_cases hf : f ∈ (E : Set (Sym2 V))
      · simpa [hf] using measurable_set_mem f
      · simp [hf]
  have hK : Measurable fun ω : Config V => cluster (ω ∩ E) o := (measurable_cluster o).comp hE
  set T : Finset V → Set (Sym2 V) := fun S => {e | ∃ v ∈ e, v ∈ (S : Set V)}
  set A : Finset V → Set (Config V) := fun S =>
    {ω | cluster (ω ∩ E) o = S ∧ (F : Set (Sym2 V)) ∩ T S ⊆ ω}
  set B : Finset V → Set (Config V) := fun S => {ω | (F : Set (Sym2 V)) \ T S ⊆ ω}
  have hFsub : ∀ (G : Set (Sym2 V)), G.Finite → MeasurableSet {ω : Config V | G ⊆ ω} :=
    fun G hG => by
      have := measurableSet_setOf_finset_coe_subset (ι := Sym2 V) hG.toFinset
      simpa using this
  have hAm : ∀ S, MeasurableSet (A S) := fun S =>
    (hK (measurableSet_singleton _)).inter (hFsub _ (F.finite_toSet.subset inter_subset_left))
  have hBm : ∀ S, MeasurableSet (B S) := fun S =>
    hFsub _ (F.finite_toSet.subset sdiff_subset)
  -- decomposition of the restored event along the value of the window cluster
  have hdec : {p : Config V × Config V | (F : Set (Sym2 V)) ⊆
      {e | e ∈ p.1 ∧ ∃ v ∈ e, v ∈ cluster (p.1 ∩ E) o} ∪
        {e | e ∈ p.2 ∧ ¬∃ v ∈ e, v ∈ cluster (p.1 ∩ E) o}} = ⋃ S, A S ×ˢ B S := by
    ext p
    simp only [mem_ofPred_eq, mem_iUnion, mem_prod, A, B, T]
    constructor
    · intro h
      obtain ⟨S, hS⟩ : ∃ S : Finset V, (S : Set V) = cluster (p.1 ∩ E) o :=
        ⟨(finite_cluster_inter_finset p.1 E o).toFinset, by simp⟩
      refine ⟨S, ⟨hS.symm, fun e he => ?_⟩, fun e he => ?_⟩
      · rcases h he.1 with h | h
        · exact h.1
        · exact absurd (hS ▸ he.2) h.2
      · rcases h he.1 with h | h
        · exact absurd (hS ▸ h.2) he.2
        · exact h.1
    · rintro ⟨S, ⟨hS, hA⟩, hB⟩ e he
      by_cases ht : ∃ v ∈ e, v ∈ cluster (p.1 ∩ E) o
      · exact Or.inl ⟨hA ⟨he, hS ▸ ht⟩, ht⟩
      · exact Or.inr ⟨hB ⟨he, fun h => ht (hS ▸ h)⟩, ht⟩
  have hdisj : Pairwise (Function.onFun Disjoint fun S => A S ×ˢ B S) := by
    intro S S' hSS'
    refine Set.disjoint_left.2 fun p hp hp' => hSS' ?_
    exact Finset.coe_injective (hp.1.1.symm.trans hp'.1.1)
  rw [hdec, measure_iUnion hdisj fun S => (hAm S).prod (hBm S)]
  simp_rw [Measure.prod_prod]
  -- each term: independence of the two blocks under `μ`
  have hind : ∀ S, μ (A S) * μ (B S) = μ (A S ∩ B S) := by
    intro S
    refine (prodBernoulli_inter_of_determined q (P := T S) (Q := (T S)ᶜ) disjoint_compl_right
      (hAm S) (hBm S) (fun ω η h => ?_) (fun ω η h => ?_)).symm
    · simp only [A, mem_ofPred_eq]
      have hc : (ω ∩ E) ∩ T S = (η ∩ E) ∩ T S := by
        rw [inter_right_comm, h, inter_right_comm]
      rw [cluster_eq_iff_of_inter_eq (o := o) hc]
      refine and_congr_right fun _ => ⟨fun h' e he => ?_, fun h' e he => ?_⟩
      · have := congrArg (e ∈ ·) h
        simp only [mem_inter_iff, he.2, and_true, eq_iff_iff] at this
        exact this.1 (h' he)
      · have := congrArg (e ∈ ·) h
        simp only [mem_inter_iff, he.2, and_true, eq_iff_iff] at this
        exact this.2 (h' he)
    · simp only [B, mem_ofPred_eq]
      constructor
      · intro h' e he
        have := congrArg (e ∈ ·) h
        simp only [mem_inter_iff, mem_compl_iff, he.2, not_false_eq_true, and_true,
          eq_iff_iff] at this
        exact this.1 (h' he)
      · intro h' e he
        have := congrArg (e ∈ ·) h
        simp only [mem_inter_iff, mem_compl_iff, he.2, not_false_eq_true, and_true,
          eq_iff_iff] at this
        exact this.2 (h' he)
  simp_rw [hind]
  -- reassemble
  have hAB : ∀ S, A S ∩ B S = {ω | cluster (ω ∩ E) o = S} ∩ {ω | (F : Set (Sym2 V)) ⊆ ω} := by
    intro S
    ext ω
    simp only [A, B, mem_inter_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨h1, fun e he => ?_⟩
      by_cases ht : e ∈ T S
      · exact h2 ⟨he, ht⟩
      · exact h3 ⟨he, ht⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, fun e he => h2 he.1⟩, fun e he => h2 he.1⟩
  simp_rw [hAB]
  have hCm : ∀ S : Finset V, MeasurableSet
      ({ω : Config V | cluster (ω ∩ E) o = S} ∩ {ω | (F : Set (Sym2 V)) ⊆ ω}) := fun S =>
    (show MeasurableSet {ω : Config V | cluster (ω ∩ E) o = S} from
      hK (measurableSet_singleton _)).inter (hFsub _ F.finite_toSet)
  rw [← measure_iUnion (f := fun S : Finset V =>
      {ω : Config V | cluster (ω ∩ E) o = S} ∩ {ω | (F : Set (Sym2 V)) ⊆ ω})
    (fun S S' hSS' => Set.disjoint_left.2 fun ω hω hω' =>
      hSS' (Finset.coe_injective (hω.1.symm.trans hω'.1))) hCm]
  congr 1
  ext ω
  simp only [mem_iUnion, mem_inter_iff, mem_ofPred_eq]
  exact ⟨fun ⟨_, _, h⟩ => h, fun h =>
    ⟨(finite_cluster_inter_finset ω E o).toFinset, by simp, h⟩⟩

/-- **Item 2: the restoration map preserves the law.** For every profile on a
countable vertex type, `(μ ⊗ μ).map (restoreMap o) = μ` with `μ = law q`. -/
theorem map_restoreMap [Countable V] (q : Sym2 V → unitInterval) (o : V) :
    ((law q).prod (law q)).map (restoreMap o) = law q := by
  classical
  have hmeas := measurable_restoreMap (V := V) o
  have : IsProbabilityMeasure (((law q).prod (law q)).map (restoreMap o)) :=
    (Measure.isProbabilityMeasure_map_iff hmeas.aemeasurable).2 inferInstance
  refine measure_ext_of_finset_subset _ _ fun F => ?_
  rw [Measure.map_apply hmeas (measurableSet_setOf_finset_coe_subset F)]
  obtain ⟨E, hEm, hE⟩ := exists_finset_exhaustion (V := Sym2 V)
  obtain ⟨R, hR⟩ : ∃ R : ℕ → Config V × Config V → Config V, R = fun n p =>
      {e | e ∈ p.1 ∧ ∃ v ∈ e, v ∈ cluster (p.1 ∩ E n) o} ∪
        {e | e ∈ p.2 ∧ ¬∃ v ∈ e, v ∈ cluster (p.1 ∩ E n) o} := ⟨_, rfl⟩
  have hEn : ∀ n, Measurable fun ω : Config V => ω ∩ (E n : Set (Sym2 V)) := fun n =>
    Measurable.of_mem fun f => by
      by_cases hf : f ∈ (E n : Set (Sym2 V))
      · simpa [hf] using measurable_set_mem f
      · simp [hf]
  have hRm : ∀ n, Measurable (R n) := by
    intro n
    rw [hR]
    exact measurable_restore_comp o (hEn n)
  -- the touch status along the truncated clusters converges
  have htouch : ∀ (ω : Config V) (e : Sym2 V), ∀ᶠ n in atTop,
      ((∃ v ∈ e, v ∈ cluster (ω ∩ E n) o) ↔ ∃ v ∈ e, v ∈ cluster ω o) := by
    intro ω e
    by_cases ht : ∃ v ∈ e, v ∈ cluster ω o
    · obtain ⟨v, hve, hv⟩ := ht
      obtain ⟨G, hGω, hG⟩ := exists_finset_of_forall_conn (ω := ω) o {v}
        fun x hx => by rw [Finset.mem_singleton] at hx; subst hx; exact hv
      have hev : ∀ᶠ n in atTop, ∀ f ∈ G, f ∈ E n := by
        rw [eventually_all_finset]
        intro f _
        obtain ⟨k, hk⟩ := hE f
        exact eventually_atTop.2 ⟨k, fun k' hk' => hEm hk' hk⟩
      filter_upwards [hev] with n hn
      refine ⟨fun ⟨w, hw, hwc⟩ => ⟨w, hw, cluster_mono inter_subset_left o hwc⟩,
        fun _ => ⟨v, hve, ?_⟩⟩
      have hsub : ((G : Set (Sym2 V)) : Config V) ⊆ ω ∩ (E n : Set (Sym2 V)) :=
        fun f hf => ⟨hGω hf, hn f hf⟩
      exact conn_mono hsub (hG v (Finset.mem_singleton_self v))
    · exact Eventually.of_forall fun n => ⟨fun ⟨w, hw, hwc⟩ =>
        absurd ⟨w, hw, cluster_mono inter_subset_left o hwc⟩ ht, fun h => absurd h ht⟩
  have hlim : Tendsto (fun n => ((law q).prod (law q)) {p | (F : Set (Sym2 V)) ⊆ R n p})
      atTop (𝓝 (((law q).prod (law q)) (restoreMap o ⁻¹' {ω | (F : Set (Sym2 V)) ⊆ ω}))) := by
    refine tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure atTop
      (hmeas (measurableSet_setOf_finset_coe_subset F))
      (fun n => hRm n (measurableSet_setOf_finset_coe_subset F)) (Eventually.of_forall fun p => ?_)
    have hall : ∀ᶠ n in atTop, ∀ e ∈ F,
        ((∃ v ∈ e, v ∈ cluster (p.1 ∩ E n) o) ↔ ∃ v ∈ e, v ∈ cluster p.1 o) := by
      rw [eventually_all_finset]
      exact fun e _ => htouch p.1 e
    filter_upwards [hall] with n hn
    simp only [mem_ofPred_eq, mem_preimage, hR]
    constructor
    · intro h e he
      rw [mem_restoreMap]
      rcases h he with h | h
      · exact Or.inl ⟨h.1, (hn e he).1 h.2⟩
      · exact Or.inr ⟨h.1, fun h' => h.2 ((hn e he).2 h')⟩
    · intro h e he
      rcases (mem_restoreMap.1 (h he)) with h | h
      · exact Or.inl ⟨h.1, (hn e he).2 h.2⟩
      · exact Or.inr ⟨h.1, fun h' => h.2 ((hn e he).1 h')⟩
  refine tendsto_nhds_unique hlim ?_
  have hc : ∀ n, ((law q).prod (law q)) {p | (F : Set (Sym2 V)) ⊆ R n p} =
      law q {ω | (F : Set (Sym2 V)) ⊆ ω} := fun n => by
    rw [hR]; exact prod_restore_window_finset_subset q o (E n) F
  simp_rw [hc]
  exact tendsto_const_nhds

/-! ### Witnesses -/

/-- On `Bool` with one pair of probability `1/2` (and the loops), restoration preserves the
law; `restoreMap_self` shows the map is the identity on the diagonal. -/
example : ((law fun _ : Sym2 Bool => (⟨1 / 2, by norm_num, by norm_num⟩ : unitInterval)).prod
      (law fun _ : Sym2 Bool => (⟨1 / 2, by norm_num, by norm_num⟩ : unitInterval))).map
        (restoreMap false) =
    law fun _ : Sym2 Bool => (⟨1 / 2, by norm_num, by norm_num⟩ : unitInterval) :=
  map_restoreMap _ false

example (ω ω' : Config Bool) : cluster (restoreMap false (ω, ω')) false = cluster ω false :=
  cluster_restoreMap false (ω, ω')

end PercLib.Percolation.Bond
