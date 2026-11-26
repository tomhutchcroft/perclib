/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-15. No upstream proof is copied.
-/
module

public import PercLib.Percolation.Bond.LocalConnectivity
public import PercLib.Probability.ClosedProduct
public import PercLib.Probability.ProdBernoulliIndependence
public import PercLib.Probability.DeterminedIndependence

/-!
# The law of a finite cluster and the domain Markov property

For a finite set `C ∋ x`, the cluster of `x` is `C` exactly when `C` is internally
connected to `x` and every boundary pair `s(y, z)`, `y ∈ C`, `z ∉ C`, is closed
(`cluster_eq_finset_iff`). These two events depend on the disjoint sets of internal and
boundary pairs, so `P(K_x = C)` factors (`law_cluster_eq_finset`). The event `{K_x = C}`
depends only on pairs meeting `C`, so it is independent of every event determined by the
outer pairs (`law_cluster_eq_inter`, the domain Markov property).

In the spelling with `localConn`, the identity `{K_x = C} = I_C ∩ D_C` holds for every set
`C ∋ x` on any vertex type (`setOf_cluster_eq_eq_inter`). On a countable vertex type the
factorization holds for every `C ∋ x` (`law_cluster_eq_eq_mul`), and the closed-boundary
probability is the infinite product of the closed probabilities of the boundary pairs
(`law_boundary_closed_eq_tprod`).

This file adds no definition. The independence of events determined by disjoint coordinate sets is
used through a private lemma; `PercLib/Probability/DeterminedIndependence.lean` proves a public
version.
-/

@[expose] public section

open MeasureTheory Set PercLib.Probability
open scoped ENNReal

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-! ### The finite-cluster law in the `localConn` spelling -/

/-- **The cluster of `x` is a set `C ∋ x`** exactly when every vertex of `C` is connected to
`x` inside `C` and no pair from `C` to its complement is open. No finiteness or countability
is needed. -/
theorem cluster_eq_iff_forall_localConn (ω : Config V) {x : V} {C : Set V} (hx : x ∈ C) :
    cluster ω x = C ↔
      (∀ y ∈ C, ω ∈ localConn C x y) ∧ ∀ u ∈ C, ∀ v ∉ C, s(u, v) ∉ ω := by
  classical
  constructor
  · intro h
    refine ⟨fun y hy => ?_, fun u hu v hv huv => ?_⟩
    · have hxy : (openGraph ω).Reachable x y := by
        have : y ∈ cluster ω x := by rw [h]; exact hy
        exact this
      obtain ⟨w⟩ := hxy
      have hw : ∀ z ∈ w.support, z ∈ C := fun z hz => by
        rw [← h]
        exact ⟨w.takeUntil z hz⟩
      exact ⟨hx, hy, ⟨w.induce C hw⟩⟩
    · have hne : u ≠ v := fun e => hv (e ▸ hu)
      have hu' : (openGraph ω).Reachable x u := by
        have : u ∈ cluster ω x := by rw [h]; exact hu
        exact this
      have hv' : v ∈ cluster ω x :=
        hu'.trans (SimpleGraph.Adj.reachable ((openGraph_adj_iff ω u v).2 ⟨huv, hne⟩))
      rw [h] at hv'
      exact hv hv'
  · rintro ⟨hin, hbd⟩
    ext v
    constructor
    · intro hv
      change (openGraph ω).Reachable x v at hv
      rw [SimpleGraph.reachable_iff_reflTransGen] at hv
      induction hv with
      | refl => exact hx
      | @tail w z _ hadj ih =>
        by_contra hz
        rw [openGraph_adj_iff] at hadj
        exact hbd w ih z hz hadj.1
    · intro hv
      exact (mem_cluster_iff ω x v).2 (localConn_subset_conn C x v (hin v hv))

/-- **`{K_x = C} = I_C ∩ D_C`** for every set `C ∋ x`, as an identity of events. -/
theorem setOf_cluster_eq_eq_inter {x : V} {C : Set V} (hx : x ∈ C) :
    {ω : Config V | cluster ω x = C} =
      {ω : Config V | ∀ y ∈ C, ω ∈ localConn C x y} ∩
        {ω : Config V | ∀ u ∈ C, ∀ v ∉ C, s(u, v) ∉ ω} := by
  ext ω
  exact cluster_eq_iff_forall_localConn ω hx

/-- The internal connection event `I_C` of a countable set is measurable, whatever the
cardinality of the vertex type. -/
theorem measurableSet_setOf_forall_localConn (x : V) {C : Set V} (hC : C.Countable) :
    MeasurableSet {ω : Config V | ∀ y ∈ C, ω ∈ localConn C x y} := by
  have : Countable C := hC.to_subtype
  have hset : {ω : Config V | ∀ y ∈ C, ω ∈ localConn C x y} = ⋂ y ∈ C, localConn C x y := by
    ext ω
    simp
  rw [hset]
  exact MeasurableSet.biInter hC fun y _ => measurableSet_localConn C x y

/-- The closed-boundary event `D_C` is measurable on a countable vertex type. -/
theorem measurableSet_setOf_boundary_closed [Countable V] (C : Set V) :
    MeasurableSet {ω : Config V | ∀ u ∈ C, ∀ v ∉ C, s(u, v) ∉ ω} := by
  simp only [ofPred_forall]
  exact MeasurableSet.iInter fun u => MeasurableSet.iInter fun _ =>
    MeasurableSet.iInter fun v => MeasurableSet.iInter fun _ => (measurableSet_mem _).compl

/-- The event `{K_x = C}` is measurable on a countable vertex type, for every set `C`. -/
theorem measurableSet_setOf_cluster_eq [Countable V] (x : V) (C : Set V) :
    MeasurableSet {ω : Config V | cluster ω x = C} := by
  by_cases hx : x ∈ C
  · rw [setOf_cluster_eq_eq_inter hx]
    exact (measurableSet_setOf_forall_localConn x C.to_countable).inter
      (measurableSet_setOf_boundary_closed C)
  · have : {ω : Config V | cluster ω x = C} = ∅ :=
      Set.eq_empty_of_forall_notMem fun ω (h : cluster ω x = C) =>
        hx (h ▸ (SimpleGraph.Reachable.refl x : x ∈ cluster ω x))
    rw [this]
    exact MeasurableSet.empty

/-- **The law of a cluster** on a countable vertex type: for every set `C ∋ x`,
`P(K_x = C) = P(I_C) P(D_C)`, since `I_C` and `D_C` depend on disjoint sets of pairs. -/
theorem law_cluster_eq_eq_mul [Countable V] (q : Sym2 V → unitInterval) {x : V} {C : Set V}
    (hx : x ∈ C) :
    law q {ω : Config V | cluster ω x = C} =
      law q {ω : Config V | ∀ y ∈ C, ω ∈ localConn C x y} *
        law q {ω : Config V | ∀ u ∈ C, ∀ v ∉ C, s(u, v) ∉ ω} := by
  rw [setOf_cluster_eq_eq_inter hx]
  refine PercLib.Probability.prodBernoulli_inter_of_determined_inter q {e | ∀ v ∈ e, v ∈ C}
    {e | ∃ u ∈ C, ∃ v ∉ C, e = s(u, v)} ?_ (measurableSet_setOf_forall_localConn x C.to_countable)
    (measurableSet_setOf_boundary_closed C) ?_ ?_
  · refine Set.disjoint_left.2 fun e he ⟨u, _, v, hv, huv⟩ => hv (he v ?_)
    rw [huv]; exact Sym2.mem_mk_right u v
  · intro ω
    simp only [mem_ofPred_eq]
    refine forall_congr' fun y => forall_congr' fun hy => ?_
    rw [mem_localConn_iff_reachable hx hy, mem_localConn_iff_reachable hx hy]
    refine localConn_iff_of_agree C ⟨x, hx⟩ ⟨y, hy⟩ fun a ha b hb => ?_
    have : s(a, b) ∈ {e : Sym2 V | ∀ v ∈ e, v ∈ C} := by
      intro v hv
      rcases Sym2.mem_iff.1 hv with rfl | rfl
      · exact ha
      · exact hb
    simp [this]
  · intro ω
    simp only [mem_ofPred_eq, mem_inter_iff]
    refine forall_congr' fun u => forall_congr' fun hu => forall_congr' fun v =>
      forall_congr' fun hv => ?_
    simp only [not_and]
    exact ⟨fun h hm => absurd hm h, fun h hm => h hm ⟨u, hu, v, hv, rfl⟩⟩

/-- Internal connection to `x` in the `localConn` spelling is reachability from `x` in the
open graph induced on `C`. -/
theorem forall_mem_localConn_iff_forall_reachable {ω : Config V} {x : V} {C : Set V}
    (hx : x ∈ C) :
    (∀ y ∈ C, ω ∈ localConn C x y) ↔ ∀ y : C, ((openGraph ω).induce C).Reachable ⟨x, hx⟩ y :=
  ⟨fun h y => (mem_localConn_iff_reachable hx y.2 ω).1 (h y y.2),
    fun h y hy => (mem_localConn_iff_reachable hx hy ω).2 (h ⟨y, hy⟩)⟩

/-- The internal connection event `I_C` in the induced-graph spelling. -/
theorem setOf_forall_mem_localConn_eq_setOf_forall_reachable {x : V} {C : Set V} (hx : x ∈ C) :
    {ω : Config V | ∀ y ∈ C, ω ∈ localConn C x y} =
      {ω : Config V | ∀ y : C, ((openGraph ω).induce C).Reachable ⟨x, hx⟩ y} :=
  Set.ext fun _ => forall_mem_localConn_iff_forall_reachable hx

/-! ### Finite sets in the induced-graph spelling -/

/-- **The cluster of `x` is a finite set `C`** exactly when every vertex of `C` is joined to
`x` inside `C` and no pair leaving `C` is open. -/
theorem cluster_eq_finset_iff (ω : Config V) (x : V) (C : Finset V) (hx : x ∈ C) :
    cluster ω x = C ↔
      (∀ y : (C : Set V), ((openGraph ω).induce (C : Set V)).Reachable ⟨x, hx⟩ y) ∧
      ∀ y ∈ C, ∀ z ∉ C, s(y, z) ∉ ω :=
  (cluster_eq_iff_forall_localConn ω hx).trans
    (and_congr_left' (forall_mem_localConn_iff_forall_reachable hx))

/-- The internal connection event of a finite set is measurable. -/
theorem measurableSet_internally_connected [Countable V] (x : V) (C : Finset V) (hx : x ∈ C) :
    MeasurableSet {ω : Config V |
      ∀ y : (C : Set V), ((openGraph ω).induce (C : Set V)).Reachable ⟨x, hx⟩ y} := by
  rw [ofPred_forall]
  exact MeasurableSet.iInter fun y => measurableSet_setOf_reachable_induce (C : Set V) ⟨x, hx⟩ y

/-- The event that no pair leaving `C` is open is measurable. -/
theorem measurableSet_boundary_closed [Countable V] (C : Finset V) :
    MeasurableSet {ω : Config V | ∀ y ∈ C, ∀ z ∉ C, s(y, z) ∉ ω} :=
  measurableSet_setOf_boundary_closed (C : Set V)

/-- The event `{K_x = C}` is measurable. -/
theorem measurableSet_cluster_eq_finset [Countable V] (x : V) (C : Finset V) (hx : x ∈ C) :
    MeasurableSet {ω : Config V | cluster ω x = C} :=
  (setOf_cluster_eq_eq_inter (C := (C : Set V)) hx) ▸
    (measurableSet_setOf_forall_localConn x C.countable_toSet).inter
      (measurableSet_setOf_boundary_closed (C : Set V))

/-- **The law of a finite cluster.** `P(K_x = C)` is the probability that `C` is internally
connected to `x`, times the probability that every pair leaving `C` is closed. -/
theorem law_cluster_eq_finset [Countable V] (q : Sym2 V → unitInterval) (x : V) (C : Finset V)
    (hx : x ∈ C) :
    law q {ω | cluster ω x = C} =
      law q {ω : Config V |
        ∀ y : (C : Set V), ((openGraph ω).induce (C : Set V)).Reachable ⟨x, hx⟩ y} *
      law q {ω : Config V | ∀ y ∈ C, ∀ z ∉ C, s(y, z) ∉ ω} := by
  rw [law_cluster_eq_eq_mul q (C := (C : Set V)) hx,
    setOf_forall_mem_localConn_eq_setOf_forall_reachable hx]
  rfl

/-- `{K_x = C}` depends only on the pairs meeting `C`. -/
theorem cluster_eq_finset_determined (x : V) (C : Finset V) (hx : x ∈ C) (ω : Config V) :
    ω ∈ {ω : Config V | cluster ω x = C} ↔
      ω ∩ {e | ∃ v ∈ e, v ∈ C} ∈ {ω : Config V | cluster ω x = C} := by
  simp only [mem_ofPred_eq]
  rw [cluster_eq_finset_iff ω x C hx, cluster_eq_finset_iff _ x C hx]
  refine and_congr (forall_congr' fun y => localConn_iff_of_agree (C : Set V) ⟨x, hx⟩ y
    fun a ha b _ => ?_) (forall_congr' fun y => forall_congr' fun hy => forall_congr' fun z =>
      forall_congr' fun _ => ?_)
  · have : s(a, b) ∈ {e : Sym2 V | ∃ v ∈ e, v ∈ C} := ⟨a, Sym2.mem_mk_left a b, ha⟩
    simp [this]
  · have : s(y, z) ∈ {e : Sym2 V | ∃ v ∈ e, v ∈ C} := ⟨y, Sym2.mem_mk_left y z, hy⟩
    simp [this]

/-- **Domain Markov property.** `{K_x = C}` is independent of every measurable event
determined by the pairs with both endpoints outside `C`. -/
theorem law_cluster_eq_inter [Countable V] (q : Sym2 V → unitInterval) (x : V) (C : Finset V)
    (hx : x ∈ C) {B : Set (Config V)} (hB : MeasurableSet B)
    (hdet : ∀ ω ω', (∀ a ∉ C, ∀ b ∉ C, (s(a, b) ∈ ω ↔ s(a, b) ∈ ω')) → (ω ∈ B ↔ ω' ∈ B)) :
    law q ({ω | cluster ω x = C} ∩ B) = law q {ω | cluster ω x = C} * law q B := by
  refine PercLib.Probability.prodBernoulli_inter_of_determined_inter q {e | ∃ v ∈ e, v ∈ C}
      {e | ∀ v ∈ e, v ∉ C} ?_
    (measurableSet_cluster_eq_finset x C hx) hB (cluster_eq_finset_determined x C hx) ?_
  · exact Set.disjoint_left.2 fun e ⟨v, hv, hvC⟩ he => he v hv hvC
  · intro ω
    refine hdet _ _ fun a ha b hb => ?_
    have : s(a, b) ∈ {e : Sym2 V | ∀ v ∈ e, v ∉ C} := by
      intro v hv
      rcases Sym2.mem_iff.1 hv with rfl | rfl
      · exact ha
      · exact hb
    simp [this]

/-- **Corollary.** Off `C`, connections are independent of `{K_x = C}`. -/
theorem law_cluster_eq_inter_localConn_compl [Countable V] (q : Sym2 V → unitInterval) (x : V)
    (C : Finset V) (hx : x ∈ C) (y z : ((C : Set V)ᶜ : Set V)) :
    law q ({ω | cluster ω x = C} ∩
        {ω | ((openGraph ω).induce ((C : Set V)ᶜ)).Reachable y z}) =
      law q {ω | cluster ω x = C} *
        law q {ω | ((openGraph ω).induce ((C : Set V)ᶜ)).Reachable y z} :=
  law_cluster_eq_inter q x C hx (measurableSet_setOf_reachable_induce _ y z) fun _ _ h =>
    localConn_iff_of_agree _ y z fun a ha b hb => h a ha b hb

/-- Boundary pairs, indexed with their endpoint in `C` first, are distinct unordered pairs. -/
theorem injective_sym2_mk_boundary (C : Set V) :
    Function.Injective fun z : {z : V × V // z.1 ∈ C ∧ z.2 ∉ C} => s(z.1.1, z.1.2) := by
  rintro ⟨⟨a, b⟩, ha, hb⟩ ⟨⟨c, d⟩, hc, hd⟩ h
  rcases Sym2.eq_iff.1 h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact absurd ha hd

/-- **The closed-boundary probability** on a countable vertex type is the infinite product of
the closed probabilities of the boundary pairs, each indexed once with its endpoint in `C`
first. It may be zero. -/
theorem law_boundary_closed_eq_tprod [Countable V] (q : Sym2 V → unitInterval) (C : Set V) :
    law q {ω : Config V | ∀ u ∈ C, ∀ v ∉ C, s(u, v) ∉ ω} =
      ∏' z : {z : V × V // z.1 ∈ C ∧ z.2 ∉ C},
        (1 - (unitInterval.toNNReal (q s(z.1.1, z.1.2)) : ℝ≥0∞)) := by
  have hset : {ω : Config V | ∀ u ∈ C, ∀ v ∉ C, s(u, v) ∉ ω} =
      {ω | ∀ z : {z : V × V // z.1 ∈ C ∧ z.2 ∉ C}, s(z.1.1, z.1.2) ∉ ω} := by
    ext ω
    simp only [mem_ofPred_eq, Subtype.forall, Prod.forall]
    exact ⟨fun h u v huv => h u huv.1 v huv.2, fun h u hu v hv => h u v ⟨hu, hv⟩⟩
  rw [hset]
  exact (prodBernoulli_forall_notMem q _ (injective_sym2_mk_boundary C)).trans
    (tprod_congr fun z => coe_toNNReal_symm_eq_one_sub _)

/-! ### Non-vacuity -/

/-- `C = {x}`: the cluster of `x` is `{x}` with the probability that every pair at `x` is
closed. -/
example [Countable V] (q : Sym2 V → unitInterval) (x : V) :
    law q {ω | cluster ω x = (({x} : Finset V) : Set V)} =
      law q {ω : Config V | ∀ y ∈ ({x} : Finset V), ∀ z ∉ ({x} : Finset V), s(y, z) ∉ ω} := by
  rw [law_cluster_eq_finset q x {x} (Finset.mem_singleton_self x)]
  have : {ω : Config V | ∀ y : (({x} : Finset V) : Set V),
      ((openGraph ω).induce (({x} : Finset V) : Set V)).Reachable
        ⟨x, Finset.mem_singleton_self x⟩ y} = univ := by
    ext ω
    simp only [mem_ofPred_eq, mem_univ, iff_true]
    rintro ⟨y, hy⟩
    have : y = x := by simpa using hy
    subst this
    exact SimpleGraph.Reachable.refl _
  rw [this, measure_univ, one_mul]

end PercLib.Percolation.Bond
