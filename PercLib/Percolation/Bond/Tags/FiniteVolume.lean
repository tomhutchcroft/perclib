/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrappers for finite-window witnesses and cluster partitions.
All mathematical inputs come from the imported modules; no source proof is copied.
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Data.Finset.Sym
public import PercLib.Meta.Tag
public import PercLib.Percolation.Bond.ClusterPartition
public import PercLib.Percolation.Bond.ClusterTails
public import PercLib.Percolation.Bond.FiniteVolume
public import PercLib.Percolation.Bond.LocalConnectivity
public import PercLib.Percolation.Bond.Susceptibility
public import PercLib.Probability.DeterministicModification
public import PercLib.Probability.Transport.Pullback

/-!
# Finite volume: correspondence

Wiki correspondence for finite-window witnesses, local domains, finite-edge exhaustions and cluster
partitions.

## Main results

* `local_domain_restriction_and_exhaustion`
* `finite_window_tail_representation`
* `root_clusters_partition`
* `finite_root_component_sums`
* `finite_edge_exhaustion_limits`
* `escape_and_order_of_volume_limits`
-/

@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace PercLib.Percolation.Bond
variable {V : Type*}

/-- The complete local-domain restriction assertion. Probability convergence is
for an arbitrary measure, not just an independent bond law. Countability is
required only for measurability, and finiteness only for the cylinder clause. -/
@[tag "7BMQ"]
theorem local_domain_restriction_and_exhaustion (S : Set V)
    (T : ℕ → Set V) (hT : Monotone T) (hcover : ∀ v, ∃ n, v ∈ T n) :
    Measurable (fun ω : Config V => Sym2.map (Subtype.val : S → V) ⁻¹' ω) ∧
    (∀ ω, (openGraph ω).induce S =
      openGraph (Sym2.map (Subtype.val : S → V) ⁻¹' ω)) ∧
    (∀ (_ : Countable S) (x y : S),
      MeasurableSet {ω : Config V | ((openGraph ω).induce S).Reachable x y}) ∧
    (∀ (_ : Finite S), ∃ F : Finset (Sym2 V), (F : Set (Sym2 V)) = S.sym2 ∧
      ∀ (x y : S) (ω ω' : Config V),
        (∀ e ∈ F, e ∈ ω ↔ e ∈ ω') →
        (((openGraph ω).induce S).Reachable x y ↔
          ((openGraph ω').induce S).Reachable x y)) ∧
    (∀ q : Sym2 V → unitInterval,
      (law q).map (fun ω => Sym2.map (Subtype.val : S → V) ⁻¹' ω) =
        law (q ∘ Sym2.map (Subtype.val : S → V))) ∧
    (∀ (x y : S) (ω ω' : Config V),
      (∀ a ∈ S, ∀ b ∈ S, s(a,b) ∈ ω ↔ s(a,b) ∈ ω') →
        (((openGraph ω).induce S).Reachable x y ↔
          ((openGraph ω').induce S).Reachable x y)) ∧
    (∀ (x y : S) (ω ω' : Config V), ω ⊆ ω' →
      ((openGraph ω).induce S).Reachable x y →
        ((openGraph ω').induce S).Reachable x y) ∧
    (∀ (ω : Config V) (U : Set V) (hSU : S ⊆ U) (x y : S),
      ((openGraph ω).induce S).Reachable x y →
        ((openGraph ω).induce U).Reachable (Set.inclusion hSU x) (Set.inclusion hSU y)) ∧
    (∀ (ω : Config V) (x y : S), ((openGraph ω).induce S).Reachable x y →
      ω ∈ conn (x : V) (y : V)) ∧
    (∀ (ω : Config V) (x y : V), ω ∈ conn x y ↔
      ∃ F : Finset V, ω ∈ localConn (F : Set V) x y) ∧
    (∀ x y : V,
      Monotone (fun n => localConn (T n) x y) ∧
      (conn x y : Set (Config V)) = ⋃ n, localConn (T n) x y) ∧
    (∀ (_ : ∀ n, Countable (T n)) (x y : V),
      (∀ n, MeasurableSet (localConn (T n) x y)) ∧
      MeasurableSet (conn x y : Set (Config V))) ∧
    (∀ (μ : Measure (Config V)) (x y : V),
      Monotone (fun n => μ (localConn (T n) x y)) ∧
      Filter.Tendsto (fun n => μ (localConn (T n) x y))
        Filter.atTop (nhds (μ (conn x y)))) := by
  refine ⟨measurable_restrict_pairs S, fun ω => openGraph_induce ω S,
    fun _ x y => measurableSet_setOf_reachable_induce S x y, ?_, ?_,
    fun x y _ _ h => localConn_iff_of_agree S x y h,
    fun x y _ _ h hc => localConn_mono_config S x y h hc,
    fun ω _ h x y hc => localConn_mono_domain ω h x y hc,
    fun ω x y hc => conn_of_localConn ω S x y hc,
    fun ω x y => conn_iff_exists_finset_localConn ω x y,
    fun x y => ⟨monotone_localConn hT x y, conn_eq_iUnion_localConn hT hcover x y⟩,
    ?_, ?_⟩
  · intro hS
    have hs : S.sym2.Finite := by
      rw [Set.sym2_eq_mk_image]
      exact ((Set.toFinite S).prod (Set.toFinite S)).image _
    refine ⟨hs.toFinset, hs.coe_toFinset, ?_⟩
    intro x y ω ω' h
    apply localConn_iff_of_agree S x y
    intro a ha b hb
    exact h s(a,b) (hs.mem_toFinset.mpr ⟨ha, hb⟩)
  · intro q
    exact PercLib.Probability.prodBernoulli_map_preimage q
      (Sym2.map.injective Subtype.val_injective)
  · intro hcount x y
    have hm (n : ℕ) : MeasurableSet (localConn (T n) x y) := by
      let : Countable (T n) := hcount n
      exact measurableSet_localConn (T n) x y
    refine ⟨hm, ?_⟩
    rw [conn_eq_iUnion_localConn hT hcover]
    exact MeasurableSet.iUnion hm
  · intro μ x y
    refine ⟨fun _ _ h => measure_mono (monotone_localConn hT x y h), ?_⟩
    have h := tendsto_measure_iUnion_atTop (μ := μ) (monotone_localConn hT x y)
    simpa only [← conn_eq_iUnion_localConn hT hcover x y, Function.comp_def] using h

-- Countable local domains remain measurable in an uncountable ambient space.
example : MeasurableSet {ω : Config ℝ |
    ((openGraph ω).induce ({0} : Set ℝ)).Reachable ⟨0, by simp⟩ ⟨0, by simp⟩} := by
  have h := local_domain_restriction_and_exhaustion ({0} : Set ℝ)
    (fun _ => univ) (fun _ _ _ => subset_rfl) (fun _ => ⟨0, mem_univ _⟩)
  exact h.2.2.1 inferInstance ⟨0, by simp⟩ ⟨0, by simp⟩

-- A genuinely growing exhaustion works for every configuration measure, with no
-- independence hypothesis and with early domains allowed to omit either endpoint.
example (μ : Measure (Config ℕ)) (x y : ℕ) :
    Filter.Tendsto (fun n => μ (localConn (Iic n) x y))
        Filter.atTop (nhds (μ (conn x y))) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, h⟩ :=
    local_domain_restriction_and_exhaustion (∅ : Set ℕ) (fun n => Iic n)
      (fun _ _ h => Iic_subset_Iic.mpr h) (fun v => ⟨v, mem_Iic.mpr le_rfl⟩)
  exact (h μ x y).2

/-- The simple open graph discards loops, connections grow with the configuration,
and the root always contributes one, even with arbitrary diagonal coordinates. -/
@[tag "Q0D1"]
theorem open_graph_and_singleton_conventions :
    (∀ (ω : Config V) x y, (openGraph ω).Adj x y ↔ s(x,y) ∈ ω ∧ x ≠ y) ∧
    (∀ (ω ω' : Config V), ω ⊆ ω' →
      openGraph ω ≤ openGraph ω' ∧
      (∀ x y, ω ∈ conn x y → ω' ∈ conn x y) ∧
      ∀ x, cluster ω x ⊆ cluster ω' x) ∧
    (∀ (ω : Config V) x, x ∈ cluster ω x ∧ 1 ≤ (cluster ω x).encard) ∧
    (∀ (ω : Config V), (∀ x y, x ≠ y → s(x,y) ∉ ω) →
      ∀ x, cluster ω x = {x}) ∧
    (∀ (ω : Config V) x y, x ≠ y → s(x,y) ∈ ω → ω ∈ conn x y) ∧
    (∀ (μ : Measure (Config V)) [IsProbabilityMeasure μ] (x y : V),
      connProb μ x x = 1 ∧ connProb μ x y = connProb μ y x ∧ 0 ≤ connProb μ x y ∧
        connProb μ x y ≤ 1) := by
  refine ⟨openGraph_adj_iff, ?_, fun ω x =>
    ⟨mem_cluster_self ω x, one_le_encard_cluster ω x⟩, ?_,
    fun _ _ _ hxy h => mem_conn_of_mem hxy h,
    fun μ _ x y => ⟨connProb_self μ x, connProb_comm μ x y, zero_le, connProb_le_one μ x y⟩⟩
  · intro ω ω' h
    exact ⟨openGraph_mono h, fun _ _ hc => conn_mono h hc,
      fun _ _ hc => conn_mono h hc⟩
  · intro ω h x
    have hg : openGraph ω = ⊥ := by
      apply le_antisymm _ bot_le
      intro a b hab
      obtain ⟨he, hne⟩ := (openGraph_adj_iff ω a b).mp hab
      exact (h a b hne he).elim
    ext y
    simp only [cluster, hg, mem_ofPred_eq, SimpleGraph.reachable_bot,
      mem_singleton_iff, eq_comm]

/-- Finite-window tails: the event identity, monotonicity, open witnesses,
endpoint cases, and measurability precisely when countability is supplied. -/
@[tag "FD69"]
theorem finite_window_tail_representation (x : V) (Λ : Finset V) (k : ℕ) :
    ({ω : Config V | k ≤ (cluster ω x ∩ (Λ : Set V)).ncard} =
      ⋃ S ∈ {S : Finset V | S ⊆ Λ ∧ S.card = k}, ⋂ y ∈ S, conn x y) ∧
    IsUpperSet {ω : Config V | k ≤ (cluster ω x ∩ (Λ : Set V)).ncard} ∧
    (∀ ω : Config V, k ≤ (cluster ω x ∩ (Λ : Set V)).ncard →
      ∃ F : Finset (Sym2 V), (F : Config V) ⊆ ω ∧
        k ≤ (cluster (F : Config V) x ∩ (Λ : Set V)).ncard) ∧
    ({ω : Config V | 0 ≤ (cluster ω x ∩ (Λ : Set V)).ncard} = univ) ∧
    (Λ.card < k → {ω : Config V | k ≤ (cluster ω x ∩ (Λ : Set V)).ncard} = ∅) ∧
    (∀ (_ : Countable V),
      MeasurableSet {ω : Config V | k ≤ (cluster ω x ∩ (Λ : Set V)).ncard}) :=
  ⟨cluster_tail_eq_iUnion x Λ k, isUpperSet_cluster_tail x Λ k,
    fun _ h => exists_finset_of_cluster_tail x Λ k h, cluster_tail_zero x Λ,
    cluster_tail_gt_card x Λ k, fun _ => measurableSet_cluster_tail x Λ k⟩

/-- Simultaneous connections and finite-window tails have finite open certificates.
Countability is needed only for the measurable-event conclusions. -/
@[tag "F0I9"]
theorem finite_connection_and_tail_witnesses (x : V) (S Λ : Finset V) (k : ℕ) :
    (∀ ω : Config V, (∀ y ∈ S, ω ∈ conn x y) →
      ∃ F : Finset (Sym2 V), (F : Config V) ⊆ ω ∧
        ∀ y ∈ S, (F : Config V) ∈ conn x y) ∧
    (∀ ω : Config V, k ≤ (cluster ω x ∩ (Λ : Set V)).ncard →
      ∃ F : Finset (Sym2 V), (F : Config V) ⊆ ω ∧
        k ≤ (cluster (F : Config V) x ∩ (Λ : Set V)).ncard) ∧
    IsUpperSet (⋂ y ∈ S, conn x y) ∧
    IsUpperSet {ω : Config V | k ≤ (cluster ω x ∩ (Λ : Set V)).ncard} ∧
    (∀ (_ : Countable V), MeasurableSet (⋂ y ∈ S, conn x y) ∧
      MeasurableSet {ω : Config V | k ≤ (cluster ω x ∩ (Λ : Set V)).ncard}) := by
  refine ⟨fun _ h => exists_finset_of_forall_conn x S h,
    fun _ h => exists_finset_of_cluster_tail x Λ k h, ?_,
    isUpperSet_cluster_tail x Λ k, ?_⟩
  · intro ω ω' h hω
    simp only [mem_iInter] at hω ⊢
    exact fun y hy => conn_mono h (hω y hy)
  · intro hV
    exact ⟨MeasurableSet.iInter fun y => MeasurableSet.iInter fun _ =>
      measurableSet_conn x y, measurableSet_cluster_tail x Λ k⟩

/-- Equality and disjointness of root clusters, together with coverage of the
whole vertex set, without countability or probability assumptions. -/
@[tag "0N0J"]
theorem root_clusters_partition (ω : Config V) :
    (∀ x y, cluster ω x = cluster ω y ↔ ω ∈ conn x y) ∧
    (∀ x y, cluster ω x = cluster ω y ∨ Disjoint (cluster ω x) (cluster ω y)) ∧
    (⋃ x, cluster ω x) = univ := by
  refine ⟨cluster_eq_iff_conn ω, cluster_eq_or_disjoint ω, ?_⟩
  exact eq_univ_of_forall fun x => mem_iUnion.mpr ⟨x, mem_cluster_self ω x⟩

/-- Both finite component-sum identities, including their internal-domain versions.
The sums are finite even though they are written as `tsum`. -/
@[tag "TUD2"]
theorem finite_root_component_sums (ω : Config V) :
    (∀ (_ : Finite V),
      (∀ f : ℕ → ℝ, ∑' x, f (cluster ω x).ncard =
        ∑' C : (openGraph ω).ConnectedComponent, (C.supp.ncard : ℝ) * f C.supp.ncard) ∧
      (∑' x, (cluster ω x).ncard =
        ∑' C : (openGraph ω).ConnectedComponent, C.supp.ncard ^ 2)) ∧
    (∀ (Λ : Set V) (_ : Finite Λ),
      (∀ f : ℕ → ℝ,
        ∑' x : Λ, f {y : Λ | ((openGraph ω).induce Λ).Reachable x y}.ncard =
          ∑' C : ((openGraph ω).induce Λ).ConnectedComponent,
            (C.supp.ncard : ℝ) * f C.supp.ncard) ∧
      (∑' x : Λ, {y : Λ | ((openGraph ω).induce Λ).Reachable x y}.ncard =
        ∑' C : ((openGraph ω).induce Λ).ConnectedComponent, C.supp.ncard ^ 2)) := by
  refine ⟨fun _ => ⟨tsum_cluster_real_function ω,
    tsum_cluster_ncard_eq_tsum_component_sq ω⟩, ?_⟩
  intro Λ hΛ
  refine ⟨?_, tsum_internal_cluster_ncard ω Λ⟩
  intro f
  have h := tsum_cluster_real_function ((openGraph ω).induce Λ).edgeSet f
  unfold cluster at h
  rw [show openGraph ((openGraph ω).induce Λ).edgeSet = (openGraph ω).induce Λ from
    SimpleGraph.fromEdgeSet_edgeSet _] at h
  exact h

/-- Measurable cluster sets and extended volumes on countable vertex types, bundled
with the indicator-sum identity on arbitrary vertex types. -/
@[tag "GUHT"]
theorem cluster_measurability_and_indicator_sum (x : V) :
    (∀ (_ : Countable V), Measurable (fun ω : Config V => cluster ω x) ∧
      Measurable (fun ω : Config V => (cluster ω x).encard)) ∧
    (∀ ω : Config V, ((cluster ω x).encard : ℝ≥0∞) =
      ∑' y, (conn x y).indicator (fun _ => (1 : ℝ≥0∞)) ω) :=
  ⟨fun _ => ⟨measurable_cluster x, measurable_encard_cluster x⟩,
    fun ω => encard_cluster_eq_tsum ω x⟩

-- The deterministic clauses remain available even on an uncountable vertex type.
example (ω : Config ℝ) :
    (⋃ x, cluster ω x) = univ := (root_clusters_partition ω).2.2

-- The empty window at threshold zero is included.
example : {ω : Config Bool | 0 ≤ (cluster ω false ∩ ((∅ : Finset Bool) : Set Bool)).ncard}
    = univ := (finite_window_tail_representation false ∅ 0).2.2.2.1

-- An actually open two-vertex connection has a finite witness.
example : ∃ F : Finset (Sym2 Bool), (F : Config Bool) ⊆ {s(false, true)} ∧
    ∀ y ∈ ({true} : Finset Bool), (F : Config Bool) ∈ conn false y := by
  apply (finite_connection_and_tail_witnesses false {true} ∅ 0).1
  intro y hy
  have hy' : y = true := by simpa using hy
  subst y
  exact mem_conn_of_mem (by decide) (by simp)

-- Empty finite vertex types and finite internal domains are not excluded.
example : ∑' x : Empty, (cluster (∅ : Config Empty) x).ncard =
    ∑' C : (openGraph (∅ : Config Empty)).ConnectedComponent, C.supp.ncard ^ 2 :=
  ((finite_root_component_sums (∅ : Config Empty)).1 inferInstance).2

open Classical in
private theorem finite_cluster_of_finite_edges (ω : Config V) (E : Finset (Sym2 V)) (x : V) :
    (cluster (ω ∩ (E : Set (Sym2 V))) x).Finite := by
  apply ((E.biUnion Sym2.toFinset).finite_toSet.insert x).subset
  intro y hy
  change (openGraph (ω ∩ (E : Set (Sym2 V)))).Reachable x y at hy
  rw [SimpleGraph.reachable_iff_reflTransGen] at hy
  induction hy with
  | refl => exact mem_insert x _
  | @tail y z _ hyz _ =>
    have he := (openGraph_adj_iff _ y z).mp hyz
    exact mem_insert_of_mem _ (Finset.mem_biUnion.mpr ⟨s(y,z), he.1.2, by simp⟩)

/-- Finite-edge restrictions retain the ambient vertex type and its root, but
have finite clusters. A finite vertex domain retains exactly its internal pairs;
its cluster is contained in the full cluster intersected with the domain. -/
@[tag "U32Y"]
theorem finite_edge_restrictions_and_clusters (ω : Config V) :
    (∀ (E : Finset (Sym2 V)) x,
      cluster (ω ∩ (E : Set (Sym2 V))) x =
        {y | (openGraph (ω ∩ (E : Set (Sym2 V)))).Reachable x y} ∧
      (cluster (ω ∩ (E : Set (Sym2 V))) x).Finite ∧
      x ∈ cluster (ω ∩ (E : Set (Sym2 V))) x) ∧
    (∀ (Λ : Finset V), (Λ.sym2 : Set (Sym2 V)) = {e | ∀ v ∈ e, v ∈ Λ}) ∧
    (∀ (Λ : Finset V) (x : V), x ∈ Λ →
      cluster (ω ∩ (Λ.sym2 : Set (Sym2 V))) x ⊆ cluster ω x ∩ (Λ : Set V)) := by
  refine ⟨fun E x => ⟨rfl, finite_cluster_of_finite_edges ω E x, mem_cluster_self _ x⟩,
    fun Λ => Set.ext (fun e => Finset.mem_sym2_iff), ?_⟩
  intro Λ x hx y hy
  refine ⟨conn_mono inter_subset_left hy, ?_⟩
  change (openGraph (ω ∩ (Λ.sym2 : Set (Sym2 V)))).Reachable x y at hy
  rw [SimpleGraph.reachable_iff_reflTransGen] at hy
  induction hy with
  | refl => exact hx
  | @tail y z _ hyz _ =>
    exact (Finset.mk_mem_sym2_iff.mp ((openGraph_adj_iff _ y z).mp hyz).1.2).2

private theorem conn_iff_exists_edge_restriction {E : ℕ → Finset (Sym2 V)}
    (hE : Monotone E) (hcover : ∀ e, ¬ e.IsDiag → ∃ n, e ∈ E n)
    (ω : Config V) (x y : V) :
    ω ∈ conn x y ↔ ∃ n, ω ∩ (E n : Set (Sym2 V)) ∈ conn x y := by
  constructor
  · intro h
    change (openGraph ω).Reachable x y at h
    rw [SimpleGraph.reachable_iff_reflTransGen] at h
    induction h with
    | refl => exact ⟨0, mem_cluster_self _ _⟩
    | @tail y z _ hyz ih =>
      obtain ⟨n, hn⟩ := ih
      obtain ⟨he, hne⟩ := (openGraph_adj_iff ω y z).mp hyz
      obtain ⟨m, hm⟩ := hcover s(y,z) (by simpa using hne)
      refine ⟨max n m, ?_⟩
      have hxy := conn_mono (inter_subset_inter_right _ (hE (Nat.le_max_left n m))) hn
      have hyz' := mem_conn_of_mem hne
        (show s(y,z) ∈ ω ∩ (E (max n m) : Set (Sym2 V)) from
          ⟨he, hE (Nat.le_max_right n m) hm⟩)
      exact hxy.trans hyz'
  · rintro ⟨n, hn⟩
    exact conn_mono inter_subset_left hn

private theorem edge_cluster_union {E : ℕ → Finset (Sym2 V)}
    (hE : Monotone E) (hcover : ∀ e, ¬ e.IsDiag → ∃ n, e ∈ E n)
    (ω : Config V) (x : V) :
    (⋃ n, cluster (ω ∩ (E n : Set (Sym2 V))) x) = cluster ω x := by
  ext y
  exact (mem_iUnion.trans (conn_iff_exists_edge_restriction hE hcover ω x y).symm)

private theorem nat_le_encard_union {K : ℕ → Set V} (hK : Monotone K) (k : ℕ) :
    (k : ℕ∞) ≤ (⋃ n, K n).encard ↔ ∃ n, (k : ℕ∞) ≤ (K n).encard := by
  constructor
  · intro h
    obtain ⟨t, ht, hk⟩ := exists_subset_encard_eq h
    have hf : t.Finite := finite_of_encard_eq_coe hk
    obtain ⟨n, hn⟩ := hK.directed_le.exists_mem_subset_of_finset_subset_biUnion
      (s := hf.toFinset) (by simpa using ht)
    exact ⟨n, hk ▸ encard_le_encard (by simpa using hn)⟩
  · rintro ⟨n, hn⟩
    exact hn.trans (encard_le_encard (subset_iUnion K n))

-- The empty finite edge set still retains the root on an infinite vertex type.
example (ω : Config ℕ) (x : ℕ) :
    (cluster (ω ∩ (∅ : Set (Sym2 ℕ))) x).Finite ∧
      x ∈ cluster (ω ∩ (∅ : Set (Sym2 ℕ))) x := by
  simpa only [Finset.coe_empty] using ((finite_edge_restrictions_and_clusters ω).1 ∅ x).2

-- On the path 0--1--2, deleting the exterior vertex 1 destroys the connection
-- between the two observed vertices, although both lie in the full cluster.
example : ∃ (ω : Config (Fin 3)) (Λ : Finset (Fin 3)),
    (0 : Fin 3) ∈ Λ ∧
    cluster (ω ∩ (Λ.sym2 : Set (Sym2 (Fin 3)))) 0 = {0} ∧
    cluster ω 0 ∩ (Λ : Set (Fin 3)) = {0,2} := by
  let ω : Config (Fin 3) := {s(0,1), s(1,2)}
  let Λ : Finset (Fin 3) := {0,2}
  have he : ω ∩ (Λ.sym2 : Set (Sym2 (Fin 3))) = ∅ := by
    ext e
    induction e using Sym2.ind with
    | h a b =>
      fin_cases a <;> fin_cases b <;> simp [ω, Λ]
  refine ⟨ω, Λ, by simp [Λ], by rw [he, cluster_empty], ?_⟩
  apply le_antisymm
  · simp [Λ]
  · intro y hy
    rcases hy with rfl | hy
    · exact ⟨mem_cluster_self _ _, by simp [Λ]⟩
    · have hy' : y = 2 := hy
      subst y
      refine ⟨?_, by simp [Λ]⟩
      exact (mem_conn_of_mem (by decide : (0 : Fin 3) ≠ 1) (by simp [ω])).trans
        (mem_conn_of_mem (by decide : (1 : Fin 3) ≠ 2) (by simp [ω]))

private theorem edge_cluster_mono {E : ℕ → Finset (Sym2 V)} (hE : Monotone E)
    (ω : Config V) (x : V) : Monotone (fun n => cluster (ω ∩ (E n : Set (Sym2 V))) x) :=
  fun _ _ h => cluster_mono (inter_subset_inter_right _ (hE h)) x

private theorem edge_tail_union {E : ℕ → Finset (Sym2 V)}
    (hE : Monotone E) (hcover : ∀ e, ¬ e.IsDiag → ∃ n, e ∈ E n)
    (x : V) (T : Set V) (k : ℕ) :
    {ω : Config V | (k : ℕ∞) ≤ (cluster ω x ∩ T).encard} =
      ⋃ n, {ω : Config V | (k : ℕ∞) ≤
        (cluster (ω ∩ (E n : Set (Sym2 V))) x ∩ T).encard} := by
  ext ω
  simp only [mem_ofPred_eq, mem_iUnion]
  rw [← edge_cluster_union hE hcover ω x, iUnion_inter]
  exact nat_le_encard_union (fun _ _ h =>
    inter_subset_inter_left T (edge_cluster_mono hE ω x h)) k

private theorem edge_tail_mono {E : ℕ → Finset (Sym2 V)} (hE : Monotone E)
    (x : V) (T : Set V) (k : ℕ) :
    Monotone (fun n => {ω : Config V | (k : ℕ∞) ≤
      (cluster (ω ∩ (E n : Set (Sym2 V))) x ∩ T).encard}) := by
  intro n m h ω hω
  exact hω.trans (encard_le_encard (inter_subset_inter_left T (edge_cluster_mono hE ω x h)))

private theorem edge_tail_convergence (μ : Measure (Config V))
    {E : ℕ → Finset (Sym2 V)} (hE : Monotone E)
    (hcover : ∀ e, ¬ e.IsDiag → ∃ n, e ∈ E n) (x : V) (T : Set V) (k : ℕ) :
    Monotone (fun n => μ {ω : Config V | (k : ℕ∞) ≤
      (cluster (ω ∩ (E n : Set (Sym2 V))) x ∩ T).encard}) ∧
    Filter.Tendsto (fun n => μ {ω : Config V | (k : ℕ∞) ≤
      (cluster (ω ∩ (E n : Set (Sym2 V))) x ∩ T).encard}) Filter.atTop
        (nhds (μ {ω : Config V | (k : ℕ∞) ≤ (cluster ω x ∩ T).encard})) := by
  refine ⟨fun _ _ h => measure_mono (edge_tail_mono hE x T k h), ?_⟩
  simpa only [← edge_tail_union hE hcover x T k, Function.comp_def] using
    tendsto_measure_iUnion_atTop (μ := μ) (edge_tail_mono hE x T k)

open Classical in
/-- Finite-edge exhaustions recover clusters, full and observed volume tails,
and expected extended cluster volumes under any measure. The product-law clause
is a pushforward identity, not conditioning on exterior coordinates. -/
@[tag "SFLE"]
theorem finite_edge_exhaustion_limits [Countable V] (μ : Measure (Config V))
    (E : ℕ → Finset (Sym2 V)) (hE : Monotone E)
    (hcover : ∀ e, ¬ e.IsDiag → ∃ n, e ∈ E n) (x : V) :
    (∀ ω, Monotone (fun n => cluster (ω ∩ (E n : Set (Sym2 V))) x) ∧
      (⋃ n, cluster (ω ∩ (E n : Set (Sym2 V))) x) = cluster ω x) ∧
    (∀ (T : Set V) (k : ℕ),
      Monotone (fun n => μ {ω : Config V | (k : ℕ∞) ≤
        (cluster (ω ∩ (E n : Set (Sym2 V))) x ∩ T).encard}) ∧
      Filter.Tendsto (fun n => μ {ω : Config V | (k : ℕ∞) ≤
        (cluster (ω ∩ (E n : Set (Sym2 V))) x ∩ T).encard}) Filter.atTop
          (nhds (μ {ω : Config V | (k : ℕ∞) ≤ (cluster ω x ∩ T).encard}))) ∧
    (Monotone (fun n => ∫⁻ ω, ((cluster (ω ∩ (E n : Set (Sym2 V))) x).encard : ℝ≥0∞) ∂μ)) ∧
    (Filter.Tendsto (fun n => ∫⁻ ω, ((cluster (ω ∩ (E n : Set (Sym2 V))) x).encard : ℝ≥0∞) ∂μ)
      Filter.atTop (nhds (∫⁻ ω, ((cluster ω x).encard : ℝ≥0∞) ∂μ))) ∧
    (∀ y, Filter.Tendsto (fun n => μ {ω : Config V | ω ∩ (E n : Set (Sym2 V)) ∈ conn x y})
      Filter.atTop (nhds (μ (conn x y)))) ∧
    (∀ (q : Sym2 V → unitInterval) n,
      (law q).map (fun ω => ω ∩ (E n : Set (Sym2 V))) =
        law (fun e => if e ∈ E n then q e else 0)) ∧
    (∀ (Λ : Finset V) (k : ℕ),
      Monotone (fun n => μ {ω : Config V | k ≤
        (cluster (ω ∩ (E n : Set (Sym2 V))) x ∩ (Λ : Set V)).ncard}) ∧
      Filter.Tendsto (fun n => μ {ω : Config V | k ≤
        (cluster (ω ∩ (E n : Set (Sym2 V))) x ∩ (Λ : Set V)).ncard}) Filter.atTop
          (nhds (μ {ω : Config V | k ≤ (cluster ω x ∩ (Λ : Set V)).ncard}))) := by
  have hm (n : ℕ) : Measurable (fun ω : Config V =>
      ((cluster (ω ∩ (E n : Set (Sym2 V))) x).encard : ℝ≥0∞)) :=
    (measurable_of_countable (fun a : ℕ∞ => (a : ℝ≥0∞))).comp
      ((measurable_encard_cluster x).comp (by fun_prop))
  have hmono : Monotone (fun n ω =>
      ((cluster (ω ∩ (E n : Set (Sym2 V))) x).encard : ℝ≥0∞)) :=
    fun _ _ h ω => ENat.toENNReal_le.mpr (encard_le_encard (edge_cluster_mono hE ω x h))
  have he (ω : Config V) : ((cluster ω x).encard : ℝ≥0∞) =
      ⨆ n, ((cluster (ω ∩ (E n : Set (Sym2 V))) x).encard : ℝ≥0∞) := by
    rw [← edge_cluster_union hE hcover ω x, encard_iUnion_of_monotone (edge_cluster_mono hE ω x),
      ENat.toENNReal_iSup]
  refine ⟨fun ω => ⟨edge_cluster_mono hE ω x, edge_cluster_union hE hcover ω x⟩,
    edge_tail_convergence μ hE hcover x,
    fun _ _ h => lintegral_mono (hmono h), ?_, ?_, ?_, ?_⟩
  · apply lintegral_tendsto_of_tendsto_of_monotone (fun n => (hm n).aemeasurable)
      (Filter.Eventually.of_forall (fun ω => fun _ _ h => hmono h ω))
    apply Filter.Eventually.of_forall
    intro ω
    rw [he]
    exact tendsto_atTop_iSup (fun _ _ h => hmono h ω)
  · intro y
    have hmono' : Monotone (fun n => {ω : Config V | ω ∩ (E n : Set (Sym2 V)) ∈ conn x y}) :=
      fun _ _ h _ hω => conn_mono (inter_subset_inter_right _ (hE h)) hω
    have hu : (⋃ n, {ω : Config V | ω ∩ (E n : Set (Sym2 V)) ∈ conn x y}) = conn x y := by
      ext ω
      exact mem_iUnion.trans (conn_iff_exists_edge_restriction hE hcover ω x y).symm
    simpa only [hu, Function.comp_def] using tendsto_measure_iUnion_atTop (μ := μ) hmono'
  · intro q n
    exact PercLib.Probability.prodBernoulli_map_inter q (E n : Set (Sym2 V))
  · intro Λ k
    have hc (r : Config V) : (k : ℕ∞) ≤ (cluster r x ∩ (Λ : Set V)).encard ↔
        k ≤ (cluster r x ∩ (Λ : Set V)).ncard := by
      rw [← (Λ.finite_toSet.subset (inter_subset_right (s := cluster r x))).cast_ncard_eq]
      exact_mod_cast Iff.rfl
    simpa only [hc] using edge_tail_convergence μ hE hcover x (Λ : Set V) k

private theorem infinite_event_as_tails (C : Config V → Set V) :
    {ω | (C ω).Infinite} = ⋂ k : ℕ, {ω | (k : ℕ∞) ≤ (C ω).encard} := by
  ext ω
  simp only [mem_ofPred_eq, mem_iInter, ← encard_eq_top_iff]
  rw [← top_le_iff, ← ENat.iSup_natCast, iSup_le_iff]

private theorem antitone_volume_tails (C : Config V → Set V) :
    Antitone (fun k : ℕ => {ω | (k : ℕ∞) ≤ (C ω).encard}) := by
  intro k l h ω hω
  exact (by exact_mod_cast h : (k : ℕ∞) ≤ l).trans hω

private theorem volume_tail_limit [Countable V] (μ : Measure (Config V)) [IsFiniteMeasure μ]
    (r : Config V → Config V) (hr : Measurable r) (x : V) :
    Filter.Tendsto (fun k : ℕ => μ {ω | (k : ℕ∞) ≤ (cluster (r ω) x).encard})
      Filter.atTop (nhds (μ {ω | (cluster (r ω) x).Infinite})) := by
  have hm (k : ℕ) : MeasurableSet {ω | (k : ℕ∞) ≤ (cluster (r ω) x).encard} :=
    (Set.to_countable {a : ℕ∞ | (k : ℕ∞) ≤ a}).measurableSet.preimage
      ((measurable_encard_cluster x).comp hr)
  simpa only [← infinite_event_as_tails, Function.comp_def] using
    tendsto_measure_iInter_atTop (μ := μ) (fun k => (hm k).nullMeasurableSet)
      (antitone_volume_tails (fun ω => cluster (r ω) x)) ⟨0, measure_ne_top _ _⟩

/-- Escapes decrease to the infinite-cluster event. For finite-edge restrictions,
taking the edge limit before the volume threshold gives the infinite-cluster
probability; reversing those limits gives zero. No independence is required. -/
@[tag "B12T"]
theorem escape_and_order_of_volume_limits [Countable V]
    (μ : Measure (Config V)) [IsProbabilityMeasure μ]
    (E : ℕ → Finset (Sym2 V)) (hE : Monotone E)
    (hcover : ∀ e, ¬ e.IsDiag → ∃ n, e ∈ E n)
    (Λ : ℕ → Finset V) (hΛ : Monotone Λ) (hvertices : ∀ v, ∃ m, v ∈ Λ m) (x : V) :
    {ω : Config V | (cluster ω x).Infinite} =
      ⋂ m, {ω | ¬ cluster ω x ⊆ (Λ m : Set V)} ∧
    Filter.Tendsto (fun m => μ {ω | ¬ cluster ω x ⊆ (Λ m : Set V)}) Filter.atTop
      (nhds (μ {ω | (cluster ω x).Infinite})) ∧
    (∀ k : ℕ, Filter.Tendsto (fun n => μ {ω | (k : ℕ∞) ≤
        (cluster (ω ∩ (E n : Set (Sym2 V))) x).encard}) Filter.atTop
      (nhds (μ {ω | (k : ℕ∞) ≤ (cluster ω x).encard}))) ∧
    Filter.Tendsto (fun k : ℕ => ⨆ n, μ {ω | (k : ℕ∞) ≤
      (cluster (ω ∩ (E n : Set (Sym2 V))) x).encard}) Filter.atTop
      (nhds (μ {ω | (cluster ω x).Infinite})) ∧
    (∀ n, Filter.Tendsto (fun k : ℕ => μ {ω | (k : ℕ∞) ≤
      (cluster (ω ∩ (E n : Set (Sym2 V))) x).encard}) Filter.atTop (nhds 0)) ∧
    Filter.Tendsto (fun n => ⨅ k : ℕ, μ {ω | (k : ℕ∞) ≤
      (cluster (ω ∩ (E n : Set (Sym2 V))) x).encard}) Filter.atTop (nhds 0) := by
  have hescape (T : Set V) : {ω : Config V | ¬ cluster ω x ⊆ T} =
      ⋃ y ∈ Tᶜ, conn x y := by
    ext ω
    simp only [mem_ofPred_eq, subset_def, not_forall, mem_iUnion, mem_compl_iff, cluster]
    tauto
  have hid : {ω : Config V | (cluster ω x).Infinite} =
      ⋂ m, {ω | ¬ cluster ω x ⊆ (Λ m : Set V)} := by
    simp_rw [hescape]
    exact cluster_infinite_eq_iInter_escape (fun _ _ h => hΛ h)
      (fun m => (Λ m).finite_toSet) hvertices x
  have hanti : Antitone (fun m => {ω : Config V | ¬ cluster ω x ⊆ (Λ m : Set V)}) := by
    intro m n h ω hω hs
    exact hω (hs.trans (hΛ h))
  have hem (m : ℕ) : MeasurableSet {ω : Config V | ¬ cluster ω x ⊆ (Λ m : Set V)} := by
    rw [hescape]
    exact measurableSet_escape x _
  have hsup (k : ℕ) : (⨆ n, μ {ω : Config V | (k : ℕ∞) ≤
      (cluster (ω ∩ (E n : Set (Sym2 V))) x).encard}) =
      μ {ω | (k : ℕ∞) ≤ (cluster ω x).encard} := by
    have h := (edge_tail_mono hE x univ k).measure_iUnion (μ := μ)
    have hu := edge_tail_union hE hcover x univ k
    simp only [inter_univ] at h hu
    rw [← hu] at h
    exact h.symm
  have hninf (n : ℕ) : {ω : Config V | (cluster (ω ∩ (E n : Set (Sym2 V))) x).Infinite} = ∅ := by
    ext ω
    simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
    exact fun h => h (finite_cluster_of_finite_edges ω (E n) x)
  refine ⟨hid, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [← hid, Function.comp_def] using tendsto_measure_iInter_atTop (μ := μ)
      (fun m => (hem m).nullMeasurableSet) hanti ⟨0, measure_ne_top _ _⟩
  · intro k
    simpa only [inter_univ] using (edge_tail_convergence μ hE hcover x univ k).2
  · simp_rw [hsup]
    exact volume_tail_limit μ id measurable_id x
  · intro n
    simpa only [hninf, measure_empty] using volume_tail_limit μ
      (fun ω => ω ∩ (E n : Set (Sym2 V))) (by fun_prop) x
  · have hzero (n : ℕ) : (⨅ k : ℕ, μ {ω : Config V | (k : ℕ∞) ≤
        (cluster (ω ∩ (E n : Set (Sym2 V))) x).encard}) = 0 := by
      rw [← (antitone_volume_tails (fun ω : Config V =>
        cluster (ω ∩ (E n : Set (Sym2 V))) x)).measure_iInter (μ := μ)
          (fun k => ((Set.to_countable {a : ℕ∞ | (k : ℕ∞) ≤ a}).measurableSet.preimage
            ((measurable_encard_cluster x).comp
              (show Measurable (fun ω : Config V => ω ∩ (E n : Set (Sym2 V)))
                  by fun_prop))).nullMeasurableSet)
          ⟨0, measure_ne_top _ _⟩,
        ← infinite_event_as_tails, hninf, measure_empty]
    simp_rw [hzero]
    exact tendsto_const_nhds

-- The deterministic all-open ray gives a genuine failure of interchanging limits.
-- This finite-edge exhaustion deliberately never retains a diagonal pair.
open Classical in
example : ∃ (E : ℕ → Finset (Sym2 ℕ)) (μ : Measure (Config ℕ)),
    IsProbabilityMeasure μ ∧ Monotone E ∧
    (∀ e, ¬ e.IsDiag → ∃ n, e ∈ E n) ∧
    (∀ n e, e.IsDiag → e ∉ E n) ∧
    μ {ω | (cluster ω 0).Infinite} = 1 ∧
    Filter.Tendsto (fun k : ℕ => ⨆ n, μ {ω | (k : ℕ∞) ≤
      (cluster (ω ∩ (E n : Set (Sym2 ℕ))) 0).encard}) Filter.atTop (nhds 1) ∧
    Filter.Tendsto (fun n => ⨅ k : ℕ, μ {ω | (k : ℕ∞) ≤
      (cluster (ω ∩ (E n : Set (Sym2 ℕ))) 0).encard}) Filter.atTop (nhds 0) ∧
    Filter.Tendsto (fun n => ∫⁻ r, ((cluster (r ∩ (E n : Set (Sym2 ℕ))) 0).encard : ℝ≥0∞) ∂μ)
      Filter.atTop (nhds ⊤) := by
  let E (n : ℕ) := ((Finset.range (n+1)).sym2).filter (fun e => ¬ e.IsDiag)
  have hE : Monotone E := by
    intro m n h
    exact Finset.filter_subset_filter _ (Finset.sym2_mono (Finset.range_mono (by omega)))
  have hcover : ∀ e : Sym2 ℕ, ¬ e.IsDiag → ∃ n, e ∈ E n := by
    intro e he
    induction e using Sym2.ind with
    | h a b =>
      refine ⟨max a b, ?_⟩
      simp only [E, Finset.mem_filter, Finset.mk_mem_sym2_iff, Finset.mem_range]
      exact ⟨⟨by omega, by omega⟩, he⟩
  let ω : Config ℕ := (SimpleGraph.hasse ℕ).edgeSet
  let μ : Measure (Config ℕ) := Measure.dirac ω
  have hc : cluster ω 0 = univ := by
    apply eq_univ_of_forall
    intro n
    change (openGraph (SimpleGraph.hasse ℕ).edgeSet).Reachable 0 n
    rw [openGraph, SimpleGraph.fromEdgeSet_edgeSet]
    exact SimpleGraph.preconnected_hasse_of_succOrder ℕ 0 n
  have hprob : μ {r | (cluster r 0).Infinite} = 1 := by
    change (Measure.dirac ω) _ = 1
    apply Measure.dirac_apply_of_mem
    change (cluster ω 0).Infinite
    rw [hc]
    exact Set.infinite_univ
  have h := escape_and_order_of_volume_limits μ E hE hcover
    (fun m => Finset.range (m+1)) (fun _ _ h => Finset.range_mono (by omega))
    (fun v => ⟨v, by simp⟩) 0
  refine ⟨E, μ, inferInstance, hE, hcover, ?_, hprob, ?_, h.2.2.2.2.2, ?_⟩
  · intro n e he
    simp [E, he]
  · simpa only [hprob] using h.2.2.2.1
  · have hi : (∫⁻ r, ((cluster r 0).encard : ℝ≥0∞) ∂μ) = ⊤ := by
      have hm : Measurable (fun r : Config ℕ => ((cluster r 0).encard : ℝ≥0∞)) :=
        (measurable_of_countable (fun a : ℕ∞ => (a : ℝ≥0∞))).comp (measurable_encard_cluster 0)
      rw [show μ = Measure.dirac ω from rfl, lintegral_dirac' ω hm, hc]
      simp
    simpa only [hi] using (finite_edge_exhaustion_limits μ E hE hcover 0).2.2.2.1

end PercLib.Percolation.Bond
