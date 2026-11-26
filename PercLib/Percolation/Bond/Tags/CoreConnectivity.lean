/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
module

public import PercLib.Meta.Tag
public import PercLib.Percolation.Bond.ClosedCertificates
public import PercLib.Percolation.Bond.HarrisDecreasing
public import PercLib.Percolation.Bond.LocalConnectivity
public import PercLib.Percolation.Bond.RowSum

/-! Correspondence wrappers for the connectivity, closed-separator and susceptibility
definitions and their basic properties.
All mathematical inputs are proved in the imported modules. -/

@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace PercLib.Percolation.Bond
variable {V : Type*}

/-- The cluster of `v` is the set of vertices connected to `v`, and the two-point function
is the probability of the connection event. -/
@[tag "6WC8"]
theorem cluster_and_tau_eq_conn (ω : Config V) (q : Sym2 V → unitInterval) (v w : V) :
    cluster ω v = {w | ω ∈ conn v w} ∧ tau q v w = law q (conn v w) :=
  ⟨rfl, rfl⟩

/-- Along an increasing exhaustion of the vertex set, the connection event is the
increasing union of the local connection events, and their probabilities converge to the
two-point function. -/
@[tag "5UJQ"]
theorem conn_eq_iUnion_localConn_and_tendsto (q : Sym2 V → unitInterval)
    {S : ℕ → Set V} (hS : Monotone S) (hcover : ∀ v, ∃ n, v ∈ S n) (x y : V) :
    (conn x y : Set (Config V)) = ⋃ n, localConn (S n) x y ∧
    Filter.Tendsto (fun n => law q (localConn (S n) x y))
      Filter.atTop (nhds (tau q x y)) :=
  ⟨conn_eq_iUnion_localConn hS hcover x y, tendsto_localConn_probability q hS hcover x y⟩

/-- Closed separators: a vertex set with closed edge boundary is a union of clusters, every
cluster boundary is closed, non-connection is witnessed by a closed vertex set or by a
closed separating set of pairs, and the cluster of `x` and its edge boundary are such
witnesses. -/
@[tag "2C4E"]
theorem closed_separators (ω : Config V) (x y : V) :
    (∀ C : Set V, (∀ a ∈ C, ∀ b ∉ C, s(a, b) ∉ ω) →
      ∀ u v, ω ∈ conn u v → u ∈ C → v ∈ C) ∧
    (∀ z a b, a ∈ cluster ω z → b ∉ cluster ω z → s(a, b) ∉ ω) ∧
    (ω ∉ conn x y ↔ ∃ C : Set V, x ∈ C ∧ y ∉ C ∧ ∀ a ∈ C, ∀ b ∉ C, s(a, b) ∉ ω) ∧
    (ω ∉ conn x y ↔ ∃ P : Set (Sym2 V),
      (∀ w : (⊤ : SimpleGraph V).Walk x y, ∃ e ∈ w.edges, e ∈ P) ∧ Disjoint P ω) ∧
    (ω ∉ conn x y →
      (x ∈ cluster ω x ∧ y ∉ cluster ω x ∧
        ∀ a ∈ cluster ω x, ∀ b ∉ cluster ω x, s(a, b) ∉ ω) ∧
      (∀ w : (⊤ : SimpleGraph V).Walk x y, ∃ e ∈ w.edges,
        e ∈ {e : Sym2 V | ∃ a ∈ cluster ω x, ∃ b ∉ cluster ω x, e = s(a, b)}) ∧
      Disjoint {e : Sym2 V | ∃ a ∈ cluster ω x, ∃ b ∉ cluster ω x, e = s(a, b)} ω) := by
  refine ⟨fun C hC u v h hu => mem_of_mem_conn_of_closed hC h hu,
    fun z a b ha hb => notMem_of_mem_cluster_of_notMem ω ha hb,
    not_mem_conn_iff_exists_closed_separating ω x y,
    not_mem_conn_iff_exists_closed_separating_pairs ω x y, fun hxy => ?_⟩
  have hy : y ∉ cluster ω x := hxy
  refine ⟨⟨mem_cluster_self ω x, hy, fun a ha b hb => notMem_of_mem_cluster_of_notMem ω ha hb⟩,
    fun w => ?_, ?_⟩
  · obtain ⟨a, ha, b, hb, he⟩ := exists_mem_edges_boundary w (mem_cluster_self ω x) hy
    exact ⟨s(a, b), he, a, ha, b, hb, rfl⟩
  · rw [Set.disjoint_left]
    rintro e ⟨a, ha, b, hb, rfl⟩
    exact notMem_of_mem_cluster_of_notMem ω ha hb

/-- Non-connection and finiteness of the cluster are decreasing events, and on a countable
vertex set both are measurable. -/
@[tag "ZQI1"]
theorem decreasing_nonconnection_finite_cluster [Countable V] (x y : V) :
    IsLowerSet (conn x y : Set (Config V))ᶜ ∧
    IsLowerSet {ω : Config V | (cluster ω x).Finite} ∧
    MeasurableSet (conn x y : Set (Config V))ᶜ ∧
    MeasurableSet {ω : Config V | (cluster ω x).Finite} := by
  refine ⟨isLowerSet_compl_conn x y, isLowerSet_cluster_finite x,
    (measurableSet_conn x y).compl, ?_⟩
  have h : {ω : Config V | (cluster ω x).Finite} =
      {ω : Config V | (cluster ω x).Infinite}ᶜ := by
    ext ω
    simp only [Set.mem_ofPred_eq, mem_compl_iff, Set.not_infinite]
  rw [h]
  exact (measurableSet_cluster_infinite x).compl

/-- The susceptibility is the expected cluster volume, equals the sum of the two-point
function over the second vertex, and is at least one. -/
@[tag "8DSI"]
theorem chi_eq_lintegral_eq_tsum_tau [Countable V] (q : Sym2 V → unitInterval) (v : V) :
    chi q v = ∫⁻ ω, ((cluster ω v).encard : ℝ≥0∞) ∂(law q) ∧
    chi q v = ∑' w, tau q v w ∧ 1 ≤ chi q v :=
  ⟨rfl, chi_eq_tsum_tau q v, one_le_chi q v⟩

end PercLib.Percolation.Bond
