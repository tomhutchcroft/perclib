/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
module

public import PercLib.Meta.Tag
public import PercLib.Combinatorics.FiniteEdgeChange
public import PercLib.Percolation.Bond.ClosedCertificates
public import PercLib.Percolation.Bond.LocalConnectivity
public import PercLib.Percolation.Bond.PathLowerBounds

/-! # Correspondence wrappers for graph certificates

Tagged restatements of deterministic graph facts and of one exact two-point computation.
All mathematical inputs are proved in the imported modules.

## Main results

* `exists_infinite_component_iff_of_finite_edge_change`: finite edge changes preserve the
  existence of an infinite component.
* `localCluster_subset_cluster_inter_and_ssubset_example`: restricted clusters lie in
  cluster intersections, strictly on the path `0 - 1 - 2`.
* `closed_separator_host_certificate`: finite closed separators, finite host certificates,
  and the absence of finite certificates without a host.
* `tau_parallel_two_edge_routes`: the exact two-point function through parallel two-edge
  routes.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal symmDiff

namespace PercLib.Percolation.Bond
variable {V : Type*}

/-- If the edge sets of two simple graphs on the same vertex type differ in finitely many
edges, one has an infinite connected component if and only if the other does. The vertex
type need not be countable and the graphs need not be locally finite. -/
@[tag "D106"]
theorem exists_infinite_component_iff_of_finite_edge_change {G H : SimpleGraph V}
    (h : (G.edgeSet ∆ H.edgeSet).Finite) :
    (∃ c : G.ConnectedComponent, c.supp.Infinite) ↔
      ∃ c : H.ConnectedComponent, c.supp.Infinite :=
  SimpleGraph.exists_supp_infinite_iff_of_finite_symmDiff h

/-- The restricted cluster `K_v^Λ` lies in `K_v ∩ Λ`; on the path `0 - 1 - 2` with both
edges open and `Λ = {0, 2}` the inclusion is strict. -/
@[tag "HQ6X"]
theorem localCluster_subset_cluster_inter_and_ssubset_example :
    (∀ (ω : Config V) (Λ : Set V) (v : V), localCluster ω Λ v ⊆ cluster ω v ∩ Λ) ∧
    localCluster ({s(0, 1), s(1, 2)} : Config (Fin 3)) {0, 2} 0 ⊂
      cluster ({s(0, 1), s(1, 2)} : Config (Fin 3)) 0 ∩ {0, 2} :=
  ⟨localCluster_subset, localCluster_ssubset_cluster_inter_fin_three⟩

/-- If `K(x)` is finite and `x ≁ y`, a finite vertex set containing `x` but not `y` has
closed pair boundary. If moreover the open graph is a subgraph of a locally finite simple
graph `G`, the host boundary `F = δK(x) ∩ E(G)` is finite, closed and meets every host walk
from `x` to `y`, and every configuration whose open graph is contained in `G` and which
closes every pair of `F` has `x ≁ y`. Without a host this fails: on an infinite vertex set,
for distinct `x`, `y` and the empty configuration, the cluster of `x` is finite and `x ≁ y`,
but no finite set of closed pairs certifies nonconnection in every configuration. -/
@[tag "NBY2"]
theorem closed_separator_host_certificate :
    (∀ (ω : Config V) (x y : V), (cluster ω x).Finite → ω ∉ conn x y →
      ∃ C : Finset V, x ∈ C ∧ y ∉ C ∧ ∀ a ∈ C, ∀ b ∉ C, s(a, b) ∉ ω) ∧
    (∀ (G : SimpleGraph V) [G.LocallyFinite] (ω : Config V) (x y : V), openGraph ω ≤ G →
      (cluster ω x).Finite → ω ∉ conn x y →
      (G.between (cluster ω x) (cluster ω x)ᶜ).edgeSet.Finite ∧
      Disjoint (G.between (cluster ω x) (cluster ω x)ᶜ).edgeSet ω ∧
      (∀ w : G.Walk x y, ∃ e ∈ w.edges, e ∈ (G.between (cluster ω x) (cluster ω x)ᶜ).edgeSet) ∧
      ∀ ω' : Config V, openGraph ω' ≤ G →
        Disjoint (G.between (cluster ω x) (cluster ω x)ᶜ).edgeSet ω' → ω' ∉ conn x y) ∧
    (Infinite V → ∀ x y : V, x ≠ y →
      (cluster (∅ : Config V) x).Finite ∧ (∅ : Config V) ∉ conn x y ∧
      ¬ ∃ P : Finset (Sym2 V), ∀ ω : Config V, Disjoint (P : Set (Sym2 V)) ω → ω ∉ conn x y) :=
  ⟨fun _ _ _ hfin h => exists_finset_closed_separating hfin h,
    fun G _ ω x _ _ hfin h =>
      ⟨finite_edgeSet_between_compl G hfin, disjoint_edgeSet_between_cluster_compl G ω x,
        fun w => exists_mem_edges_mem_edgeSet_between_compl w (mem_cluster_self ω x) h,
        fun _ hle hdisj => notMem_conn_of_disjoint_edgeSet_between_compl
          (mem_cluster_self ω x) h hle hdisj⟩,
    fun _ x y hxy =>
      ⟨cluster_empty x ▸ finite_singleton x, (empty_mem_conn_iff x y).not.2 hxy,
        not_exists_finset_forall_disjoint_notMem_conn x y⟩⟩

/-- Let `x ≠ y` and distinct middle vertices `z₁, …, z_k` different from `x` and `y`. If
the only pairs of distinct vertices with positive probability are `{x, zᵢ}` and `{zᵢ, y}`,
with probabilities `aᵢ` and `bᵢ`, then `τ(x, y) = 1 - ∏ᵢ (1 - aᵢ bᵢ)`; if all these
probabilities equal `t`, then `τ(x, y) = 1 - (1 - t²)^k`. Diagonal probabilities are
arbitrary. -/
@[tag "YPNG"]
theorem tau_parallel_two_edge_routes [Countable V] (q : Sym2 V → unitInterval) {x y : V}
    {k : ℕ} {z : Fin k → V} (hz : Function.Injective z) (hxy : x ≠ y) (hzx : ∀ i, z i ≠ x)
    (hzy : ∀ i, z i ≠ y)
    (hq : ∀ u v, u ≠ v → (∀ i, s(u, v) ≠ s(x, z i) ∧ s(u, v) ≠ s(z i, y)) → q s(u, v) = 0) :
    tau q x y = 1 - ∏ i, (1 - (unitInterval.toNNReal (q s(x, z i)) : ℝ≥0∞) *
      (unitInterval.toNNReal (q s(z i, y)) : ℝ≥0∞)) ∧
    ∀ t : unitInterval, (∀ i, q s(x, z i) = t) → (∀ i, q s(z i, y) = t) →
      tau q x y = 1 - (1 - (unitInterval.toNNReal t : ℝ≥0∞) *
        (unitInterval.toNNReal t : ℝ≥0∞)) ^ k :=
  ⟨tau_eq_one_sub_prod_of_parallel_routes q hz hxy hzx hzy hq, fun _ hxt hyt => by
    simpa only [Fintype.card_fin] using
      tau_eq_one_sub_pow_of_parallel_routes q hz hxy hzx hzy hq hxt hyt⟩

end PercLib.Percolation.Bond
