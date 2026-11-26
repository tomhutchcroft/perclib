/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Adapted from repository `yujinhkim/lrp`, file `PercLib/CriticalLRP/Exploration/BFS/Counting.lean`;
added at source revision `b4ea9ce13d15b85d2ffa5c7544656693d8e7f59a`, supplied under its Apache-2.0
header. The canonical target
namespace is `PercLib.Percolation.Bond.Exploration.BFS`. Existing monotone-union/cardinality and
cluster-measurability APIs are used
instead of restating them. The proof of the lower-base characterization of `epow` is included as
useful API. This is a proof-only module; forbidden options and task labels are omitted.
-/
module

public import PercLib.Percolation.Bond.Exploration.BFS.Measurable
public import PercLib.Percolation.Bond.FiniteVolume
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Basic.ENNReal.BigOperators
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# BFS generations and finite-horizon cardinality convergence

The true open cluster is the increasing union of its BFS horizons. Its extended cardinality
is one plus the supremum of finite generation sums, and its `ℝ≥0∞` cardinality is a genuine
infinite sum. Finite-horizon convergence is proved without assuming that the cluster, vertex
degrees, or graph is finite. The convergence supplies bounds to a possibly infinite cluster.

Generic monotone-union and extended-cardinality conversion lemmas already in the library are used
on the relevant hypotheses; no separate finite-window configuration is introduced.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter PercLib.Percolation.Bond
open scoped ENNReal BigOperators Topology

namespace PercLib.Percolation.Bond.Exploration.BFS

variable {V : Type*}

/-! ### The finite horizon and its cardinality -/

theorem horizon_eq_P_succ (ω : Config V) (o : V) (k : ℕ) :
    horizon ω o k = P ω o (k + 1) := by
  rw [horizon_eq, P_succ]

theorem horizon_succ (ω : Config V) (o : V) (k : ℕ) :
    horizon ω o (k + 1) = horizon ω o k ∪ gen ω o k := by
  rw [horizon_eq_P_succ, horizon_eq_P_succ, P_succ, gen]

theorem disjoint_horizon_gen (ω : Config V) (o : V) (k : ℕ) :
    Disjoint (horizon ω o k) (gen ω o k) := by
  rw [horizon_eq_P_succ, gen]
  exact disjoint_P_A ω o (k + 1)

theorem horizon_mono (ω : Config V) (o : V) : Monotone (horizon ω o) := by
  intro i j h
  induction h with
  | refl => exact subset_rfl
  | step _ ih =>
      exact ih.trans (by rw [horizon_succ]; exact Set.subset_union_left)

theorem horizon_subset_cluster (ω : Config V) (o : V) (k : ℕ) :
    horizon ω o k ⊆ cluster ω o := by
  intro y hy
  rw [horizon_eq] at hy
  rcases hy with hyP | hyA
  · rw [P_eq_iUnion] at hyP
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hyP
    exact A_subset_cluster ω o j hj
  · exact A_subset_cluster ω o k hyA

theorem A_subset_horizon_succ (ω : Config V) (o : V) (k : ℕ) :
    A ω o k ⊆ horizon ω o (k + 1) := by
  rw [horizon_eq_P_succ]
  exact (A_subset_P_succ ω o k).trans (P_subset_succ ω o (k + 1))

/-- The cluster is the increasing union of the finite horizons. -/
theorem cluster_eq_iUnion_horizon (ω : Config V) (o : V) :
    cluster ω o = ⋃ k, horizon ω o k := by
  rw [cluster_eq_iUnion_A]
  apply le_antisymm
  · intro y hy
    rw [Set.mem_iUnion] at hy ⊢
    obtain ⟨k, hk⟩ := hy
    exact ⟨k + 1, A_subset_horizon_succ ω o k hk⟩
  · intro y hy
    rw [Set.mem_iUnion] at hy
    obtain ⟨k, hk⟩ := hy
    have hcl : y ∈ cluster ω o := horizon_subset_cluster ω o k hk
    rwa [cluster_eq_iUnion_A] at hcl

theorem encard_horizon (ω : Config V) (o : V) (k : ℕ) :
    (horizon ω o k).encard = 1 + ∑ j ∈ Finset.range k, (gen ω o j).encard := by
  induction k with
  | zero =>
      rw [Finset.range_zero, Finset.sum_empty]
      rw [horizon_eq, P_zero, A_zero, Set.empty_union, Set.encard_singleton, add_zero]
  | succ k ih =>
      rw [horizon_succ, Set.encard_union_eq (disjoint_horizon_gen ω o k), ih,
        Finset.sum_range_succ, add_assoc]

/-! ### The counting identities -/

/-- The cardinality of the actual cluster is one plus the supremum of the finite
partial sums of generation cardinalities (the `ℕ∞`-sum). -/
theorem encard_cluster_eq_iSup_horizon (ω : Config V) (o : V) :
    (cluster ω o).encard = ⨆ k, (horizon ω o k).encard := by
  rw [cluster_eq_iUnion_horizon]
  exact encard_iUnion_of_monotone (horizon_mono ω o)


theorem encard_cluster_eq_iSup (ω : Config V) (o : V) :
    (cluster ω o).encard =
      ⨆ k, (1 + ∑ j ∈ Finset.range k, (gen ω o j).encard) := by
  rw [encard_cluster_eq_iSup_horizon]
  exact iSup_congr fun k => encard_horizon ω o k

/-- The cardinality of the actual cluster is one plus the genuine `tsum` of the
generation cardinalities in `ℝ≥0∞`. -/
theorem encard_cluster_toENNReal_eq_tsum (ω : Config V) (o : V) :
    ((cluster ω o).encard : ℝ≥0∞) =
      1 + ∑' j : ℕ, ((gen ω o j).encard : ℝ≥0∞) := by
  rw [encard_cluster_eq_iSup, ENat.toENNReal_iSup, ENNReal.tsum_eq_iSup_nat,
    ENNReal.add_iSup]
  apply iSup_congr
  intro k
  rw [ENat.toENNReal_add, ENat.toENNReal_one,
    show ((∑ j ∈ Finset.range k, (gen ω o j).encard : ℕ∞) : ℝ≥0∞)
      = ∑ j ∈ Finset.range k, ((gen ω o j).encard : ℝ≥0∞) from
      map_sum ENat.toENNRealRingHom _ _]

/-- Monotone finite-horizon convergence of the cluster cardinality in `ℝ≥0∞`. -/
theorem tendsto_encard_horizon (ω : Config V) (o : V) :
    Tendsto (fun k => ((horizon ω o k).encard : ℝ≥0∞)) atTop
      (𝓝 ((cluster ω o).encard : ℝ≥0∞)) := by
  have hmono : Monotone fun k => ((horizon ω o k).encard : ℝ≥0∞) :=
    fun i j h => ENat.toENNReal_le.mpr (Set.encard_mono (horizon_mono ω o h))
  have h := tendsto_atTop_iSup hmono
  rwa [← ENat.toENNReal_iSup, ← encard_cluster_eq_iSup_horizon] at h

end PercLib.Percolation.Bond.Exploration.BFS
