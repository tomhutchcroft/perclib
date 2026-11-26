/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Proof of Lemma I.4.12, the two-cluster gap inequality, of T. Hutchcroft, *Critical long-range
percolation I*, arXiv:2508.18807v1, the target `TwoClusterGap` of
`PercLib/Percolation/Bond/ClusterCorrelation/Defs.lean`, for every profile. The argument follows the
repository `yujinhkim/lrp`, branch `critical-lrp-1`, commit
`d382e4c28d92dd4e698ebf4f2aaf0bc932ae73fc`, file
`PercLib/CriticalLRP/Correlation/TwoClusterGap.lean` (`twoCluster_gap_le`); licence Apache-2.0 as
declared in that file header and `third_party/critical-lrp/NOTICE.md`; upstream
`yujinhkim/Critical-Long-range-percolation` at `3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf` (not
independently verified). Contributor: yujinhkim. The source's hypotheses `hTG` (tree graph) and
`hBK` are discharged by `treeGraphInequality` and `countable_profile_bk` of this library; the proof
is rewritten on the bond interface.
-/
module

public import PercLib.Percolation.Bond.ClusterCorrelation.Restoration
public import PercLib.Percolation.Bond.Forest
public import PercLib.Percolation.Bond.TreeGraph.BranchPoint
public import PercLib.Probability.CountableBK
public import Mathlib.Combinatorics.SimpleGraph.Paths

/-! # Lemma I.4.12: the two-cluster gap inequality

Write `τ(o,x) τ(y,z)` as the probability under `μ ⊗ μ` that `o ↔ x` in `ω` and `y ↔ z` in
`ω'`. Take a path from `y` to `z` in `ω'`.
* If it avoids `K_o(ω)`, the restored configuration `ω̃ = restoreMap o (ω, ω')` (law `μ`)
  has `o ↔ x`, `y ↔ z` and `o ↮ y`.
* Otherwise it visits some `b ∈ K_o(ω)`, and splitting the path at `b` shows that `y ↔ b`
  and `b ↔ z` occur disjointly in `ω'`; BK and the tree-graph inequality bound this by
  `∑_a τ(o,a) τ(a,x) τ(a,b) · τ(y,b) τ(b,z)`.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set
open scoped ENNReal
open PercLib.Probability

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-- The pairs of a walk of the open graph are open. -/
theorem walk_edges_subset {ω : Config V} {u v : V} (p : (openGraph ω).Walk u v) :
    ∀ e ∈ p.edges, e ∈ ω := fun e he => by
  have h := p.edges_subset_edgeSet he
  simp only [openGraph, SimpleGraph.edgeSet_fromEdgeSet, mem_sdiff] at h
  exact h.1

/-- **Splitting a path.** If a trail of `ω` from `y` to `z` passes through `b`, then `y ↔ b` and
`b ↔ z` occur disjointly in `ω`. -/
theorem mem_disjointOccurrence_of_trail {ω : Config V} {y z b : V}
    (p : (openGraph ω).Walk y z) (hp : p.IsTrail) (hb : b ∈ p.support) :
    ω ∈ disjointOccurrence (conn y b) (conn b z) := by
  classical
  rw [mem_disjointOccurrence_iff_open (isUpperSet_conn y b) (isUpperSet_conn b z)]
  set p₁ := p.takeUntil b hb
  set p₂ := p.dropUntil b hb
  have hdisj := hp.disjoint_edges_takeUntil_dropUntil hb
  have hsub : ∀ e, e ∈ p₁.edges ∨ e ∈ p₂.edges → e ∈ ω := fun e he => by
    rcases he with he | he
    · exact walk_edges_subset p e (p.edges_takeUntil_subset_edges hb he)
    · exact walk_edges_subset p e (p.edges_dropUntil_subset_edges hb he)
  refine ⟨{e | e ∈ p₁.edges}, {e | e ∈ p₂.edges}, p₁.edges.finite_toSet,
    p₂.edges.finite_toSet, Set.disjoint_left.2 fun e h₁ h₂ => hdisj h₁ h₂,
    fun e he => hsub e (Or.inl he), fun e he => hsub e (Or.inr he),
    mem_conn_of_walk_edges p₁ fun e he => he, mem_conn_of_walk_edges p₂ fun e he => he⟩

/-- **Lemma I.4.12** for every profile on a countable vertex type. -/
theorem twoClusterGap [Countable V] : TwoClusterGap V := by
  intro q o x y z
  classical
  set μ := law q
  set E : Set (Config V) := conn o x ∩ conn y z ∩ (conn o y)ᶜ
  have hEm : MeasurableSet E :=
    ((measurableSet_conn o x).inter (measurableSet_conn y z)).inter (measurableSet_conn o y).compl
  set B : V → Set (Config V × Config V) := fun b =>
    (conn o x ∩ conn o b) ×ˢ disjointOccurrence (conn y b) (conn b z)
  -- the covering
  have hcover : conn o x ×ˢ conn y z ⊆ restoreMap o ⁻¹' E ∪ ⋃ b, B b := by
    rintro p ⟨hx, hz⟩
    obtain ⟨w⟩ := (show (openGraph p.2).Reachable y z from hz)
    set w' := w.bypass
    have hw' : w'.IsPath := w.bypass_isPath
    by_cases hb : ∃ b ∈ w'.support, b ∈ cluster p.1 o
    · obtain ⟨b, hbw, hbK⟩ := hb
      exact Or.inr (mem_iUnion.2 ⟨b, ⟨hx, hbK⟩,
        mem_disjointOccurrence_of_trail w' hw'.isTrail hbw⟩)
    · simp only [not_exists, not_and] at hb
      refine Or.inl ⟨⟨?_, ?_⟩, ?_⟩
      · change x ∈ cluster (restoreMap o p) o
        rw [cluster_restoreMap]; exact hx
      · refine mem_conn_of_walk_edges w' fun e he => ?_
        have hnt : ¬∃ v ∈ e, v ∈ cluster p.1 o := by
          rintro ⟨v, hv, hvK⟩
          exact hb v (w'.fst_mem_support_of_mem_edges (Sym2.other_spec hv ▸ he)) hvK
        exact (mem_restoreMap_of_not_touch hnt).2 (walk_edges_subset w' e he)
      · intro hoy
        have : y ∈ cluster (restoreMap o p) o := hoy
        rw [cluster_restoreMap] at this
        exact hb y w'.start_mem_support this
  -- the bound on each piece
  have hB : ∀ b, (μ.prod μ) (B b) ≤
      (∑' a, tau q o a * tau q a x * tau q a b) * (tau q y b * tau q b z) := fun b => by
    rw [Measure.prod_prod]
    exact mul_le_mul' (treeGraphInequality V q o x b)
      (countable_profile_bk q (isUpperSet_conn y b) (isUpperSet_conn b z))
  calc tau q o x * tau q y z = (μ.prod μ) (conn o x ×ˢ conn y z) := by
        rw [Measure.prod_prod]; rfl
    _ ≤ (μ.prod μ) (restoreMap o ⁻¹' E) + (μ.prod μ) (⋃ b, B b) :=
        (measure_mono hcover).trans (measure_union_le _ _)
    _ ≤ μ E + ∑' b, (∑' a, tau q o a * tau q a x * tau q a b) * (tau q y b * tau q b z) := by
        refine add_le_add (le_of_eq ?_) ((measure_iUnion_le _).trans (ENNReal.tsum_le_tsum hB))
        rw [← Measure.map_apply (measurable_restoreMap o) hEm, map_restoreMap]
    _ = law q (conn o x ∩ conn y z ∩ (conn o y)ᶜ) +
          ∑' a, ∑' b, tau q o a * tau q a x * tau q a b * tau q y b * tau q b z := by
        congr 1
        simp_rw [← ENNReal.tsum_mul_right]
        rw [ENNReal.tsum_comm]
        refine tsum_congr fun a => tsum_congr fun b => ?_
        ring

/-! ### Witnesses -/

/-- The zero profile on `ℕ` with `o, x, y, z` distinct: both sides vanish, and the theorem
applies. -/
example : tau (fun _ : Sym2 ℕ => (0 : unitInterval)) 0 1 * tau (fun _ => 0) 2 3 ≤
    law (fun _ : Sym2 ℕ => (0 : unitInterval)) (conn 0 1 ∩ conn 2 3 ∩ (conn 0 2)ᶜ) +
      ∑' a, ∑' b, tau (fun _ => 0) 0 a * tau (fun _ => 0) a 1 * tau (fun _ => 0) a b *
        tau (fun _ => 0) 2 b * tau (fun _ => 0) b 3 :=
  twoClusterGap (fun _ => 0) 0 1 2 3

example (q : Sym2 Bool → unitInterval) (x z : Bool) :=
  twoClusterGap_of_eq q false x z

end PercLib.Percolation.Bond
