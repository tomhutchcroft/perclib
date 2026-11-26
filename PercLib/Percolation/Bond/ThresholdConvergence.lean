/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs on this library's bond-percolation interface and pinned mathlib
56a005855ea17e0b0958f73ec801ae140b0a1679. No upstream code is copied.
Mathematical reference: the standard coupling of all product measures by thresholding
independent uniform variables.
-/
module

public import PercLib.Percolation.Bond.Basic
public import PercLib.Probability.Coupling.Monotone

/-!
# Convergence of cluster observables along converging profiles

Let profiles `q i` converge pointwise to `q₀`, all below a profile `p` whose clusters at the
points of a finite set `Λ` are almost surely finite. Then the expectation of every bounded
observable that depends only on the clusters of the points of `Λ` converges. The proof
couples all profiles by thresholding one family of independent uniform variables: below `p`,
a cluster of a point of `Λ` only sees the finitely many pairs inside the `p`-clusters, and each
of these eventually has its limiting status, since a uniform variable equals the limiting
threshold with probability zero.

## Main results

* `PercLib.Percolation.Bond.cluster_subset_of_forall_mem_imp`: a cluster below `P` only uses
  pairs inside any set containing the `P`-cluster.
* `PercLib.Percolation.Bond.eventually_cluster_setOf_le_eq`: the deterministic eventual
  agreement of threshold clusters.
* `PercLib.Percolation.Bond.tendsto_lintegral_law_of_tendsto`: convergence of the expectations.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set PercLib.Probability
open scoped ENNReal

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-- Below a configuration `P`, the cluster of `x` only uses pairs inside any set `C` containing
the `P`-cluster of `x`: if every such pair open in `ω` is open in `ω'`, the `ω`-cluster is
contained in the `ω'`-cluster. -/
theorem cluster_subset_of_forall_mem_imp {ω ω' P : Config V} (hω : ω ⊆ P) {C : Set V} {x : V}
    (hC : cluster P x ⊆ C) (h : ∀ a ∈ C, ∀ b ∈ C, s(a, b) ∈ ω → s(a, b) ∈ ω') :
    cluster ω x ⊆ cluster ω' x := by
  intro y hy
  change (openGraph ω).Reachable x y at hy
  change (openGraph ω').Reachable x y
  rw [SimpleGraph.reachable_iff_reflTransGen] at hy ⊢
  induction hy with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c hxb hbc ih =>
    refine ih.tail ?_
    have hrb : (openGraph ω).Reachable x b := (SimpleGraph.reachable_iff_reflTransGen _ _).2 hxb
    have hrc : (openGraph ω).Reachable x c :=
      (SimpleGraph.reachable_iff_reflTransGen _ _).2 (hxb.tail hbc)
    have hb : b ∈ C := hC (hrb.mono (openGraph_mono hω))
    have hc : c ∈ C := hC (hrc.mono (openGraph_mono hω))
    rw [openGraph_adj_iff] at hbc ⊢
    exact ⟨h b hb c hc hbc.1, hbc.2⟩

/-- Two configurations below `P` that agree on the pairs inside a set containing the
`P`-cluster of `x` have the same cluster at `x`. -/
theorem cluster_eq_of_forall_mem_iff {ω ω' P : Config V} (hω : ω ⊆ P) (hω' : ω' ⊆ P)
    {C : Set V} {x : V} (hC : cluster P x ⊆ C)
    (h : ∀ a ∈ C, ∀ b ∈ C, (s(a, b) ∈ ω ↔ s(a, b) ∈ ω')) : cluster ω x = cluster ω' x :=
  (cluster_subset_of_forall_mem_imp hω hC fun a ha b hb => (h a ha b hb).1).antisymm
    (cluster_subset_of_forall_mem_imp hω' hC fun a ha b hb => (h a ha b hb).2)

/-- Deterministic eventual agreement of threshold clusters: if `q i → q₀` pointwise, all below
`p`, the `p`-threshold clusters of the points of `Λ` are finite and `U` avoids the limiting
thresholds, then eventually the `q i`-threshold clusters of the points of `Λ` are the
`q₀`-threshold clusters. -/
theorem eventually_cluster_setOf_le_eq {E : Type*} [TopologicalSpace E] [LinearOrder E]
    [OrderTopology E] {ι : Type*} {l : Filter ι} (U : Sym2 V → E)
    {q : ι → Sym2 V → E} {q₀ p : Sym2 V → E}
    (hq : ∀ e, Tendsto (fun i => q i e) l (𝓝 (q₀ e))) (hle : ∀ i, q i ≤ p) (hle₀ : q₀ ≤ p)
    (Λ : Finset V) (hfin : ∀ x ∈ Λ, (cluster {e | U e ≤ p e} x).Finite)
    (hU : ∀ e, U e ≠ q₀ e) :
    ∀ᶠ i in l, ∀ x ∈ Λ, cluster {e | U e ≤ q i e} x = cluster {e | U e ≤ q₀ e} x := by
  set P : Config V := {e | U e ≤ p e}
  set C : Set V := ⋃ x ∈ Λ, cluster P x
  have hCf : C.Finite := Set.Finite.biUnion Λ.finite_toSet hfin
  set Es : Set (Sym2 V) := (fun z : V × V => s(z.1, z.2)) '' (C ×ˢ C)
  have hEf : Es.Finite := (hCf.prod hCf).image _
  have key : ∀ e, ∀ᶠ i in l, (U e ≤ q i e ↔ U e ≤ q₀ e) := by
    intro e
    rcases lt_or_gt_of_ne (hU e) with h | h
    · filter_upwards [(hq e).eventually (lt_mem_nhds h)] with i hi
      exact iff_of_true hi.le h.le
    · filter_upwards [(hq e).eventually (gt_mem_nhds h)] with i hi
      exact iff_of_false (not_le.2 hi) (not_le.2 h)
  filter_upwards [hEf.eventually_all.2 fun e _ => key e] with i hi x hx
  refine cluster_eq_of_forall_mem_iff (P := P) (fun e he => le_trans he (hle i e))
    (fun e he => le_trans he (hle₀ e)) (C := C)
    (Set.subset_biUnion_of_mem (u := fun x => cluster P x) (Finset.mem_coe.2 hx))
    fun a ha b hb => hi _ ⟨(a, b), ⟨ha, hb⟩, rfl⟩

/-- Thresholding at a fixed profile is measurable. -/
theorem measurable_setOf_le_apply {E : Type*} (r : E → unitInterval) :
    Measurable fun U : E → unitInterval => {e | U e ≤ r e} :=
  measurable_setOfPred.comp (by fun_prop)

variable [Countable V]

/-- **Convergence of cluster observables.** Let `q i → q₀` pointwise along a countably
generated filter, all below a profile `p` whose clusters at the points of a finite set `Λ` are
almost surely finite. Then for every bounded measurable observable `f` depending only on the
clusters of the points of `Λ`, `E_{q i} f → E_{q₀} f`. -/
theorem tendsto_lintegral_law_of_tendsto {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {q : ι → Sym2 V → unitInterval} {q₀ p : Sym2 V → unitInterval}
    (hq : ∀ e, Tendsto (fun i => q i e) l (𝓝 (q₀ e))) (hle : ∀ i, q i ≤ p) (hle₀ : q₀ ≤ p)
    (Λ : Finset V) (hfin : ∀ᵐ ω ∂law p, ∀ x ∈ Λ, (cluster ω x).Finite)
    {f : Config V → ℝ≥0∞} (hf : Measurable f) {C : ℝ≥0∞} (hC : C ≠ ∞) (hfC : ∀ ω, f ω ≤ C)
    (hloc : ∀ ω ω', (∀ x ∈ Λ, cluster ω x = cluster ω' x) → f ω = f ω') :
    Tendsto (fun i => ∫⁻ ω, f ω ∂law (q i)) l (𝓝 (∫⁻ ω, f ω ∂law q₀)) := by
  set μ := Measure.infinitePi fun _ : Sym2 V => (volume : Measure unitInterval)
  have hlaw : ∀ r, ∫⁻ ω, f ω ∂law r = ∫⁻ U, f {e | U e ≤ r e} ∂μ := fun r => by
    rw [law, ← infinitePi_volume_map_setOf_le_eq_prodBernoulli,
      lintegral_map hf (measurable_setOf_le_apply r)]
  simp_rw [hlaw]
  refine tendsto_lintegral_filter_of_dominated_convergence (fun _ => C)
    (Eventually.of_forall fun i => hf.comp (measurable_setOf_le_apply _))
    (Eventually.of_forall fun i => ae_of_all _ fun U => hfC _) (by simp [hC]) ?_
  have h1 : ∀ᵐ U ∂μ, ∀ x ∈ Λ, (cluster {e | U e ≤ p e} x).Finite := by
    have h : ∀ᵐ ω ∂μ.map (fun U => {e | U e ≤ p e}), ∀ x ∈ Λ, (cluster ω x).Finite := by
      rw [infinitePi_volume_map_setOf_le_eq_prodBernoulli]
      exact hfin
    exact ae_of_ae_map (measurable_setOf_le_apply p).aemeasurable h
  have h2 : ∀ᵐ U ∂μ, ∀ e, U e ≠ q₀ e := by
    rw [ae_all_iff]
    intro e
    have h0 : μ {U | U e = q₀ e} = 0 := by
      have hm : Measurable fun U : Sym2 V → unitInterval => U e := measurable_pi_apply e
      rw [show {U : Sym2 V → unitInterval | U e = q₀ e} = (fun U => U e) ⁻¹' {q₀ e} from rfl,
        ← Measure.map_apply hm (measurableSet_singleton _), Measure.infinitePi_map_eval]
      exact measure_singleton _
    exact measure_eq_zero_iff_ae_notMem.1 h0
  filter_upwards [h1, h2] with U hU1 hU2
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_cluster_setOf_le_eq U hq hle hle₀ Λ hU1 hU2] with i hi
  exact (hloc _ _ hi).symm

end PercLib.Percolation.Bond
