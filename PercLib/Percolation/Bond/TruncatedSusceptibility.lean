/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New definition and proofs, written on 2026-11-22. No upstream proof is copied.
Mathematical reference: the truncated susceptibility `E_p[|K|; |K| < ∞]` of percolation theory
(Grimmett, *Percolation*, 2nd ed., §8.6; Duminil-Copin–Tassion 2016).
-/
module

public import PercLib.Meta.Tag
public import PercLib.Percolation.Bond.Susceptibility

/-!
# Truncated susceptibility

The truncated susceptibility `χ^f_q(x) = E_q[|K_x|; |K_x| < ∞]` is the expected cluster volume
with infinite clusters counted as zero. It is `ℝ≥0∞`-valued and agrees with the susceptibility
`chi q x` exactly when the cluster is almost surely finite or both are infinite.

## Main definitions

* `truncatedChi q x`: the truncated susceptibility.

## Main results

* `truncatedChi_eq_lintegral_ncard`: infinite clusters have `ncard = 0`, so
  `χ^f = E |K_x|.ncard`.
* `truncatedChi_eq_setLIntegral`: `χ^f = ∫⁻ over {K_x finite} of |K_x|`.
* `truncatedChi_le_chi`: `χ^f ≤ χ`.
* `chi_eq_truncatedChi_add_top_mul`: `χ = χ^f + ∞ · P(|K_x| = ∞)`.
* `truncatedChi_eq_chi_of_ae_finite`: if `K_x` is almost surely finite, `χ^f = χ`.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-- The **truncated susceptibility** `E_q[|K_x|; |K_x| < ∞]`: the expected volume of the open
cluster of `x`, where the volume is taken to be zero on infinite clusters. -/
@[tag "MTJT"]
def truncatedChi (q : Sym2 V → unitInterval) (x : V) : ℝ≥0∞ :=
  ∫⁻ ω, {ω : Config V | (cluster ω x).Finite}.indicator
    (fun ω => ((cluster ω x).encard : ℝ≥0∞)) ω ∂(law q)

/-- The integrand of `truncatedChi` is the `ncard` of the cluster, which vanishes on infinite
sets. -/
theorem indicator_finite_encard_cluster_eq_ncard (ω : Config V) (x : V) :
    {ω : Config V | (cluster ω x).Finite}.indicator
      (fun ω => ((cluster ω x).encard : ℝ≥0∞)) ω = ((cluster ω x).ncard : ℝ≥0∞) := by
  by_cases h : (cluster ω x).Finite
  · rw [indicator_of_mem (show ω ∈ {ω : Config V | (cluster ω x).Finite} from h),
      ← h.cast_ncard_eq]
    rfl
  · rw [indicator_of_notMem (show ω ∉ {ω : Config V | (cluster ω x).Finite} from h),
      Set.Infinite.ncard h]
    simp

theorem truncatedChi_eq_lintegral_ncard (q : Sym2 V → unitInterval) (x : V) :
    truncatedChi q x = ∫⁻ ω, ((cluster ω x).ncard : ℝ≥0∞) ∂(law q) := by
  simp only [truncatedChi, indicator_finite_encard_cluster_eq_ncard]

/-- On a countable vertex type the event that the cluster is finite is measurable. -/
theorem measurableSet_cluster_finite [Countable V] (x : V) :
    MeasurableSet {ω : Config V | (cluster ω x).Finite} := by
  have h : {ω : Config V | (cluster ω x).Finite} =
      {ω : Config V | (cluster ω x).Infinite}ᶜ := by
    ext ω
    simp only [Set.mem_ofPred_eq, mem_compl_iff, Set.not_infinite]
  rw [h]
  exact (measurableSet_cluster_infinite x).compl

theorem truncatedChi_eq_setLIntegral [Countable V] (q : Sym2 V → unitInterval) (x : V) :
    truncatedChi q x =
      ∫⁻ ω in {ω : Config V | (cluster ω x).Finite}, ((cluster ω x).encard : ℝ≥0∞) ∂(law q) :=
  lintegral_indicator (measurableSet_cluster_finite x) _

theorem truncatedChi_le_chi (q : Sym2 V → unitInterval) (x : V) :
    truncatedChi q x ≤ chi q x :=
  lintegral_mono fun ω => indicator_le_self _ _ ω

/-- The susceptibility splits as the truncated susceptibility plus `∞` times the probability of
an infinite cluster. -/
theorem chi_eq_truncatedChi_add_top_mul [Countable V] (q : Sym2 V → unitInterval) (x : V) :
    chi q x = truncatedChi q x + ∞ * law q {ω : Config V | (cluster ω x).Infinite} := by
  have hfin := measurableSet_cluster_finite (V := V) x
  have hcompl : {ω : Config V | (cluster ω x).Finite}ᶜ =
      {ω : Config V | (cluster ω x).Infinite} := by
    ext ω
    simp only [Set.mem_ofPred_eq, mem_compl_iff, Set.not_finite]
  have hinf : ∫⁻ ω in {ω : Config V | (cluster ω x).Infinite},
      ((cluster ω x).encard : ℝ≥0∞) ∂(law q) =
        ∞ * law q {ω : Config V | (cluster ω x).Infinite} := by
    rw [← setLIntegral_const]
    refine setLIntegral_congr_fun (measurableSet_cluster_infinite x) fun ω hω => ?_
    simp [Set.Infinite.encard_eq hω]
  rw [chi, truncatedChi_eq_setLIntegral, ← hinf, ← hcompl, lintegral_add_compl _ hfin]

/-- If the cluster is almost surely finite, the truncated and full susceptibilities agree. -/
theorem truncatedChi_eq_chi_of_ae_finite [Countable V] {q : Sym2 V → unitInterval} {x : V}
    (h : ∀ᵐ ω ∂(law q), (cluster ω x).Finite) : truncatedChi q x = chi q x := by
  refine lintegral_congr_ae (h.mono fun ω hω => ?_)
  exact indicator_of_mem (show ω ∈ {ω : Config V | (cluster ω x).Finite} from hω) _

end PercLib.Percolation.Bond
