/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-26: the flux threshold as an infimum and an explicit linear
supercritical density bound, for transitive summable kernels. No upstream proof is copied and
no definition is added.
-/
module

public import PercLib.Percolation.Bond.Sharpness
public import PercLib.Percolation.Bond.IntensityMonotone

/-! # The sharpness threshold as an infimum

For `J` with summable rows, preserved by a transitive family of bijections, write
`Φ_β(o,T) = boundaryFlux (intensityProfile J β) T o`.

## Main results

* `boundaryFlux_intensityProfile_mono`: `β ↦ Φ_β(o,T)` is nondecreasing.
* `rootCriticalIntensity_eq_sInf_one_le_boundaryFlux`:
  `β_c = inf {β ≥ 0 | Φ_β(o,T) ≥ 1 for every finite T ∋ o}`, with `inf ∅ = ∞`.
* `inv_mul_min_le_law_real_cluster_infinite`: for `β > β_c`,
  `P_β(|K_o| = ∞) ≥ (β_c + 1)⁻¹ min {β - β_c, 1}`.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace PercLib.Percolation.Bond

variable {V : Type*}

open Classical in
/-- The boundary flux `Φ_β(o,T)` is nondecreasing in the intensity `β`. -/
theorem boundaryFlux_intensityProfile_mono [Countable V] (J : Sym2 V → ℝ≥0) (T : Finset V)
    (o : V) {β₁ β₂ : ℝ≥0} (h : β₁ ≤ β₂) :
    boundaryFlux (intensityProfile J β₁) T o ≤ boundaryFlux (intensityProfile J β₂) T o := by
  rw [boundaryFlux_def, boundaryFlux_def]
  refine Finset.sum_le_sum fun u _ => ENNReal.tsum_le_tsum fun v => ?_
  split_ifs
  · exact le_rfl
  · refine mul_le_mul' (law_intensityProfile_mono (isUpperSet_localConn _ _ _)
      (measurableSet_localConn _ _ _) J h) (ENNReal.coe_le_coe.2 ?_)
    rw [← NNReal.coe_le_coe]
    simpa using intensityProfile_mono J h s(u, v)

open Classical in
/-- **The flux threshold as an infimum.** Under transitivity and summable rows,
`β_c = inf {β ≥ 0 | Φ_β(o,T) ≥ 1 for every finite T ∋ o}` in `ℝ≥0∞`, with `inf ∅ = ∞`. -/
theorem rootCriticalIntensity_eq_sInf_one_le_boundaryFlux [Countable V] (J : Sym2 V → ℝ≥0)
    (hT : ∀ x y : V, ∃ σ : V ≃ V, σ x = y ∧ ∀ e, J (Sym2.map σ e) = J e)
    (hJ : ∀ u, Summable fun v => (J s(u, v) : ℝ)) (o : V) :
    rootCriticalIntensity J o =
      sInf ((↑) '' {β : ℝ≥0 | ∀ T : Finset V, o ∈ T →
        1 ≤ boundaryFlux (intensityProfile J β) T o}) := by
  refine le_antisymm (le_sInf ?_) ?_
  · rintro _ ⟨β, hβ, rfl⟩
    by_contra h
    rw [not_le, rootCriticalIntensity_eq_sSup_boundaryFlux_lt_one J hT hJ o, lt_sSup_iff] at h
    obtain ⟨_, ⟨β', ⟨S, hoS, hΦ⟩, rfl⟩, hlt⟩ := h
    exact absurd ((hβ S hoS).trans (boundaryFlux_intensityProfile_mono J S o
      (ENNReal.coe_lt_coe.1 hlt).le)) (not_le.2 hΦ)
  · by_cases hc : rootCriticalIntensity J o = ⊤
    · rw [hc]
      exact le_top
    · lift rootCriticalIntensity J o to ℝ≥0 using hc with b hb
      exact sInf_le ⟨b, fun T hoT =>
        one_le_boundaryFlux_of_rootCriticalIntensity_le J hT hJ hb.symm.le T hoT, rfl⟩

/-- For `0 ≤ c < β`, `(c + 1)⁻¹ min {β - c, 1} ≤ 1 - c/β`. -/
theorem inv_add_one_mul_min_le_one_sub_div {c β : ℝ} (hc : 0 ≤ c) (hcβ : c < β) :
    (c + 1)⁻¹ * min (β - c) 1 ≤ 1 - c / β := by
  have hβ : 0 < β := hc.trans_lt hcβ
  have h1 : 1 - c / β = (β - c) / β := by field_simp
  rw [h1, inv_mul_eq_div, div_le_div_iff₀ (by positivity) hβ]
  rcases min_cases (β - c) 1 with ⟨hm, hle⟩ | ⟨hm, hlt⟩
  · rw [hm]
    nlinarith
  · rw [hm]
    nlinarith [mul_nonneg hc (sub_nonneg.2 hlt.le)]

/-- **Explicit linear density bound.** Under transitivity and summable rows, for every
`β > β_c`, `P_β(|K_o| = ∞) ≥ (β_c + 1)⁻¹ min {β - β_c, 1}`. -/
theorem inv_mul_min_le_law_real_cluster_infinite [Countable V] (J : Sym2 V → ℝ≥0)
    (hT : ∀ x y : V, ∃ σ : V ≃ V, σ x = y ∧ ∀ e, J (Sym2.map σ e) = J e)
    (hJ : ∀ u, Summable fun v => (J s(u, v) : ℝ)) {o : V} {β : ℝ≥0}
    (hβ : rootCriticalIntensity J o < β) :
    ((rootCriticalIntensity J o).toReal + 1)⁻¹ *
        min ((β : ℝ) - (rootCriticalIntensity J o).toReal) 1 ≤
      (law (intensityProfile J β)).real {ω | (cluster ω o).Infinite} := by
  have h := one_sub_div_le_law_cluster_infinite J hT hJ hβ
  lift rootCriticalIntensity J o to ℝ≥0 using ne_top_of_lt hβ with b hb
  have hbβ : b < β := ENNReal.coe_lt_coe.1 hβ
  have hβ0 : β ≠ 0 := (pos_of_gt hbβ).ne'
  have hdiv : b / β ≤ 1 := (div_le_one₀ (pos_of_gt hbβ)).2 hbβ.le
  rw [← ENNReal.coe_div hβ0, ← ENNReal.coe_one, ← ENNReal.coe_sub] at h
  have hr := ENNReal.toReal_mono (measure_ne_top _ _) h
  rw [ENNReal.coe_toReal, NNReal.coe_sub hdiv, NNReal.coe_div, NNReal.coe_one] at hr
  rw [ENNReal.coe_toReal]
  exact (inv_add_one_mul_min_le_one_sub_div b.2 (NNReal.coe_lt_coe.2 hbβ)).trans hr

end PercLib.Percolation.Bond
