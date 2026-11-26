/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-21. No upstream proof is copied. Mathematical reference:
N. H. Bingham, C. M. Goldie and J. L. Teugels, *Regular variation*, §1.6 (Karamata's
theorem), applied to a tail function.
-/
module

public import PercLib.Analysis.RegularVariation.UniformConvergence
public import Mathlib.MeasureTheory.Integral.Layercake

/-!
# Truncated means of a regularly varying tail

Let `F` be a nonincreasing nonnegative function, regularly varying at infinity of index `-ρ`
with `ρ < 1` (typically `F t = P(X > t)`). Karamata's integral theorem gives, for every fixed
`ε > 0`,
`(ε / z) ∫_0^{z/ε} F ∼ ε^ρ F(z) / (1 - ρ)` as `z → ∞`.
The layer-cake formula identifies `(1/c) ∫_0^{c} P(X > t) dt` with `E min(1, X / c)`.

## Main results

* `tendsto_mul_integral_div_of_regularlyVarying`: the truncated-mean asymptotic above;
* `lintegral_min_eq_lintegral_tail`: `E min(c, X) = ∫_0^c P(X > t) dt` for `X ≥ 0`.
-/

@[expose] public section

noncomputable section

open Filter Set MeasureTheory
open scoped Topology ENNReal

namespace PercLib.Analysis

/-- **Truncated mean of a regularly varying tail.** If `F ≥ 0` is antitone and regularly
varying of index `-ρ` with `ρ < 1`, then for every `ε > 0`,
`(ε / z) ∫_0^{z/ε} F / F z → ε ^ ρ / (1 - ρ)` as `z → ∞`. -/
theorem tendsto_mul_integral_div_of_regularlyVarying {F : ℝ → ℝ} {ρ ε : ℝ} (hρ : ρ < 1)
    (hε : 0 < ε) (hF : Antitone F) (hrv : RegularlyVarying (-ρ) F) :
    Tendsto (fun z => ε / z * (∫ t in (0 : ℝ)..z / ε, F t) / F z) atTop
      (𝓝 (ε ^ ρ / (1 - ρ))) := by
  have hm : Measurable F := hF.measurable
  have hρ' : (-1 : ℝ) < -ρ := by linarith
  have hK := lemma_I_2_10_of_regularlyVarying hρ' hm (hF.locallyIntegrable.locallyIntegrableOn _)
    hrv.eventually_pos hrv
  have hden : Tendsto (fun r => r * F r) atTop atTop :=
    tendsto_r_mul_of_potter hρ' hrv.eventually_pos (potterBounds_of_regularlyVarying hm hrv)
  -- the contribution of `[0, 1]` is negligible
  have h01 : Tendsto (fun r => (∫ t in (0 : ℝ)..1, F t) / (r * F r)) atTop (𝓝 0) := by
    have := hden.inv_tendsto_atTop.const_mul (∫ t in (0 : ℝ)..1, F t)
    rw [mul_zero] at this
    exact this.congr fun r => by simp [div_eq_mul_inv]
  have hratio : Tendsto (fun r => F r / F (ε * r)) atTop (𝓝 (ε ^ ρ)) := by
    have h := (hrv.tendsto hε).inv₀ (Real.rpow_pos_of_pos hε _).ne'
    rw [Real.rpow_neg hε.le, inv_inv] at h
    refine h.congr' ?_
    filter_upwards with r
    rw [inv_div]
  have hsum : Tendsto (fun r => ((∫ t in (0 : ℝ)..1, F t) / (r * F r) +
      (∫ t in (1 : ℝ)..r, F t) / (r * F r)) * (F r / F (ε * r))) atTop
      (𝓝 ((0 + 1 / (-ρ + 1)) * ε ^ ρ)) := (h01.add hK).mul hratio
  have hlim : (0 + 1 / (-ρ + 1)) * ε ^ ρ = ε ^ ρ / (1 - ρ) := by
    rw [zero_add, show -ρ + 1 = 1 - ρ by ring]; ring
  rw [hlim] at hsum
  have hcomp := hsum.comp (tendsto_id.atTop_div_const hε)
  refine hcomp.congr' ?_
  filter_upwards [eventually_gt_atTop 0,
    (tendsto_id.atTop_div_const hε).eventually hrv.eventually_pos] with z hz hFz
  simp only [Function.comp_apply, id] at hFz ⊢
  have hzε : ε * (z / ε) = z := by field_simp
  rw [hzε, ← add_div, intervalIntegral.integral_add_adjacent_intervals
    (hF.intervalIntegrable) (hF.intervalIntegrable)]
  have h1 : 0 < z / ε := div_pos hz hε
  field_simp

/-- **Layer cake for a truncated variable.** For `X ≥ 0` and `c ≥ 0`,
`E min(c, X) = ∫_0^c P(X > t) dt`. -/
theorem lintegral_min_eq_lintegral_tail {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {X : Ω → ℝ≥0∞} (hX : Measurable X) (c : ℝ) :
    ∫⁻ ω, min (ENNReal.ofReal c) (X ω) ∂μ =
      ∫⁻ t in Ioo 0 c, μ {ω | ENNReal.ofReal t < X ω} := by
  set f : Ω → ℝ := fun ω => (min (ENNReal.ofReal c) (X ω)).toReal with hf
  have hfin : ∀ ω, min (ENNReal.ofReal c) (X ω) ≠ ⊤ :=
    fun ω => (lt_of_le_of_lt (min_le_left _ _) ENNReal.ofReal_lt_top).ne
  have hof : ∀ ω, ENNReal.ofReal (f ω) = min (ENNReal.ofReal c) (X ω) :=
    fun ω => ENNReal.ofReal_toReal (hfin ω)
  have hfm : Measurable f := (measurable_const.min hX).ennreal_toReal
  have hlc := lintegral_eq_lintegral_meas_lt μ (Eventually.of_forall fun ω => by
    simp [f]) hfm.aemeasurable
  simp_rw [hof] at hlc
  rw [hlc, ← lintegral_indicator measurableSet_Ioo, ← lintegral_indicator measurableSet_Ioi]
  congr 1
  funext t
  by_cases ht : t ∈ Ioi (0 : ℝ)
  · have ht0 : 0 < t := ht
    rw [indicator_of_mem ht]
    by_cases htc : t < c
    · rw [indicator_of_mem (show t ∈ Ioo 0 c from ⟨ht0, htc⟩)]
      congr 1
      ext ω
      simp only [mem_ofPred_eq]
      rw [← ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht0.le, hof, lt_min_iff]
      exact and_iff_right ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 htc)
    · rw [indicator_of_notMem (fun h => htc h.2)]
      convert measure_empty (μ := μ)
      ext ω
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_lt]
      rw [← ENNReal.ofReal_le_ofReal_iff ht0.le, hof]
      exact (min_le_left _ _).trans (ENNReal.ofReal_le_ofReal (not_lt.1 htc))
  · rw [indicator_of_notMem ht, indicator_of_notMem (fun h => ht h.1)]

end PercLib.Analysis
