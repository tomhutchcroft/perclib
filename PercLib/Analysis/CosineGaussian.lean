/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New proofs for this project; no upstream Lean code is copied.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp

/-!
# Sharp half-period cosine bounds and Gaussian comparison

The chord of sine on `[0,π/4]` gives the optimal quadratic coefficient on
`[-π/2,π/2]`. Evenness and reflection about `π/2` reduce the exponential absolute-cosine
integral over a full period to four central quarter-period integrals.

## Main results

* `four_mul_sq_div_pi_sq_le_one_sub_cos`: the half-period quadratic deficit bound.
* `four_mul_sq_div_pi_sq_eq_one_sub_cos_pi_div_two`: endpoint equality.
* `integral_exp_abs_cos_sub_one_le`: the full-period Gaussian integral estimate.
* `integral_exp_abs_cos_sub_one_div_two_pi_le`: its normalized form.
-/

@[expose] public section

open Real Set MeasureTheory

namespace PercLib.Analysis

/-- On the central half-period, the cosine deficit has quadratic coefficient `4/π²`. -/
theorem four_mul_sq_div_pi_sq_le_one_sub_cos {x : ℝ} (hx : |x| ≤ π / 2) :
    4 * x ^ 2 / π ^ 2 ≤ 1 - cos x := by
  wlog hx0 : 0 ≤ x
  · simpa using this (by rwa [abs_neg]) (neg_nonneg.mpr (le_of_not_ge hx0))
  rw [abs_of_nonneg hx0] at hx
  have hr0 : 0 ≤ 2 * x / π := by positivity
  have hr1 : 2 * x / π ≤ 1 := (div_le_iff₀ pi_pos).mpr (by linarith)
  have hsin : √2 / π * x ≤ sin (x / 2) := by
    have h := strictConcaveOn_sin_Icc.concaveOn.2
      (show (0 : ℝ) ∈ Icc 0 π from ⟨le_rfl, pi_pos.le⟩)
      (show π / 4 ∈ Icc 0 π from ⟨by positivity, by linarith [pi_pos]⟩)
      (show 0 ≤ 1 - 2 * x / π from sub_nonneg.mpr hr1) hr0 (by ring)
    simp only [smul_eq_mul, sin_zero, sin_pi_div_four, mul_zero, zero_add] at h
    have harg : 2 * x / π * (π / 4) = x / 2 := by field_simp; ring
    rw [harg] at h
    convert h using 1
    ring
  have hsq := (pow_le_pow_left₀ (by positivity) hsin 2).trans_eq (sin_sq_eq_half_sub _)
  simp only [mul_pow, div_pow, sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)] at hsq
  ring_nf at hsq ⊢
  linarith

/-- Equality at the endpoint shows that the uniform quadratic coefficient cannot increase. -/
theorem four_mul_sq_div_pi_sq_eq_one_sub_cos_pi_div_two :
    4 * (π / 2) ^ 2 / π ^ 2 = 1 - cos (π / 2) := by
  rw [cos_pi_div_two]
  field_simp
  ring

/-- Evenness and half-period reflection reduce the full absolute-cosine integral to
four copies of the central quarter-period. -/
theorem integral_exp_abs_cos_sub_one_eq_four_mul (a : ℝ) :
    (∫ t in Ioo (-π) π, exp (a * (|cos t| - 1))) =
      4 * ∫ t in (0 : ℝ)..π / 2, exp (a * (cos t - 1)) := by
  let f : ℝ → ℝ := fun t => exp (a * (|cos t| - 1))
  have hf : Continuous f := by fun_prop
  have heven (t : ℝ) : f (-t) = f t := by simp only [f, cos_neg]
  have hreflect (t : ℝ) : f (π - t) = f t := by simp only [f, cos_pi_sub, abs_neg]
  have hneg : (∫ t in (-π)..0, f t) = ∫ t in (0 : ℝ)..π, f t := by
    have h := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := π) f
    simpa only [heven, neg_zero] using h.symm
  have hright : (∫ t in π / 2..π, f t) = ∫ t in (0 : ℝ)..π / 2, f t := by
    have h := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := π / 2) f π
    have hhalf : π - π / 2 = π / 2 := by ring
    simpa only [hreflect, hhalf, sub_zero] using h.symm
  have hwhole := intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable (μ := volume) (-π) 0) (hf.intervalIntegrable 0 π)
  have hhalf := intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable (μ := volume) 0 (π / 2)) (hf.intervalIntegrable (π / 2) π)
  have hcentral : (∫ t in (0 : ℝ)..π / 2, f t) =
      ∫ t in (0 : ℝ)..π / 2, exp (a * (cos t - 1)) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le pi_div_two_pos.le] at ht
    have hc : 0 ≤ cos t := cos_nonneg_of_mem_Icc ⟨by linarith [ht.1, pi_pos], ht.2⟩
    simp only [f, abs_of_nonneg hc]
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (show -π ≤ π by linarith [pi_pos])]
  change (∫ t in (-π)..π, f t) = _
  rw [hneg] at hwhole
  rw [hright, hcentral] at hhalf
  linarith

/-- The periodic absolute-cosine exponential admits a Gaussian bound with coefficient
coming from the sharp central quadratic estimate. -/
theorem integral_exp_abs_cos_sub_one_le {a : ℝ} (ha : 0 < a) :
    (∫ t in Ioo (-π) π, exp (a * (|cos t| - 1))) ≤ π * √(π / a) := by
  let c : ℝ := 4 * a / π ^ 2
  have hc : 0 < c := by dsimp only [c]; positivity
  have hgauss := integrable_exp_neg_mul_sq hc
  have hcentral : (∫ t in (0 : ℝ)..π / 2, exp (a * (cos t - 1))) ≤
      ∫ t in (0 : ℝ)..π / 2, exp (-c * t ^ 2) := by
    apply intervalIntegral.integral_mono_on pi_div_two_pos.le
      ((by fun_prop : Continuous (fun t : ℝ => exp (a * (cos t - 1)))).intervalIntegrable _ _)
      ((by fun_prop : Continuous (fun t : ℝ => exp (-c * t ^ 2))).intervalIntegrable _ _)
    intro t ht
    apply exp_le_exp.mpr
    have hdef := four_mul_sq_div_pi_sq_le_one_sub_cos
      (show |t| ≤ π / 2 by rw [abs_of_nonneg ht.1]; exact ht.2)
    have hmul := mul_le_mul_of_nonneg_left hdef ha.le
    change a * (cos t - 1) ≤ -(4 * a / π ^ 2) * t ^ 2
    convert neg_le_neg hmul using 1 <;> ring
  have hhalfline : (∫ t in (0 : ℝ)..π / 2, exp (-c * t ^ 2)) ≤
      ∫ t in Ioi (0 : ℝ), exp (-c * t ^ 2) := by
    rw [intervalIntegral.integral_of_le pi_div_two_pos.le]
    exact setIntegral_mono_set hgauss.integrableOn
      (Filter.Eventually.of_forall fun t => (exp_pos _).le)
      (Filter.Eventually.of_forall fun _ ht => ht.1)
  have hscale : 4 * (√(π / c) / 2) = π * √(π / a) := by
    have heq : π / c = (π / 2) ^ 2 * (π / a) := by dsimp only [c]; field_simp; ring
    rw [heq, sqrt_mul (sq_nonneg _), sqrt_sq pi_div_two_pos.le]
    ring
  rw [integral_exp_abs_cos_sub_one_eq_four_mul]
  calc
    _ ≤ 4 * (∫ t in Ioi (0 : ℝ), exp (-c * t ^ 2)) :=
      mul_le_mul_of_nonneg_left (hcentral.trans hhalfline) (by norm_num)
    _ = _ := by rw [integral_gaussian_Ioi, hscale]

/-- Normalizing the full-period integral by its length gives `sqrt (π/(4a))`. -/
theorem integral_exp_abs_cos_sub_one_div_two_pi_le {a : ℝ} (ha : 0 < a) :
    (∫ t in Ioo (-π) π, exp (a * (|cos t| - 1))) / (2 * π) ≤ √(π / (4 * a)) := by
  have h := div_le_div_of_nonneg_right (integral_exp_abs_cos_sub_one_le ha)
    (show (0 : ℝ) ≤ 2 * π by positivity)
  have heq : π * √(π / a) / (2 * π) = √(π / (4 * a)) := by
    have harg : π / (4 * a) = (π / a) / 4 := by ring
    have hfour : √(4 : ℝ) = 2 := by
      rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, sqrt_sq (by norm_num)]
    rw [harg, sqrt_div (div_nonneg pi_pos.le ha.le), hfour]
    field_simp
  exact h.trans_eq heq

end PercLib.Analysis
