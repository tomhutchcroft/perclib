/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New proofs for this project; no upstream Lean code is copied.
Mathematical reference: weighted nearest-neighbour walk resolvents, obtained by
comparing their even Fourier-moment coefficients with the inverse-sixth series.
-/
module

public import PercLib.Analysis.NearestNeighborResolventCritical
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# A weighted nearest-neighbour cubic resolvent bound

Changing measure by the squared symbol gives the exact weighted binomial series.
Its even coefficients are bounded by one twenty-first of the shifted inverse-sixth
coefficients. The comparison takes place after integration, so it remains valid
when the Fourier symbol is negative.

## Main results

* `hasSum_integral_nearestNeighborSymbol_sq_mul_inv_cube`: the exact even series.
* `integral_nearestNeighborSymbol_sq_mul_inv_cube_le`: the normalized weighted
  cubic resolvent is at most `53/(105d)` for `d ≥ 1000` and `0 ≤ r < 1`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Metric Set Real Filter

namespace PercLib.Analysis

/-- The weighted cubic coefficient is at most one twenty-first of the shifted
inverse-sixth coefficient. Equality holds at the first two even orders. -/
theorem choose_two_mul_add_two_le_choose_two_mul_add_seven (m : ℕ) :
    ((2 * m + 2).choose 2 : ℝ) ≤ ((2 * m + 7).choose 5 : ℝ) / 21 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · norm_num [Nat.choose]
  have htwo : (2 * m + 1 : ℝ) * (2 * m + 2) = 2 * ((2 * m + 2).choose 2 : ℝ) := by
    have h := Nat.descFactorial_eq_factorial_mul_choose (2 * m + 2) 2
    change (2 * m + 1) * ((2 * m + 2) * 1) = 2 * (2 * m + 2).choose 2 at h
    simp only [mul_one] at h
    exact_mod_cast h
  have hfive : (2 * m + 3 : ℝ) * ((2 * m + 4) * ((2 * m + 5) *
      ((2 * m + 6) * (2 * m + 7)))) = 120 * ((2 * m + 7).choose 5 : ℝ) := by
    have h := Nat.descFactorial_eq_factorial_mul_choose (2 * m + 7) 5
    change (2 * m + 3) * ((2 * m + 4) * ((2 * m + 5) *
      ((2 * m + 6) * ((2 * m + 7) * 1)))) = 120 * (2 * m + 7).choose 5 at h
    simp only [mul_one] at h
    exact_mod_cast h
  have hm1 : (0 : ℝ) ≤ (m : ℝ) - 1 := by
    have hmR : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
    linarith
  have hpoly : (0 : ℝ) ≤ 4 * m * ((m : ℝ) - 1) *
      (8 * (m : ℝ) ^ 3 + 108 * (m : ℝ) ^ 2 + 598 * m + 513) := by positivity
  nlinarith

/-- Squaring a bounded function gives a finite density, so the existing integrated
binomial theorem also yields its squared-weight resolvent series. -/
theorem hasSum_integral_sq_mul_binomial_of_abs_le_one {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] {f : X → ℝ}
    (hf : Measurable f) (hb : ∀ x, |f x| ≤ 1)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (s : ℕ) :
    HasSum (fun n => ((n + s).choose s : ℝ) * r ^ n * (∫ x, f x ^ (n + 2) ∂μ))
      (∫ x, f x ^ 2 / (1 - r * f x) ^ (s + 1) ∂μ) := by
  have hf2 : Integrable (fun x => f x ^ 2) μ := by
    apply Integrable.of_bound (hf.pow_const 2).aestronglyMeasurable 1
    apply Eventually.of_forall
    intro x
    rw [norm_pow, Real.norm_eq_abs]
    exact pow_le_one₀ (abs_nonneg _) (hb x)
  let ν := μ.withDensity fun x => ENNReal.ofReal (f x ^ 2)
  have : IsFiniteMeasure ν := isFiniteMeasure_withDensity_ofReal hf2.hasFiniteIntegral
  have hweight (g : X → ℝ) : (∫ x, g x ∂ν) = ∫ x, f x ^ 2 * g x ∂μ := by
    dsimp [ν]
    rw [integral_withDensity_eq_integral_toReal_smul
      ((hf.pow_const 2).ennreal_ofReal) (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    simp only [ENNReal.toReal_ofReal (sq_nonneg _), smul_eq_mul]
  have h := hasSum_integral_binomial_of_abs_le_one ν hf.aestronglyMeasurable
    (Eventually.of_forall hb) hr0 hr1 s
  simp_rw [hweight] at h
  have hpow (n : ℕ) : (∫ x, f x ^ 2 * f x ^ n ∂μ) = ∫ x, f x ^ (n + 2) ∂μ := by
    apply integral_congr_ae
    apply Eventually.of_forall
    intro x
    change f x ^ 2 * f x ^ n = f x ^ (n + 2)
    rw [pow_add]
    ring
  simp_rw [hpow] at h
  simpa only [mul_one_div] using h

/-- The exact even-moment expansion of every squared-symbol positive integral resolvent power. -/
theorem hasSum_integral_nearestNeighborSymbol_sq_mul_inv_pow {d : ℕ} (hd : 0 < d)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (s : ℕ) :
    HasSum (fun m => ((2 * m + s).choose s : ℝ) * r ^ (2 * m) *
      (((2 * π) ^ d)⁻¹ * (∫ k in ball (0 : Fin d → ℝ) π,
        ((d : ℝ)⁻¹ * ∑ j, cos (k j)) ^ (2 * (m + 1)))))
      (((2 * π) ^ d)⁻¹ * (∫ k in ball (0 : Fin d → ℝ) π,
        ((d : ℝ)⁻¹ * ∑ j, cos (k j)) ^ 2 /
          (1 - r * ((d : ℝ)⁻¹ * ∑ j, cos (k j))) ^ (s + 1))) := by
  let F : ℕ → ℝ := fun n => ((n + s).choose s : ℝ) * r ^ n *
    (((2 * π) ^ d)⁻¹ * (∫ k in ball (0 : Fin d → ℝ) π,
      ((d : ℝ)⁻¹ * ∑ j, cos (k j)) ^ (n + 2)))
  have hfull : HasSum F
      (((2 * π) ^ d)⁻¹ * (∫ k in ball (0 : Fin d → ℝ) π,
        ((d : ℝ)⁻¹ * ∑ j, cos (k j)) ^ 2 /
          (1 - r * ((d : ℝ)⁻¹ * ∑ j, cos (k j))) ^ (s + 1))) := by
    dsimp only [F]
    rw [volume_restrict_pi_ball_eq_pi_Ioo]
    have h := hasSum_integral_sq_mul_binomial_of_abs_le_one
      (Measure.pi fun _ : Fin d => volume.restrict (Ioo (-π) π))
      (f := fun k => (d : ℝ)⁻¹ * ∑ j, cos (k j)) (by fun_prop)
      (abs_nearestNeighborSymbol_le_one hd) hr0 hr1 s
    apply (h.mul_left (((2 * π) ^ d)⁻¹)).congr_fun
    intro n
    ring
  have heven : Summable (fun m => F (2 * m)) := hfull.summable.comp_injective
    (show Function.Injective (fun m : ℕ => 2 * m) by intro m n h; dsimp at h; omega)
  have hodd : HasSum (fun m => F (2 * m + 1)) 0 := by
    have hzero (m : ℕ) : F (2 * m + 1) = 0 := by
      dsimp [F]
      rw [show 2 * m + 1 + 2 = 2 * (m + 1) + 1 by omega,
        integral_nearestNeighborSymbol_pow_odd, mul_zero, mul_zero]
    simpa only [hzero] using (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℝ)) 0)
  have heq := (HasSum.even_add_odd (f := F) heven.hasSum hodd).unique hfull
  rw [add_zero] at heq
  have h := heq ▸ heven.hasSum
  exact h

/-- The exact even-moment expansion of the squared-symbol cubic resolvent. -/
theorem hasSum_integral_nearestNeighborSymbol_sq_mul_inv_cube {d : ℕ} (hd : 0 < d)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    HasSum (fun m => ((2 * m + 2).choose 2 : ℝ) * r ^ (2 * m) *
      (((2 * π) ^ d)⁻¹ * (∫ k in ball (0 : Fin d → ℝ) π,
        ((d : ℝ)⁻¹ * ∑ j, cos (k j)) ^ (2 * (m + 1)))))
      (((2 * π) ^ d)⁻¹ * (∫ k in ball (0 : Fin d → ℝ) π,
        ((d : ℝ)⁻¹ * ∑ j, cos (k j)) ^ 2 /
          (1 - r * ((d : ℝ)⁻¹ * ∑ j, cos (k j))) ^ 3)) :=
  hasSum_integral_nearestNeighborSymbol_sq_mul_inv_pow hd hr0 hr1 2

/-- The normalized squared-symbol cubic resolvent is at most `53/(105d)`,
uniformly in the subcritical parameter, for every dimension at least 1000. -/
theorem integral_nearestNeighborSymbol_sq_mul_inv_cube_le {d : ℕ} (hd : 1000 ≤ d)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ((2 * π) ^ d)⁻¹ * (∫ k in ball (0 : Fin d → ℝ) π,
      ((d : ℝ)⁻¹ * ∑ j, cos (k j)) ^ 2 /
        (1 - r * ((d : ℝ)⁻¹ * ∑ j, cos (k j))) ^ 3) ≤ 53 / (105 * (d : ℝ)) := by
  let M : ℕ → ℝ := fun m => ((2 * π) ^ d)⁻¹ *
    (∫ k in ball (0 : Fin d → ℝ) π, ((d : ℝ)⁻¹ * ∑ j, cos (k j)) ^ (2 * m))
  let H : ℕ → ℝ := fun m => ((2 * m + 5).choose 5 : ℝ) * M m
  have hfull := summable_and_tsum_nearestNeighbor_moment_inv_six_le hd
  change Summable H ∧ (∑' m, H m) ≤ 1 + 53 / (5 * (d : ℝ)) at hfull
  have hMnonneg (m : ℕ) : 0 ≤ M m := by
    dsimp [M]
    apply mul_nonneg (by positivity)
    apply integral_nonneg
    intro k
    dsimp only
    rw [pow_mul]
    positivity
  have hMzero : M 0 = 1 := by
    dsimp [M]
    rw [volume_restrict_pi_ball_eq_pi_Ioo]
    simp only [pow_zero]
    have hvol : (∫ _k : Fin d → ℝ, (1 : ℝ)
        ∂Measure.pi (fun _ => volume.restrict (Ioo (-π) π))) = (2 * π) ^ d := by
      simpa using integral_pi_sum_cos_pow_zero d
    rw [hvol, inv_mul_cancel₀ (by positivity)]
  have hHzero : H 0 = 1 := by simp [H, hMzero]
  have hshift : Summable (fun m => H (m + 1)) := (summable_nat_add_iff 1).mpr hfull.1
  have hsum : (∑' m, H (m + 1)) ≤ 53 / (5 * (d : ℝ)) := by
    have hsplit := hfull.1.tsum_eq_zero_add
    rw [hHzero] at hsplit
    linarith [hfull.2]
  have hexp := hasSum_integral_nearestNeighborSymbol_sq_mul_inv_cube
    (show 0 < d by omega) hr0 hr1
  rw [← hexp.tsum_eq]
  calc
    _ ≤ ∑' m, H (m + 1) / 21 := by
      apply hexp.summable.tsum_le_tsum _ (hshift.div_const 21)
      intro m
      have hc := choose_two_mul_add_two_le_choose_two_mul_add_seven m
      have hrpow : r ^ (2 * m) ≤ 1 := pow_le_one₀ hr0 hr1.le
      calc
        _ ≤ ((2 * m + 2).choose 2 : ℝ) * M (m + 1) :=
          mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (by positivity) hrpow)
            (hMnonneg (m + 1))
        _ ≤ (((2 * m + 7).choose 5 : ℝ) / 21) * M (m + 1) :=
          mul_le_mul_of_nonneg_right hc (hMnonneg (m + 1))
        _ = H (m + 1) / 21 := by
          dsimp [H]
          rw [show 2 * (m + 1) + 5 = 2 * m + 7 by omega]
          ring
    _ = (∑' m, H (m + 1)) / 21 := tsum_div_const
    _ ≤ (53 / (5 * (d : ℝ))) / 21 :=
      div_le_div_of_nonneg_right hsum (by norm_num)
    _ = _ := by ring

end PercLib.Analysis
