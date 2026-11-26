/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New proofs for this project; no upstream Lean code is copied.
Mathematical reference: the Fourier moments of simple nearest-neighbour walk on the
integer lattice, computed by independence of the coordinate characters.
-/
module

public import PercLib.Analysis.LazyWalkThresholds
public import Mathlib.Data.Nat.Choose.Sum

/-!
# The first two even moments of the nearest-neighbour symbol

The ordinary nearest-neighbour symbol on `ℤ^d` is `d⁻¹ ∑ j, cos (k j)`.
Its second and fourth moments with normalized torus volume are exactly `1 / (2d)`
and `3(2d - 1) / (8d³)`. The integration domain is the same sup-norm ball
`(-π, π)^d` used by the finite-step Fourier formulas in `LazyWalkThresholds`.

## Main results

* `integral_sum_cos_sq`, `integral_sum_cos_pow_four`: the unnormalized coordinate sums.
* `integral_nearestNeighborSymbol_sq`, `integral_nearestNeighborSymbol_pow_four`:
  the exact normalized moments for every positive dimension.
-/

@[expose] public section

noncomputable section

open MeasureTheory Metric Set Real Finset

namespace PercLib.Analysis

private theorem integrable_sum_cos_pow {ι : Type*} [Fintype ι]
    (μ : Measure (ι → ℝ)) [IsFiniteMeasure μ] (m : ℕ) :
    Integrable (fun k => (∑ j, cos (k j)) ^ m) μ := by
  refine Integrable.of_bound
    ((continuous_finsetSum _ fun j _ =>
      continuous_cos.comp (continuous_apply j)).pow m).aestronglyMeasurable
    ((Fintype.card ι : ℝ) ^ m)
    (Filter.Eventually.of_forall fun k => ?_)
  rw [norm_pow]
  apply pow_le_pow_left₀ (norm_nonneg _) _ m
  calc
    ‖∑ j, cos (k j)‖ ≤ ∑ j, ‖cos (k j)‖ := norm_sum_le _ _
    _ ≤ ∑ _j : ι, (1 : ℝ) := sum_le_sum fun j _ => by
      simpa only [Real.norm_eq_abs] using abs_cos_le_one (k j)
    _ = _ := by simp

private theorem integrable_cos_pow (μ : Measure ℝ) [IsFiniteMeasure μ] (m : ℕ) :
    Integrable (fun k => cos k ^ m) μ := by
  refine Integrable.of_bound (by fun_prop) 1 (Filter.Eventually.of_forall fun k => ?_)
  rw [norm_pow, Real.norm_eq_abs]
  exact pow_le_one₀ (abs_nonneg _) (abs_cos_le_one _)

/-- Open-period cosine moments agree with the corresponding interval integrals. -/
theorem integral_Ioo_cos_pow_eq_interval (m : ℕ) :
    (∫ k in Ioo (-π) π, cos k ^ m) = ∫ k in (-π)..π, cos k ^ m := by
  rw [intervalIntegral.integral_of_le (by linarith [pi_pos]), integral_Ioc_eq_integral_Ioo]

private theorem integral_Ioo_cos_pow_zero : (∫ k in Ioo (-π) π, cos k ^ 0) = 2 * π := by
  rw [integral_Ioo_cos_pow_eq_interval]
  simp
  ring

private theorem integral_Ioo_cos_pow_one : (∫ k in Ioo (-π) π, cos k ^ 1) = 0 := by
  rw [integral_Ioo_cos_pow_eq_interval]
  simp

private theorem integral_Ioo_cos_pow_two : (∫ k in Ioo (-π) π, cos k ^ 2) = π := by
  rw [integral_Ioo_cos_pow_eq_interval]
  simp

private theorem integral_Ioo_cos_pow_three : (∫ k in Ioo (-π) π, cos k ^ 3) = 0 := by
  rw [integral_Ioo_cos_pow_eq_interval]
  simp

private theorem integral_Ioo_cos_pow_four : (∫ k in Ioo (-π) π, cos k ^ 4) = 3 * π / 4 := by
  rw [integral_Ioo_cos_pow_eq_interval]
  rw [show (4 : ℕ) = 2 + 2 from rfl, integral_cos_pow]
  simp
  ring

/-- Integrating out one coordinate gives the binomial recurrence for cosine moments. -/
theorem integral_pi_sum_cos_pow_succ (μ : Measure ℝ) [IsFiniteMeasure μ]
    (d m : ℕ) :
    (∫ k : Fin (d + 1) → ℝ, (∑ j, cos (k j)) ^ m ∂Measure.pi (fun _ => μ)) =
      ∑ r ∈ range (m + 1), (m.choose r : ℝ) * (∫ t, cos t ^ r ∂μ) *
        ∫ k : Fin d → ℝ, (∑ j, cos (k j)) ^ (m - r) ∂Measure.pi (fun _ => μ) := by
  have hchange :
      (∫ k : Fin (d + 1) → ℝ, (∑ j, cos (k j)) ^ m ∂Measure.pi (fun _ => μ)) =
      ∫ z : ℝ × (Fin d → ℝ), (cos z.1 + ∑ j, cos (z.2 j)) ^ m
        ∂μ.prod (Measure.pi (fun _ => μ)) := by
    rw [← ((measurePreserving_piFinSuccAbove (fun _ : Fin (d + 1) => μ) 0).symm).integral_comp']
    simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Fin.sum_univ_succ, Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.cons_succ,
      Fin.zero_succAbove, Fin.cons_zero, cast_eq]
  rw [hchange]
  simp_rw [add_pow]
  have hint (r : ℕ) : Integrable
      (fun z : ℝ × (Fin d → ℝ) => cos z.1 ^ r *
        (∑ j, cos (z.2 j)) ^ (m - r) * (m.choose r : ℝ))
      (μ.prod (Measure.pi (fun _ : Fin d => μ))) :=
    ((integrable_cos_pow μ r).mul_prod
      (integrable_sum_cos_pow (Measure.pi (fun _ : Fin d => μ)) (m - r))).mul_const _
  rw [integral_finsetSum _ fun r _ => hint r]
  apply sum_congr rfl
  intro r hr
  rw [integral_mul_const, integral_prod_mul (fun t : ℝ => cos t ^ r)
    (fun k : Fin d → ℝ => (∑ j, cos (k j)) ^ (m - r))]
  ring

/-- The zeroth cosine-sum moment is the volume of the torus box. -/
theorem integral_pi_sum_cos_pow_zero (d : ℕ) :
    (∫ k : Fin d → ℝ, (∑ j, cos (k j)) ^ 0
      ∂Measure.pi (fun _ => volume.restrict (Ioo (-π) π))) = (2 * π) ^ d := by
  have h := integral_fintype_prod_eq_pow (ι := Fin d)
    (μ := volume.restrict (Ioo (-π) π)) (fun k : ℝ => cos k ^ 0)
  rw [integral_Ioo_cos_pow_zero] at h
  simpa only [pow_zero, prod_const_one, Fintype.card_fin] using h

private theorem integral_pi_sum_cos_even_moments (d : ℕ) :
    (∫ k : Fin d → ℝ, (∑ j, cos (k j)) ^ 2
      ∂Measure.pi (fun _ => volume.restrict (Ioo (-π) π))) = (2 * π) ^ d * d / 2 ∧
    (∫ k : Fin d → ℝ, (∑ j, cos (k j)) ^ 4
      ∂Measure.pi (fun _ => volume.restrict (Ioo (-π) π))) =
      (2 * π) ^ d * (3 * d * (2 * d - 1)) / 8 := by
  induction d with
  | zero => simp
  | succ d ih =>
    constructor
    · rw [integral_pi_sum_cos_pow_succ]
      simp only [sum_range_succ, sum_range_zero, Nat.choose_zero_right,
        Nat.choose_self, Nat.cast_one, Nat.choose_succ_self_right,
        Nat.sub_zero, Nat.sub_self, one_mul, zero_add]
      rw [integral_Ioo_cos_pow_zero, integral_Ioo_cos_pow_one, integral_Ioo_cos_pow_two,
        integral_pi_sum_cos_pow_zero, ih.1]
      push_cast
      rw [pow_succ]
      ring
    · rw [integral_pi_sum_cos_pow_succ]
      norm_num only [sum_range_succ, sum_range_zero, Nat.choose_zero_right,
        Nat.choose_self, Nat.choose_succ_self_right, Nat.choose_eq_factorial_div_factorial,
        Nat.factorial, Nat.cast_one, Nat.cast_ofNat, Nat.reduceSub, Nat.reduceMul,
        Nat.reduceDiv, Nat.reduceAdd, one_mul, zero_add]
      rw [integral_Ioo_cos_pow_zero, integral_Ioo_cos_pow_one, integral_Ioo_cos_pow_two,
        integral_Ioo_cos_pow_three, integral_Ioo_cos_pow_four, integral_pi_sum_cos_pow_zero,
        ih.1, ih.2]
      push_cast
      rw [pow_succ]
      ring

/-- The sup-norm torus box has the product of its one-dimensional restricted measures. -/
theorem volume_restrict_pi_ball_eq_pi_Ioo (d : ℕ) :
    (volume : Measure (Fin d → ℝ)).restrict (ball 0 π) =
      Measure.pi (fun _ => volume.restrict (Ioo (-π) π)) := by
  have hball : ball (0 : Fin d → ℝ) π = Set.univ.pi fun _ => Ioo (-π) π := by
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · ext k
      simp [Subsingleton.elim k 0, pi_pos]
    · have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
      rw [ball_pi _ pi_pos]
      simp [Real.ball_eq_Ioo]
  rw [hball, volume_pi, Measure.restrict_pi_pi]

/-- The second moment of the sum of the coordinate cosines on the torus box. -/
theorem integral_sum_cos_sq (d : ℕ) :
    (∫ k in ball (0 : Fin d → ℝ) π, (∑ j, cos (k j)) ^ 2) =
      (2 * π) ^ d * d / 2 := by
  rw [volume_restrict_pi_ball_eq_pi_Ioo]
  exact (integral_pi_sum_cos_even_moments d).1

/-- The fourth moment of the sum of the coordinate cosines on the torus box. -/
theorem integral_sum_cos_pow_four (d : ℕ) :
    (∫ k in ball (0 : Fin d → ℝ) π, (∑ j, cos (k j)) ^ 4) =
      (2 * π) ^ d * (3 * d * (2 * d - 1)) / 8 := by
  rw [volume_restrict_pi_ball_eq_pi_Ioo]
  exact (integral_pi_sum_cos_even_moments d).2

/-- The normalized second torus moment of the ordinary nearest-neighbour symbol is
`1 / (2d)`. -/
theorem integral_nearestNeighborSymbol_sq {d : ℕ} (hd : 0 < d) :
    ((2 * π) ^ d)⁻¹ *
      (∫ k in ball (0 : Fin d → ℝ) π, ((d : ℝ)⁻¹ * ∑ j, cos (k j)) ^ 2) =
      1 / (2 * d : ℝ) := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hp0 : (2 * π) ^ d ≠ 0 := pow_ne_zero _ (mul_ne_zero (by norm_num) pi_ne_zero)
  simp_rw [mul_pow]
  rw [integral_const_mul, integral_sum_cos_sq]
  field_simp
  ring

/-- The normalized fourth torus moment of the ordinary nearest-neighbour symbol is
`3(2d - 1) / (8d³)`. -/
theorem integral_nearestNeighborSymbol_pow_four {d : ℕ} (hd : 0 < d) :
    ((2 * π) ^ d)⁻¹ *
      (∫ k in ball (0 : Fin d → ℝ) π, ((d : ℝ)⁻¹ * ∑ j, cos (k j)) ^ 4) =
      3 * (2 * d - 1) / (8 * (d : ℝ) ^ 3) := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hp0 : (2 * π) ^ d ≠ 0 := pow_ne_zero _ (mul_ne_zero (by norm_num) pi_ne_zero)
  simp_rw [mul_pow]
  rw [integral_const_mul, integral_sum_cos_pow_four]
  field_simp
  ring

end PercLib.Analysis
