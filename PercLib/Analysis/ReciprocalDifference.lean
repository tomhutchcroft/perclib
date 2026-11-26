/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New proofs for this project; no upstream Lean code is copied.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Second differences of reciprocals

## Main results

An exact symmetric identity separates the second difference of a reciprocal
into the second difference and squared first difference of its denominator.
The resulting estimate retains absolute values, so it applies to signed kernels.
The random-walk comparison keeps its parameter-dependent constant.
-/

@[expose] public section

namespace PercLib.Analysis

/-- Symmetric second-difference identity; no positivity is required. -/
theorem reciprocal_second_difference {a b c : ℝ}
    (ha : 1 - a ≠ 0) (hb : 1 - b ≠ 0) (hc : 1 - c ≠ 0) :
    (1 - a)⁻¹ + (1 - c)⁻¹ - 2 * (1 - b)⁻¹ =
      (1 - b)⁻¹ * ((1 - a)⁻¹ + (1 - c)⁻¹) / 2 * (a + c - 2 * b) +
      (1 - b)⁻¹ * (1 - a)⁻¹ * (1 - c)⁻¹ / 2 * (c - a) ^ 2 := by
  field_simp
  ring

/-- A denominator estimate with separate second and first difference controls.
Keeping the reciprocal factors absolute avoids a sign assumption. -/
theorem abs_reciprocal_second_difference_le {a b c u v : ℝ}
    (ha : 1 - a ≠ 0) (hb : 1 - b ≠ 0) (hc : 1 - c ≠ 0)
    (hsecond : |a + c - 2 * b| ≤ 2 * u)
    (hfirst : (c - a) ^ 2 ≤ 16 * v * u) :
    |(1 - a)⁻¹ + (1 - c)⁻¹ - 2 * (1 - b)⁻¹| ≤
      (|(1 - a)⁻¹| + |(1 - c)⁻¹|) * |(1 - b)⁻¹| * u +
      8 * |(1 - a)⁻¹ * (1 - b)⁻¹ * (1 - c)⁻¹| * v * u := by
  rw [reciprocal_second_difference ha hb hc]
  calc
    _ ≤ |(1 - b)⁻¹ * ((1 - a)⁻¹ + (1 - c)⁻¹) / 2 * (a + c - 2 * b)| +
        |(1 - b)⁻¹ * (1 - a)⁻¹ * (1 - c)⁻¹ / 2 * (c - a) ^ 2| :=
      abs_add_le _ _
    _ ≤ (|(1 - b)⁻¹| * (|(1 - a)⁻¹| + |(1 - c)⁻¹|) / 2) * (2 * u) +
        (|(1 - b)⁻¹| * |(1 - a)⁻¹| * |(1 - c)⁻¹| / 2) * (16 * v * u) := by
      simp only [abs_mul, abs_div, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num), abs_pow, sq_abs]
      apply add_le_add
      · exact mul_le_mul
          (div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left (abs_add_le _ _) (abs_nonneg _)) (by norm_num))
          hsecond (abs_nonneg _) (by positivity)
      · exact mul_le_mul_of_nonneg_left hfirst (by positivity)
    _ = _ := by simp only [abs_mul]; ring

/-- The random-walk denominator comparison, before division. -/
theorem walk_denominator_comparison {lam t : ℝ}
    (hlam : lam ≤ 1) (ht : -1 ≤ t) :
    (1 + lam) * (1 - t) ≤ 2 * (1 - lam * t) := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hlam) (show 0 ≤ 1 + t by linarith)]

/-- Parameter-dependent comparison with the massless reciprocal. -/
theorem walk_reciprocal_le {lam t : ℝ}
    (hlam0 : 0 ≤ lam) (hlam1 : lam < 1) (ht0 : -1 ≤ t) (ht1 : t < 1) :
    (1 - lam * t)⁻¹ ≤ 2 / (1 + lam) * (1 - t)⁻¹ := by
  have hden : 0 < 1 - lam * t := by
    nlinarith [mul_nonneg hlam0 (sub_nonneg.mpr ht1.le)]
  have hmass : 0 < 1 - t := sub_pos.mpr ht1
  have hplus : 0 < 1 + lam := by linarith
  have h := walk_denominator_comparison hlam1.le ht0
  apply (le_div_iff₀ hmass).2
  apply (le_div_iff₀ hplus).2
  rw [inv_mul_eq_div, div_mul_eq_mul_div]
  apply (div_le_iff₀ hden).2
  nlinarith

/-- Equality at the lowest possible symbol proves that the comparison factor
`2 / (1 + lam)` cannot be decreased uniformly over symbols in `[-1,1)`. -/
theorem walk_reciprocal_comparison_sharp (lam : ℝ) :
    (1 - lam * (-1))⁻¹ = 2 / (1 + lam) * (1 - (-1 : ℝ))⁻¹ := by
  simp
  ring

end PercLib.Analysis
