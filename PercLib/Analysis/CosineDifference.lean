/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New proofs for this project; no upstream Lean code is copied.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Differences of absolutely summable cosine kernels

The coefficients may have either sign and the phase functions are arbitrary. The bounds
therefore apply to real Fourier kernels without a lattice or positivity hypothesis.

## Main results

* `abs_tsum_cos_second_difference_le`: the symmetric difference has constant `2`.
* `tsum_cos_antisymmetric_difference_sq_le_sin_sq`: a sine-square Cauchy–Schwarz bound.
* `tsum_cos_antisymmetric_difference_sq_le`: the cosine-deficit bound with constant `16`.
-/

@[expose] public section

open Real

namespace PercLib.Analysis

variable {ι : Type*}

/-- Multiplication by arbitrary cosine phases preserves summability of a real kernel. -/
theorem summable_mul_cos {a : ι → ℝ} (ha : Summable a) (t : ι → ℝ) :
    Summable (fun i => a i * cos (t i)) := by
  apply ha.abs.of_norm_bounded
  intro i
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  exact mul_le_of_le_one_right (abs_nonneg _) (abs_cos_le_one _)

/-- The absolute kernel weighted by a cosine deficit is summable. -/
theorem summable_abs_mul_one_sub_cos {a : ι → ℝ} (ha : Summable a) (t : ι → ℝ) :
    Summable (fun i => |a i| * (1 - cos (t i))) := by
  simp_rw [mul_sub, mul_one]
  exact ha.abs.sub (summable_mul_cos ha.abs t)

/-- The absolute kernel weighted by a squared sine is summable. -/
theorem summable_abs_mul_sin_sq {a : ι → ℝ} (ha : Summable a) (t : ι → ℝ) :
    Summable (fun i => |a i| * sin (t i) ^ 2) := by
  apply ha.abs.of_norm_bounded
  intro i
  rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (sq_nonneg _))]
  exact mul_le_of_le_one_right (abs_nonneg _) (sin_sq_le_one _)

private theorem summable_mul_sin_mul_sin {a : ι → ℝ} (ha : Summable a) (l k : ι → ℝ) :
    Summable (fun i => a i * sin (l i) * sin (k i)) := by
  apply ha.abs.of_norm_bounded
  intro i
  simp only [norm_mul, Real.norm_eq_abs]
  exact (mul_le_of_le_one_right (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    (abs_sin_le_one _)).trans (mul_le_of_le_one_right (abs_nonneg _) (abs_sin_le_one _))

/-- A cosine kernel has symmetric second difference bounded by twice the absolute
kernel's cosine deficit. -/
theorem abs_tsum_cos_second_difference_le {a : ι → ℝ} (ha : Summable a) (l k : ι → ℝ) :
    |(∑' i, a i * cos (l i - k i)) + (∑' i, a i * cos (l i + k i)) -
      2 * (∑' i, a i * cos (l i))| ≤ 2 * ∑' i, |a i| * (1 - cos (k i)) := by
  have hminus := (summable_mul_cos ha (fun i => l i - k i)).hasSum
  have hplus := (summable_mul_cos ha (fun i => l i + k i)).hasSum
  have hbase := (summable_mul_cos ha l).hasSum
  have hweight := (summable_abs_mul_one_sub_cos ha k).hasSum.mul_left 2
  apply ((hminus.add hplus).sub (hbase.mul_left 2)).norm_le_of_bounded hweight
  intro i
  have hk : 0 ≤ 1 - cos (k i) := sub_nonneg.mpr (cos_le_one _)
  have hid : a i * cos (l i - k i) + a i * cos (l i + k i) -
      2 * (a i * cos (l i)) = -2 * a i * cos (l i) * (1 - cos (k i)) := by
    rw [cos_sub, cos_add]
    ring
  rw [hid, Real.norm_eq_abs]
  simp only [abs_mul, abs_neg, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num),
    abs_of_nonneg hk]
  calc
    _ ≤ 2 * |a i| * (1 - cos (k i)) :=
      mul_le_mul_of_nonneg_right
        (mul_le_of_le_one_right (by positivity) (abs_cos_le_one _)) hk
    _ = _ := by ring

/-- The antisymmetric cosine difference satisfies a Cauchy–Schwarz estimate retaining
the squared sines. This is stronger than the bound by cosine deficits. -/
theorem tsum_cos_antisymmetric_difference_sq_le_sin_sq {a : ι → ℝ}
    (ha : Summable a) (l k : ι → ℝ) :
    ((∑' i, a i * cos (l i + k i)) - (∑' i, a i * cos (l i - k i))) ^ 2 ≤
      4 * (∑' i, |a i| * sin (l i) ^ 2) * ∑' i, |a i| * sin (k i) ^ 2 := by
  classical
  have hl := summable_abs_mul_sin_sq ha l
  have hk := summable_abs_mul_sin_sq ha k
  have hr := summable_mul_sin_mul_sin ha l k
  have hcs : (∑' i, a i * sin (l i) * sin (k i)) ^ 2 ≤
      (∑' i, |a i| * sin (l i) ^ 2) * ∑' i, |a i| * sin (k i) ^ 2 := by
    refine le_of_tendsto_of_tendsto' (hr.hasSum.pow 2)
      (Filter.Tendsto.mul hl.hasSum hk.hasSum) ?_
    intro s
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
      (fun i _ => mul_nonneg (abs_nonneg _) (sq_nonneg _))
      (fun i _ => mul_nonneg (abs_nonneg _) (sq_nonneg _))
    intro i _
    apply le_of_eq
    simp only [mul_pow, ← sq_abs (a i)]
    ring
  have hid : (∑' i, a i * cos (l i + k i)) - (∑' i, a i * cos (l i - k i)) =
      -2 * ∑' i, a i * sin (l i) * sin (k i) := by
    rw [← (summable_mul_cos ha (fun i => l i + k i)).tsum_sub
      (summable_mul_cos ha (fun i => l i - k i)), ← tsum_mul_left]
    apply tsum_congr
    intro i
    rw [cos_add, cos_sub]
    ring
  rw [hid]
  nlinarith

/-- The squared antisymmetric cosine difference is bounded by the product of the two
absolute cosine deficits, with constant `16`. -/
theorem tsum_cos_antisymmetric_difference_sq_le {a : ι → ℝ}
    (ha : Summable a) (l k : ι → ℝ) :
    ((∑' i, a i * cos (l i + k i)) - (∑' i, a i * cos (l i - k i))) ^ 2 ≤
      16 * (∑' i, |a i| * (1 - cos (l i))) * ∑' i, |a i| * (1 - cos (k i)) := by
  have hbound (t : ι → ℝ) : (∑' i, |a i| * sin (t i) ^ 2) ≤
      2 * ∑' i, |a i| * (1 - cos (t i)) := by
    rw [← tsum_mul_left]
    apply (summable_abs_mul_sin_sq ha t).tsum_le_tsum _
      ((summable_abs_mul_one_sub_cos ha t).mul_left 2)
    intro i
    have hs : sin (t i) ^ 2 ≤ 2 * (1 - cos (t i)) := by
      nlinarith [sin_sq_add_cos_sq (t i), sq_nonneg (1 - cos (t i))]
    nlinarith [mul_le_mul_of_nonneg_left hs (abs_nonneg (a i))]
  have hmul := mul_le_mul (hbound l) (hbound k)
    (tsum_nonneg (fun i => mul_nonneg (abs_nonneg _) (sq_nonneg _)))
    (mul_nonneg (by norm_num) (tsum_nonneg
      (fun i => mul_nonneg (abs_nonneg _) (sub_nonneg.mpr (cos_le_one _)))))
  have hcs := tsum_cos_antisymmetric_difference_sq_le_sin_sq ha l k
  nlinarith

end PercLib.Analysis
