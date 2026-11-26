/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New proofs for this project; no upstream Lean code is copied.
-/
module

public import PercLib.Analysis.CosineDifference
public import PercLib.Analysis.LatticeCosineWeight

/-!
# Spatial moments control lattice Fourier differences

For an absolutely summable signed lattice kernel with finite absolute second spatial
moment, the symmetric second difference of its cosine transform is bounded by twice
that moment times the coordinate cosine deficit. Frequencies are arbitrary real vectors.

## Main results

* `tsum_abs_mul_one_sub_cos_lattice_le`: the cosine moment is bounded by the spatial moment.
* `abs_tsum_lattice_cos_second_difference_le`: the bound retaining coordinate squares.
* `abs_tsum_lattice_cos_second_difference_le_norm_sq`: the sup-norm bound with factor `2 d`.
-/

@[expose] public section

open Real

namespace PercLib.Analysis

/-- The absolute cosine moment is bounded by the absolute second spatial moment times
the sum of coordinate cosine deficits. -/
theorem tsum_abs_mul_one_sub_cos_lattice_le {ι : Type*} [Fintype ι]
    {f : (ι → ℤ) → ℝ} (hf : Summable f)
    (hw : Summable (fun x => |f x| * ∑ i, (x i : ℝ) ^ 2)) (k : ι → ℝ) :
    (∑' x, |f x| * (1 - cos (∑ i, k i * (x i : ℝ)))) ≤
      (∑' x, |f x| * ∑ i, (x i : ℝ) ^ 2) * ∑ i, (1 - cos (k i)) := by
  have h := (summable_abs_mul_one_sub_cos hf (fun x => ∑ i, k i * (x i : ℝ))).tsum_le_tsum
    (fun x => show |f x| * (1 - cos (∑ i, k i * (x i : ℝ))) ≤
        (|f x| * ∑ i, (x i : ℝ) ^ 2) * ∑ i, (1 - cos (k i)) from by
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left (one_sub_cos_sum_mul_intCast_le x k) (abs_nonneg (f x)))
    (hw.mul_right (∑ i, (1 - cos (k i))))
  simpa only [tsum_mul_right] using h

/-- The actual signed cosine-transform second difference is bounded by twice the
absolute second spatial moment times the coordinate cosine deficit. -/
theorem abs_tsum_lattice_cos_second_difference_le {ι : Type*} [Fintype ι]
    {f : (ι → ℤ) → ℝ} (hf : Summable f)
    (hw : Summable (fun x => |f x| * ∑ i, (x i : ℝ) ^ 2)) (l k : ι → ℝ) :
    |(∑' x, f x * cos (∑ i, (l i - k i) * (x i : ℝ))) +
        (∑' x, f x * cos (∑ i, (l i + k i) * (x i : ℝ))) -
        2 * (∑' x, f x * cos (∑ i, l i * (x i : ℝ)))| ≤
      2 * (∑' x, |f x| * ∑ i, (x i : ℝ) ^ 2) * ∑ i, (1 - cos (k i)) := by
  have h := abs_tsum_cos_second_difference_le hf
    (fun x => ∑ i, l i * (x i : ℝ)) (fun x => ∑ i, k i * (x i : ℝ))
  simp only [sub_mul, add_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  refine h.trans ?_
  simpa only [mul_assoc, Finset.sum_sub_distrib] using
    mul_le_mul_of_nonneg_left (tsum_abs_mul_one_sub_cos_lattice_le hf hw k)
      (by norm_num : (0 : ℝ) ≤ 2)

/-- The sup-norm version of the absolute cosine-moment bound. -/
theorem tsum_abs_mul_one_sub_cos_lattice_le_norm_sq {d : ℕ}
    {f : (Fin d → ℤ) → ℝ} (hf : Summable f)
    (hw : Summable (fun x => |f x| * ‖x‖ ^ 2)) (k : Fin d → ℝ) :
    (∑' x, |f x| * (1 - cos (∑ i, k i * (x i : ℝ)))) ≤
      (d : ℝ) * (∑' x, |f x| * ‖x‖ ^ 2) * ∑ i, (1 - cos (k i)) := by
  have h := (summable_abs_mul_one_sub_cos hf (fun x => ∑ i, k i * (x i : ℝ))).tsum_le_tsum
    (fun x => show |f x| * (1 - cos (∑ i, k i * (x i : ℝ))) ≤
        (d : ℝ) * (|f x| * ‖x‖ ^ 2) * ∑ i, (1 - cos (k i)) from by
      have hp := mul_le_mul_of_nonneg_left
        (one_sub_cos_sum_mul_intCast_le_norm_sq x k) (abs_nonneg (f x))
      simpa only [mul_assoc, mul_left_comm, mul_comm] using hp)
    ((hw.mul_left (d : ℝ)).mul_right (∑ i, (1 - cos (k i))))
  simpa only [tsum_mul_left, tsum_mul_right] using h

/-- In sup norm the second-difference bound has factor `2 d` in front of the absolute
second spatial moment and the sum of coordinate cosine deficits. -/
theorem abs_tsum_lattice_cos_second_difference_le_norm_sq {d : ℕ}
    {f : (Fin d → ℤ) → ℝ} (hf : Summable f)
    (hw : Summable (fun x => |f x| * ‖x‖ ^ 2)) (l k : Fin d → ℝ) :
    |(∑' x, f x * cos (∑ i, (l i - k i) * (x i : ℝ))) +
        (∑' x, f x * cos (∑ i, (l i + k i) * (x i : ℝ))) -
        2 * (∑' x, f x * cos (∑ i, l i * (x i : ℝ)))| ≤
      2 * (d : ℝ) * (∑' x, |f x| * ‖x‖ ^ 2) * ∑ i, (1 - cos (k i)) := by
  have h := abs_tsum_cos_second_difference_le hf
    (fun x => ∑ i, l i * (x i : ℝ)) (fun x => ∑ i, k i * (x i : ℝ))
  simp only [sub_mul, add_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  refine h.trans ?_
  simpa only [mul_assoc, Finset.sum_sub_distrib] using
    mul_le_mul_of_nonneg_left (tsum_abs_mul_one_sub_cos_lattice_le_norm_sq hf hw k)
      (by norm_num : (0 : ℝ) ≤ 2)

end PercLib.Analysis
