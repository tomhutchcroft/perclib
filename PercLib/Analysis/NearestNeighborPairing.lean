/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New proofs for this project; no upstream Lean code is copied.
Mathematical reference: the Gaussian pairing bound for even Fourier moments of
simple nearest-neighbour walk on the integer lattice.
-/
module

public import PercLib.Analysis.NearestNeighborMoments

/-!
# Pairing bounds for all nearest-neighbour moments

Each coordinate cosine has vanishing odd moments and even moments bounded by those
of a centered Gaussian of variance one half. The binomial coordinate recurrence
preserves these bounds. Normalizing the coordinate sum gives the factorial pairing
bound in every positive dimension and at every even order.

## Main results

* `integral_Ioo_cos_pow_odd`: odd coordinate cosine moments vanish.
* `integral_sum_cos_pow_even_le`: the unnormalized even-moment pairing bound.
* `integral_nearestNeighborSymbol_pow_even_le`: the normalized factorial bound.
-/

@[expose] public section

noncomputable section

open MeasureTheory Metric Set Real Finset

namespace PercLib.Analysis

/-- Every odd cosine moment over one full period vanishes. -/
theorem integral_Ioo_cos_pow_odd (m : ℕ) :
    (∫ t in Ioo (-π) π, cos t ^ (2 * m + 1)) = 0 := by
  simp_rw [integral_Ioo_cos_pow_eq_interval]
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) + 1 = (2 * m + 1) + 2 by omega, integral_cos_pow]
    simp [ih]

private theorem pairing_factorial_succ (m : ℕ) :
    (((2 * (m + 1)).factorial : ℝ) / (4 ^ (m + 1) * ((m + 1).factorial : ℝ))) =
      ((2 * m + 1 : ℝ) / 2) *
        (((2 * m).factorial : ℝ) / (4 ^ m * (m.factorial : ℝ))) := by
  have hm : (m.factorial : ℝ) ≠ 0 := by positivity
  rw [show 2 * (m + 1) = (2 * m + 1) + 1 by omega]
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat,
    Nat.cast_one, pow_succ]
  field_simp
  ring

/-- The even cosine moment is bounded by the Gaussian moment of variance one half. -/
theorem integral_Ioo_cos_pow_even_le (m : ℕ) :
    (∫ t in Ioo (-π) π, cos t ^ (2 * m)) ≤
      (2 * π) * (((2 * m).factorial : ℝ) / (4 ^ m * (m.factorial : ℝ))) := by
  induction m with
  | zero =>
    rw [integral_Ioo_cos_pow_eq_interval]
    simp
    linarith
  | succ m ih =>
    have hrec : (∫ t in Ioo (-π) π, cos t ^ (2 * (m + 1))) =
        ((2 * m + 1 : ℝ) / (2 * m + 2)) *
          (∫ t in Ioo (-π) π, cos t ^ (2 * m)) := by
      rw [integral_Ioo_cos_pow_eq_interval, integral_Ioo_cos_pow_eq_interval,
        show 2 * (m + 1) = 2 * m + 2 by omega, integral_cos_pow]
      simp
    have hratio : (2 * m + 1 : ℝ) / (2 * m + 2) ≤ (2 * m + 1 : ℝ) / 2 := by
      apply div_le_div_of_nonneg_left (by positivity) (by norm_num)
      nlinarith [Nat.cast_nonneg (α := ℝ) m]
    rw [hrec, pairing_factorial_succ]
    calc
      _ ≤ ((2 * m + 1 : ℝ) / (2 * m + 2)) *
          ((2 * π) * (((2 * m).factorial : ℝ) / (4 ^ m * (m.factorial : ℝ)))) :=
        mul_le_mul_of_nonneg_left ih (by positivity)
      _ ≤ ((2 * m + 1 : ℝ) / 2) *
          ((2 * π) * (((2 * m).factorial : ℝ) / (4 ^ m * (m.factorial : ℝ)))) :=
        mul_le_mul_of_nonneg_right hratio (by positivity)
      _ = _ := by ring

private theorem sum_range_even_of_odd_eq_zero (f : ℕ → ℝ)
    (hodd : ∀ j, f (2 * j + 1) = 0) (m : ℕ) :
    (∑ r ∈ range (2 * m + 1), f r) = ∑ j ∈ range (m + 1), f (2 * j) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) + 1 = (2 * m + 1) + 1 + 1 by omega,
      sum_range_succ, sum_range_succ, ih, hodd, add_zero, sum_range_succ]
    simp only [sum_range_succ, show 2 * m + 1 + 1 = 2 * (m + 1) by omega]

private theorem pairing_convolution_term (m j : ℕ) (hj : j ≤ m) (d : ℝ) :
    ((2 * m).choose (2 * j) : ℝ) *
        (((2 * j).factorial : ℝ) / (4 ^ j * (j.factorial : ℝ))) *
        (((2 * (m - j)).factorial : ℝ) / (4 ^ (m - j) * ((m - j).factorial : ℝ))) *
        d ^ (m - j) =
      (((2 * m).factorial : ℝ) / (4 ^ m * (m.factorial : ℝ))) *
        (m.choose j : ℝ) * d ^ (m - j) := by
  have hsub : 2 * m - 2 * j = 2 * (m - j) := by omega
  have hbig : ((2 * m).choose (2 * j) : ℝ) * ((2 * j).factorial : ℝ) *
      ((2 * (m - j)).factorial : ℝ) = ((2 * m).factorial : ℝ) := by
    exact_mod_cast hsub ▸ Nat.choose_mul_factorial_mul_factorial (show 2 * j ≤ 2 * m by omega)
  have hsmall : (m.choose j : ℝ) * (j.factorial : ℝ) * ((m - j).factorial : ℝ) =
      (m.factorial : ℝ) := by exact_mod_cast Nat.choose_mul_factorial_mul_factorial hj
  have hpow : (4 : ℝ) ^ m = 4 ^ j * 4 ^ (m - j) := by
    rw [← pow_add, Nat.add_sub_of_le hj]
  have hj0 : (j.factorial : ℝ) ≠ 0 := by positivity
  have hs0 : ((m - j).factorial : ℝ) ≠ 0 := by positivity
  have hm0 : (m.factorial : ℝ) ≠ 0 := by positivity
  apply mul_right_cancel₀ (pow_ne_zero m (show (4 : ℝ) ≠ 0 by norm_num))
  rw [hpow]
  field_simp
  nlinarith [congrArg (fun a : ℝ => a * (m.factorial : ℝ) * d ^ (m - j)) hbig,
    congrArg (fun a : ℝ => a * ((2 * m).factorial : ℝ) * d ^ (m - j)) hsmall]

private theorem integral_pi_sum_cos_pow_even_le (d m : ℕ) :
    (∫ k : Fin d → ℝ, (∑ j, cos (k j)) ^ (2 * m)
      ∂Measure.pi (fun _ => volume.restrict (Ioo (-π) π))) ≤
      (2 * π) ^ d * (((2 * m).factorial : ℝ) / (4 ^ m * (m.factorial : ℝ))) *
        (d : ℝ) ^ m := by
  induction d generalizing m with
  | zero =>
    cases m with
    | zero => simpa using (integral_pi_sum_cos_pow_zero 0).le
    | succ m => simp
  | succ d ih =>
    rw [integral_pi_sum_cos_pow_succ]
    rw [sum_range_even_of_odd_eq_zero _ (fun j => by
      rw [integral_Ioo_cos_pow_odd, mul_zero, zero_mul])]
    calc
      _ ≤ ∑ j ∈ range (m + 1),
          ((2 * m).choose (2 * j) : ℝ) *
            ((2 * π) * (((2 * j).factorial : ℝ) / (4 ^ j * (j.factorial : ℝ)))) *
            ((2 * π) ^ d *
              (((2 * (m - j)).factorial : ℝ) /
                (4 ^ (m - j) * ((m - j).factorial : ℝ))) * (d : ℝ) ^ (m - j)) := by
        apply sum_le_sum
        intro j hj
        have hjm : j ≤ m := Nat.le_of_lt_succ (mem_range.mp hj)
        rw [show 2 * m - 2 * j = 2 * (m - j) by omega]
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left (integral_Ioo_cos_pow_even_le j) (by positivity)
        · exact ih (m - j)
        · apply integral_nonneg
          intro k
          change 0 ≤ (∑ l, cos (k l)) ^ (2 * (m - j))
          rw [mul_comm 2, pow_mul]
          exact sq_nonneg _
        · positivity
      _ = ∑ j ∈ range (m + 1),
          (2 * π) ^ (d + 1) *
            (((2 * m).factorial : ℝ) / (4 ^ m * (m.factorial : ℝ))) *
            ((m.choose j : ℝ) * (d : ℝ) ^ (m - j)) := by
        apply sum_congr rfl
        intro j hj
        have hjm : j ≤ m := Nat.le_of_lt_succ (mem_range.mp hj)
        have h := pairing_convolution_term m j hjm (d : ℝ)
        rw [pow_succ]
        nlinarith [congrArg (fun a : ℝ => (2 * π) ^ d * (2 * π) * a) h]
      _ = _ := by
        rw [← mul_sum]
        have hbin : (∑ j ∈ range (m + 1), (m.choose j : ℝ) * (d : ℝ) ^ (m - j)) =
            ((d : ℝ) + 1) ^ m := by
          simpa [mul_comm, add_comm] using (add_pow (1 : ℝ) (d : ℝ) m).symm
        rw [hbin]
        simp

/-- The sum of `d` coordinate cosines has every even moment bounded by the
Gaussian pairing moment of variance `d / 2`, with unnormalized torus volume. -/
theorem integral_sum_cos_pow_even_le (d m : ℕ) :
    (∫ k in ball (0 : Fin d → ℝ) π, (∑ j, cos (k j)) ^ (2 * m)) ≤
      (2 * π) ^ d * (((2 * m).factorial : ℝ) / (4 ^ m * (m.factorial : ℝ))) *
        (d : ℝ) ^ m := by
  rw [volume_restrict_pi_ball_eq_pi_Ioo]
  exact integral_pi_sum_cos_pow_even_le d m

/-- The normalized even nearest-neighbour Fourier moment obeys the factorial
pairing bound `(2m)! / (m! (4d)^m)` in every positive dimension. -/
theorem integral_nearestNeighborSymbol_pow_even_le {d : ℕ} (hd : 0 < d) (m : ℕ) :
    ((2 * π) ^ d)⁻¹ *
      (∫ k in ball (0 : Fin d → ℝ) π, ((d : ℝ)⁻¹ * ∑ j, cos (k j)) ^ (2 * m)) ≤
      ((2 * m).factorial : ℝ) / ((m.factorial : ℝ) * (4 * (d : ℝ)) ^ m) := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hp0 : (2 * π) ^ d ≠ 0 := by positivity
  rw [show (fun k : Fin d → ℝ => ((d : ℝ)⁻¹ * ∑ j, cos (k j)) ^ (2 * m)) =
      (fun k => (d : ℝ)⁻¹ ^ (2 * m) * (∑ j, cos (k j)) ^ (2 * m)) by
        ext k
        rw [mul_pow], integral_const_mul]
  calc
    _ ≤ ((2 * π) ^ d)⁻¹ * ((d : ℝ)⁻¹ ^ (2 * m) *
        ((2 * π) ^ d *
          (((2 * m).factorial : ℝ) / (4 ^ m * (m.factorial : ℝ))) * (d : ℝ) ^ m)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (integral_sum_cos_pow_even_le d m) (by positivity))
        (by positivity)
    _ = _ := by
      have hdpow : (d : ℝ) ^ (2 * m) = ((d : ℝ) ^ m) ^ 2 := by
        rw [mul_comm 2 m, pow_mul]
      simp only [inv_pow, mul_pow, hdpow]
      field_simp

end PercLib.Analysis
