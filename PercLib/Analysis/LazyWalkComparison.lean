/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New proofs for this project; no upstream Lean code is copied.
Mathematical reference: the binomial time change from a walk to its half-lazy version.
-/
module

public import PercLib.Analysis.LazyWalkThresholds
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Data.Nat.Choose.Sum

/-!
# Exact comparison of lazy and nonlazy Green functions

Replacing a step kernel `p` by `(δ₀ + p) / 2` multiplies its Green function by two.
The comparison takes place in `ℝ≥0∞`, so it also covers recurrent walks and does not
require a probability normalization, symmetry, or finite Green functions. Its bubble
and triangle diagrams are multiplied by four and eight, respectively.

## Main results

* `tsum_choose_half_pow`: the normalized binomial column sums to two.
* `lazy_convPow_eq_sum_choose`: the binomial time-change formula.
* `tsum_lazy_convPow_eq_two_mul`: the Green-function comparison from the recursions.
* `tsum_lazy_step_convPow_eq_two_mul`: the comparison for the actual lazy step kernel.
* `tsum_sq_lazy_green_eq_four_mul`, `tsum_triangle_lazy_green_eq_eight_mul`:
  exact comparison of the two Green diagrams.
-/

@[expose] public section

noncomputable section

open Finset
open scoped ENNReal

namespace PercLib.Analysis

/-- Every column of the binomial time change has total weight two. -/
theorem tsum_choose_half_pow (k : ℕ) :
    ∑' n : ℕ, (2 : ℝ≥0∞)⁻¹ ^ n * (n.choose k : ℝ≥0∞) = 2 := by
  have hgeom := hasSum_choose_mul_geometric_of_norm_lt_one k
    (r := (1 / 2 : ℝ)) (by norm_num)
  have hvalue : (1 / (1 - (1 / 2 : ℝ)) ^ (k + 1)) * (1 / 2 : ℝ) ^ k = 2 := by
    rw [show 1 - (1 / 2 : ℝ) = 1 / 2 by norm_num, pow_succ]
    field_simp
  have hshift : HasSum
      (fun n : ℕ => (1 / 2 : ℝ) ^ (n + k) * ((n + k).choose k : ℝ)) 2 := by
    have hg := hgeom.mul_right ((1 / 2 : ℝ) ^ k)
    rw [hvalue] at hg
    simpa only [pow_add, mul_comm, mul_left_comm, mul_assoc] using hg
  have hhead : ∑ n ∈ range k, (1 / 2 : ℝ) ^ n * (n.choose k : ℝ) = 0 := by
    apply sum_eq_zero
    intro n hn
    simp [Nat.choose_eq_zero_of_lt (mem_range.mp hn)]
  have hfull : HasSum (fun n : ℕ => (1 / 2 : ℝ) ^ n * (n.choose k : ℝ)) 2 := by
    simpa only [hhead, zero_add] using
      (HasSum.sum_range_add (f := fun n : ℕ => (1 / 2 : ℝ) ^ n * (n.choose k : ℝ))
        (k := k) hshift)
  have h := congrArg ENNReal.ofReal hfull.tsum_eq
  rw [ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hfull.summable] at h
  simpa [ENNReal.ofReal_mul, ENNReal.ofReal_pow, ENNReal.ofReal_div_of_pos,
    ENNReal.inv_pow] using h

section ConvolutionPowers

variable {Γ : Type*} [AddGroup Γ]
  (p : Γ → ℝ≥0∞) (P L : ℕ → Γ → ℝ≥0∞)

/-- The half-lazy recursion is a binomial mixture of the original convolution powers.
Only equality of the two initial kernels is required. -/
theorem lazy_convPow_eq_sum_choose
    (h0 : ∀ x, L 0 x = P 0 x)
    (hP : ∀ n x, P (n + 1) x = ∑' y, P n y * p (-y + x))
    (hL : ∀ n x, L (n + 1) x =
      (2 : ℝ≥0∞)⁻¹ * L n x + (2 : ℝ≥0∞)⁻¹ * ∑' y, L n y * p (-y + x))
    (n : ℕ) (x : Γ) :
    L n x = (2 : ℝ≥0∞)⁻¹ ^ n * ∑ k ∈ range (n + 1), (n.choose k : ℝ≥0∞) * P k x := by
  induction n generalizing x with
  | zero => simp [h0]
  | succ n ih =>
    have hconv : (∑' y, L n y * p (-y + x)) =
        (2 : ℝ≥0∞)⁻¹ ^ n *
          ∑ k ∈ range (n + 1), (n.choose k : ℝ≥0∞) * P (k + 1) x := by
      simp_rw [ih, mul_assoc, sum_mul]
      rw [ENNReal.tsum_mul_left]
      rw [Summable.tsum_finsetSum fun _ _ => ENNReal.summable]
      congr 1
      apply sum_congr rfl
      intro k hk
      simp_rw [mul_assoc]
      rw [ENNReal.tsum_mul_left, ← hP]
    rw [hL, ih, hconv]
    rw [Finset.sum_choose_succ_mul (fun k _ => P k x) n, pow_succ]
    ring

/-- Inserting an independent hold of probability one half doubles every Green value,
including infinite values. -/
theorem tsum_lazy_convPow_eq_two_mul
    (h0 : ∀ x, L 0 x = P 0 x)
    (hP : ∀ n x, P (n + 1) x = ∑' y, P n y * p (-y + x))
    (hL : ∀ n x, L (n + 1) x =
      (2 : ℝ≥0∞)⁻¹ * L n x + (2 : ℝ≥0∞)⁻¹ * ∑' y, L n y * p (-y + x))
    (x : Γ) :
    ∑' n, L n x = 2 * ∑' n, P n x := by
  classical
  have hrow (n : ℕ) : L n x =
      ∑' k : ℕ, ((2 : ℝ≥0∞)⁻¹ ^ n * (n.choose k : ℝ≥0∞)) * P k x := by
    rw [lazy_convPow_eq_sum_choose p P L h0 hP hL, mul_sum]
    simp only [mul_assoc]
    symm
    apply tsum_eq_sum
    intro k hk
    have hnk : n < k := by simpa only [mem_range, Nat.lt_succ_iff, not_le] using hk
    simp [Nat.choose_eq_zero_of_lt hnk]
  simp_rw [hrow]
  rw [ENNReal.tsum_comm]
  simp_rw [ENNReal.tsum_mul_right, tsum_choose_half_pow]
  exact ENNReal.tsum_mul_left

open scoped Classical in
/-- The half-lazy step kernel `(δ₀ + p) / 2` has twice the Green function of `p`.
No normalization or transience assumption is needed. -/
theorem tsum_lazy_step_convPow_eq_two_mul
    (h0 : ∀ x, L 0 x = P 0 x)
    (hP : ∀ n x, P (n + 1) x = ∑' y, P n y * p (-y + x))
    (hL : ∀ n x, L (n + 1) x = ∑' y, L n y *
      ((2 : ℝ≥0∞)⁻¹ * (if -y + x = 0 then 1 else 0) + (2 : ℝ≥0∞)⁻¹ * p (-y + x)))
    (x : Γ) :
    ∑' n, L n x = 2 * ∑' n, P n x := by
  classical
  apply tsum_lazy_convPow_eq_two_mul p P L h0 hP
  intro n z
  rw [hL]
  simp_rw [mul_add, mul_left_comm (L n _) (2 : ℝ≥0∞)⁻¹]
  rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
  congr 1
  congr 1
  rw [tsum_eq_single z]
  · simp
  · intro y hy
    simp [neg_add_eq_zero, hy]

end ConvolutionPowers

section Diagrams

variable {Γ : Type*} (P L : ℕ → Γ → ℝ≥0∞)

/-- Doubling the Green function multiplies its bubble diagram by four. -/
theorem tsum_sq_lazy_green_eq_four_mul
    (hgreen : ∀ x, ∑' n, L n x = 2 * ∑' n, P n x) :
    ∑' x, (∑' n, L n x) ^ 2 = 4 * ∑' x, (∑' n, P n x) ^ 2 := by
  simp_rw [hgreen, mul_pow]
  norm_num only [show (2 : ℝ≥0∞) ^ 2 = 4 by norm_num]
  exact ENNReal.tsum_mul_left

/-- Doubling the Green function multiplies its triangle diagram by eight. -/
theorem tsum_triangle_lazy_green_eq_eight_mul [AddGroup Γ]
    (hgreen : ∀ x, ∑' n, L n x = 2 * ∑' n, P n x) :
    ∑' x, ∑' y, (∑' n, L n x) * (∑' n, L n (y - x)) * (∑' n, L n y) =
      8 * ∑' x, ∑' y, (∑' n, P n x) * (∑' n, P n (y - x)) * (∑' n, P n y) := by
  simp_rw [hgreen]
  calc
    _ = ∑' x, ∑' y, (8 : ℝ≥0∞) *
        ((∑' n, P n x) * (∑' n, P n (y - x)) * (∑' n, P n y)) := by
      apply tsum_congr
      intro x
      apply tsum_congr
      intro y
      ring
    _ = _ := by simp_rw [ENNReal.tsum_mul_left]

end Diagrams

end PercLib.Analysis
