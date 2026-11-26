/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New proofs for this project; no upstream Lean code is copied.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.Normed.Group.Int
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Cosine weights on the integer lattice

The cosine deficit of a lattice Fourier phase is bounded by the squared Euclidean length
of the lattice point times the sum of the coordinate cosine deficits. The estimate holds
for every real frequency, without choosing a torus representative.

## Main results

* `one_sub_cos_sum_mul_intCast_le`: the bound retaining the sum of coordinate squares.
* `one_sub_cos_sum_mul_intCast_le_norm_sq`: its sup-norm form on `Fin d → ℤ`.

The first bound has coefficient one; a single nonzero coordinate attains equality.
-/

@[expose] public section

open Real

namespace PercLib.Analysis

/-- Integer multiplication can increase the absolute sine by at most the absolute
value of the multiplier. -/
theorem abs_sin_int_mul_le (n : ℤ) (t : ℝ) :
    |sin ((n : ℝ) * t)| ≤ |(n : ℝ)| * |sin t| := by
  have hnat (m : ℕ) : |sin ((m : ℝ) * t)| ≤ (m : ℝ) * |sin t| := by
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using
      abs_sin_sum_le (Finset.range m) (fun _ => t)
  rcases n.eq_nat_or_neg with ⟨m, rfl | rfl⟩
  · simpa only [Int.cast_natCast, abs_of_nonneg (show (0 : ℝ) ≤ m from Nat.cast_nonneg m)]
      using hnat m
  · simpa only [Int.cast_neg, Int.cast_natCast, neg_mul, sin_neg, abs_neg,
      abs_of_nonneg (show (0 : ℝ) ≤ m from Nat.cast_nonneg m)] using hnat m

/-- The cosine deficit of an integer lattice phase is controlled by the squared
Euclidean length of the lattice point and the sum of coordinate deficits. -/
theorem one_sub_cos_sum_mul_intCast_le {ι : Type*} [Fintype ι]
    (x : ι → ℤ) (k : ι → ℝ) :
    1 - cos (∑ i, k i * (x i : ℝ)) ≤
      (∑ i, (x i : ℝ) ^ 2) * ∑ i, (1 - cos (k i)) := by
  have hphase : (∑ i, k i * (x i : ℝ)) / 2 =
      ∑ i, (x i : ℝ) * (k i / 2) := by
    rw [div_eq_mul_inv, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hsum : |sin ((∑ i, k i * (x i : ℝ)) / 2)| ≤
      ∑ i, |(x i : ℝ)| * |sin (k i / 2)| := by
    rw [hphase]
    refine (abs_sin_sum_le Finset.univ (fun i => (x i : ℝ) * (k i / 2))).trans ?_
    exact Finset.sum_le_sum fun i _ => abs_sin_int_mul_le (x i) (k i / 2)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i => |(x i : ℝ)|) (fun i => |sin (k i / 2)|)
  simp only [sq_abs] at hcs
  have hsquares := (pow_le_pow_left₀ (abs_nonneg _) hsum 2).trans hcs
  rw [sq_abs] at hsquares
  have hhalf (t : ℝ) : 2 * sin (t / 2) ^ 2 = 1 - cos t := by
    have h := sin_sq_eq_half_sub (x := t / 2)
    rw [show 2 * (t / 2) = t by ring] at h
    linarith
  have hdeficits : 2 * ∑ i, sin (k i / 2) ^ 2 = ∑ i, (1 - cos (k i)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => hhalf (k i)
  calc
    1 - cos (∑ i, k i * (x i : ℝ)) =
        2 * sin ((∑ i, k i * (x i : ℝ)) / 2) ^ 2 := (hhalf _).symm
    _ ≤ 2 * ((∑ i, (x i : ℝ) ^ 2) * ∑ i, sin (k i / 2) ^ 2) := by
      linarith [hsquares]
    _ = (∑ i, (x i : ℝ) ^ 2) * ∑ i, (1 - cos (k i)) := by
      rw [← hdeficits]
      ring

/-- The sup-norm version retains one factor of the dimension in front of the sum
of coordinate deficits, or two factors in front of their average. -/
theorem one_sub_cos_sum_mul_intCast_le_norm_sq {d : ℕ}
    (x : Fin d → ℤ) (k : Fin d → ℝ) :
    1 - cos (∑ i, k i * (x i : ℝ)) ≤
      (d : ℝ) * ‖x‖ ^ 2 * ∑ i, (1 - cos (k i)) := by
  have hsum : (∑ i, (x i : ℝ) ^ 2) ≤ (d : ℝ) * ‖x‖ ^ 2 := by
    calc
      _ ≤ ∑ _i : Fin d, ‖x‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        rw [← sq_abs (x i : ℝ), ← Int.norm_eq_abs]
        exact pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm x i) 2
      _ = _ := by simp
  exact (one_sub_cos_sum_mul_intCast_le x k).trans
    (mul_le_mul_of_nonneg_right hsum
      (Finset.sum_nonneg fun i _ => sub_nonneg.mpr (cos_le_one (k i))))

/-- A nonzero one-dimensional phase attains the coefficient one in the Euclidean bound. -/
example :
    1 - cos (∑ _i : Fin 1, Real.pi * ((1 : ℤ) : ℝ)) =
      (∑ _i : Fin 1, ((1 : ℤ) : ℝ) ^ 2) * ∑ _i : Fin 1, (1 - cos Real.pi) ∧
      0 < 1 - cos (∑ _i : Fin 1, Real.pi * ((1 : ℤ) : ℝ)) := by
  norm_num

end PercLib.Analysis
