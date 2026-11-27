/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New proofs for this project; no upstream Lean code is copied.
-/
module

public import PercLib.Percolation.Bond.Lace.Expansion.Infinite
public import PercLib.Analysis.CosineDifference

/-!
# Weighted absolute bounds for the canonical signed lace kernel

The nonnegative coefficient series controls the weighted absolute signed kernel.
The weight may be any nonnegative real function; finite unweighted coefficient
mass is not needed when the weighted mass itself is finite.

## Main results

* `summable_mul_laceSum_of_weightedCoefficientMass_ne_top`: weighted summability.
* `tsum_mul_abs_laceSum_le_weightedCoefficientMass`: domination by actual coefficients.
* `abs_laceSum_cosine_sub_mass_le_weightedCoefficientMass`: the actual transform variation.
-/

@[expose] public section
noncomputable section

open PercLib.Analysis
open scoped ENNReal

namespace PercLib.Percolation.Bond.Lace

variable {V : Type*}

/-- A finite weighted coefficient row controls the corresponding value of the
canonical signed kernel, including weights equal to zero. -/
theorem norm_mul_laceSum_le_weightedCoefficientMass
    (q : Sym2 V → unitInterval) (x y : V) (w : ℝ) (hw : 0 ≤ w)
    (hW : (∑' n : ℕ, ENNReal.ofReal w * laceCoefficient q n x y) ≠ ⊤) :
    ‖w * laceSum q x y‖ ≤
      (∑' n : ℕ, ENNReal.ofReal w * laceCoefficient q n x y).toReal := by
  have hnorm : Summable (fun n : ℕ =>
      ‖w * ((-1 : ℝ) ^ n * (laceCoefficient q n x y).toReal)‖) := by
    simpa only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
      Real.norm_eq_abs, abs_of_nonneg hw, abs_of_nonneg ENNReal.toReal_nonneg,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal hw] using ENNReal.summable_toReal hW
  calc
    _ = ‖∑' n : ℕ, w * ((-1 : ℝ) ^ n * (laceCoefficient q n x y).toReal)‖ := by
      rw [laceSum, tsum_mul_left]
    _ ≤ ∑' n : ℕ, ‖w * ((-1 : ℝ) ^ n * (laceCoefficient q n x y).toReal)‖ :=
      norm_tsum_le_tsum_norm hnorm
    _ = _ := by
      rw [ENNReal.tsum_toReal_eq (ENNReal.ne_top_of_tsum_ne_top hW)]
      apply tsum_congr
      intro n
      simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
        Real.norm_eq_abs, abs_of_nonneg hw, abs_of_nonneg ENNReal.toReal_nonneg,
        ENNReal.toReal_mul, ENNReal.toReal_ofReal hw]

/-- Finite weighted total coefficient mass implies summability of the weighted
canonical kernel, without a separate assumption on its unweighted mass. -/
theorem summable_mul_laceSum_of_weightedCoefficientMass_ne_top
    (q : Sym2 V → unitInterval) (x : V) (w : V → ℝ) (hw : ∀ y, 0 ≤ w y)
    (hW : (∑' n : ℕ, ∑' y, ENNReal.ofReal (w y) * laceCoefficient q n x y) ≠ ⊤) :
    Summable (fun y => w y * laceSum q x y) := by
  have hswap : (∑' y, ∑' n : ℕ, ENNReal.ofReal (w y) * laceCoefficient q n x y) ≠ ⊤ := by
    rwa [ENNReal.tsum_comm]
  exact (ENNReal.summable_toReal hswap).of_norm_bounded fun y =>
    norm_mul_laceSum_le_weightedCoefficientMass q x y (w y) (hw y)
      (ENNReal.ne_top_of_tsum_ne_top hswap y)

/-- The actual nonnegative weighted coefficient mass bounds the weighted absolute
mass of the infinite signed kernel. The constant is exactly one. -/
theorem tsum_mul_abs_laceSum_le_weightedCoefficientMass
    (q : Sym2 V → unitInterval) (x : V) (w : V → ℝ) (hw : ∀ y, 0 ≤ w y)
    (hW : (∑' n : ℕ, ∑' y, ENNReal.ofReal (w y) * laceCoefficient q n x y) ≠ ⊤) :
    (∑' y, w y * |laceSum q x y|) ≤
      (∑' n : ℕ, ∑' y, ENNReal.ofReal (w y) * laceCoefficient q n x y).toReal := by
  have hswap : (∑' y, ∑' n : ℕ, ENNReal.ofReal (w y) * laceCoefficient q n x y) ≠ ⊤ := by
    rwa [ENNReal.tsum_comm]
  have h := Summable.tsum_le_tsum
    (fun y => norm_mul_laceSum_le_weightedCoefficientMass q x y (w y) (hw y)
      (ENNReal.ne_top_of_tsum_ne_top hswap y))
    (summable_mul_laceSum_of_weightedCoefficientMass_ne_top q x w hw hW).norm
    (ENNReal.summable_toReal hswap)
  rw [← ENNReal.tsum_toReal_eq (ENNReal.ne_top_of_tsum_ne_top hswap),
    ENNReal.tsum_comm] at h
  simpa only [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hw _)] using h

/-- Every cosine-deficit weight has finite coefficient mass when the total
unweighted mass is finite, since its pointwise value lies between zero and two. -/
theorem cosine_weightedCoefficientMass_ne_top
    (q : Sym2 V → unitInterval) (x : V) (t : V → ℝ)
    (hmass : (∑' n : ℕ, ∑' y, laceCoefficient q n x y) ≠ ⊤) :
    (∑' n : ℕ, ∑' y,
      ENNReal.ofReal (1 - Real.cos (t y)) * laceCoefficient q n x y) ≠ ⊤ := by
  apply ne_top_of_le_ne_top
    (ENNReal.mul_ne_top (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) hmass)
  rw [← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro n
  rw [← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro y
  apply mul_le_mul' _ le_rfl
  exact (ENNReal.ofReal_le_ofReal
    (show 1 - Real.cos (t y) ≤ 2 by linarith [Real.neg_one_le_cos (t y)])).trans_eq
      (by norm_num)

/-- The variation of the actual signed lace cosine transform is bounded by
its actual nonnegative cosine-weighted coefficient series. -/
theorem abs_laceSum_cosine_sub_mass_le_weightedCoefficientMass
    (q : Sym2 V → unitInterval) (x : V) (t : V → ℝ)
    (hmass : (∑' n : ℕ, ∑' y, laceCoefficient q n x y) ≠ ⊤) :
    |(∑' y, laceSum q x y * Real.cos (t y)) - ∑' y, laceSum q x y| ≤
      (∑' n : ℕ, ∑' y,
        ENNReal.ofReal (1 - Real.cos (t y)) * laceCoefficient q n x y).toReal := by
  have hs := summable_laceSum q x hmass
  have hw (y : V) : 0 ≤ 1 - Real.cos (t y) := sub_nonneg.mpr (Real.cos_le_one _)
  have hW := cosine_weightedCoefficientMass_ne_top q x t hmass
  apply le_trans _ (tsum_mul_abs_laceSum_le_weightedCoefficientMass q x
    (fun y => 1 - Real.cos (t y)) hw hW)
  have hnorm := (hs.sub (summable_mul_cos hs t)).norm
  have h := norm_tsum_le_tsum_norm hnorm
  rw [hs.tsum_sub (summable_mul_cos hs t)] at h
  have he (y : V) : ‖laceSum q x y - laceSum q x y * Real.cos (t y)‖ =
      (1 - Real.cos (t y)) * |laceSum q x y| := by
    rw [← mul_one_sub, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (hw y), mul_comm]
  simp only [he, Real.norm_eq_abs] at h
  simpa only [abs_sub_comm] using h

end PercLib.Percolation.Bond.Lace
