/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New proofs for this project; no upstream Lean code is copied.
Mathematical reference: the random-walk comparisons in Chapter 8 of
Heydenreich and van der Hofstad (2017).
-/
module

public import PercLib.Analysis.CosineReciprocal

/-!
# Second differences of random-walk reciprocals

A nonnegative probability kernel and a parameter in `[0,1)` give positive reciprocal
denominators at every phase. Normalization converts cosine moments into the deficit
of the cosine transform, so the signed-kernel estimate applies without assumed
Fourier-difference bounds.

## Main results

* `walk_cosine_reciprocal_pos`: positivity of the actual reciprocal.
* `abs_walk_cosine_reciprocal_second_difference_le_mul`: the difference estimate retaining
  the walk parameter as an additional factor.
* `abs_walk_cosine_reciprocal_second_difference_le`: the parameter-independent form.
-/

@[expose] public section

open Real

namespace PercLib.Analysis

variable {ι : Type*} {a : ι → ℝ}

/-- For a normalized real kernel, the cosine moment is exactly its transform deficit. -/
theorem tsum_mul_one_sub_cos_eq_one_sub_tsum_mul_cos (ha : HasSum a 1) (t : ι → ℝ) :
    (∑' i, a i * (1 - cos (t i))) = 1 - ∑' i, a i * cos (t i) := by
  simp_rw [mul_sub, mul_one]
  rw [ha.summable.tsum_sub (summable_mul_cos ha.summable t), ha.tsum_eq]

/-- The cosine transform of a nonnegative probability kernel is at most one. -/
theorem tsum_mul_cos_le_one_of_hasSum (ha : HasSum a 1) (ha0 : ∀ i, 0 ≤ a i)
    (t : ι → ℝ) : (∑' i, a i * cos (t i)) ≤ 1 := by
  rw [← ha.tsum_eq]
  exact (summable_mul_cos ha.summable t).tsum_le_tsum
    (fun i => mul_le_of_le_one_right (ha0 i) (cos_le_one _)) ha.summable

/-- Every cosine phase of a nonnegative probability kernel has a positive walk reciprocal
when the walk parameter is nonnegative and less than one. -/
theorem walk_cosine_reciprocal_pos (ha : HasSum a 1) (ha0 : ∀ i, 0 ≤ a i)
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam < 1) (t : ι → ℝ) :
    0 < (1 - lam * (∑' i, a i * cos (t i)))⁻¹ := by
  apply inv_pos.mpr
  have h := mul_le_mul_of_nonneg_left (tsum_mul_cos_le_one_of_hasSum ha ha0 t) hlam0
  nlinarith

/-- The random-walk reciprocal difference estimate with its extra parameter factor.
The cosine moments and reciprocal signs are derived from the probability kernel. -/
theorem abs_walk_cosine_reciprocal_second_difference_le_mul
    (ha : HasSum a 1) (ha0 : ∀ i, 0 ≤ a i) {lam : ℝ}
    (hlam0 : 0 ≤ lam) (hlam1 : lam < 1) (l k : ι → ℝ) :
    let Cm := (1 - lam * (∑' i, a i * cos (l i - k i)))⁻¹
    let C0 := (1 - lam * (∑' i, a i * cos (l i)))⁻¹
    let Cp := (1 - lam * (∑' i, a i * cos (l i + k i)))⁻¹
    let gk := 1 - ∑' i, a i * cos (k i)
    |Cm + Cp - 2 * C0| ≤ lam * gk * (C0 * Cm + C0 * Cp + 8 * Cm * Cp) := by
  let S (t : ι → ℝ) : ℝ := ∑' i, a i * cos (t i)
  let C (t : ι → ℝ) : ℝ := (1 - lam * S t)⁻¹
  let g (t : ι → ℝ) : ℝ := 1 - S t
  let m : ι → ℝ := fun i => l i - k i
  let p : ι → ℝ := fun i => l i + k i
  change |C m + C p - 2 * C l| ≤ lam * g k * (C l * C m + C l * C p + 8 * C m * C p)
  have hpos (t : ι → ℝ) : 0 < C t := walk_cosine_reciprocal_pos ha ha0 hlam0 hlam1 t
  have hden (t : ι → ℝ) : 1 - lam * S t ≠ 0 := (inv_pos.mp (hpos t)).ne'
  have hg (t : ι → ℝ) : 0 ≤ g t :=
    sub_nonneg.mpr (tsum_mul_cos_le_one_of_hasSum ha ha0 t)
  have hscaled (t : ι → ℝ) : (∑' i, (lam * a i) * cos (t i)) = lam * S t := by
    simp only [mul_assoc, tsum_mul_left, S]
  have hmoment (t : ι → ℝ) : (∑' i, |lam * a i| * (1 - cos (t i))) = lam * g t := by
    calc
      _ = ∑' i, lam * (a i * (1 - cos (t i))) := by
        apply tsum_congr
        intro i
        rw [abs_of_nonneg (mul_nonneg hlam0 (ha0 i)), mul_assoc]
      _ = _ := by
        rw [tsum_mul_left, tsum_mul_one_sub_cos_eq_one_sub_tsum_mul_cos ha t]
  have hraw := abs_cosine_reciprocal_second_difference_le (ha.summable.mul_left lam) l k
    (by rw [hscaled]; exact hden m) (by rw [hscaled]; exact hden l)
    (by rw [hscaled]; exact hden p)
  dsimp only at hraw
  simp only [hscaled, hmoment] at hraw
  change |C m + C p - 2 * C l| ≤
    (|C m| + |C p|) * |C l| * (lam * g k) +
      8 * |C m * C l * C p| * (lam * g l) * (lam * g k) at hraw
  rw [abs_of_pos (hpos m), abs_of_pos (hpos p), abs_of_pos (hpos l),
    abs_of_pos (mul_pos (mul_pos (hpos m) (hpos l)) (hpos p))] at hraw
  have hcancel : C l * (1 - lam * S l) = 1 := inv_mul_cancel₀ (hden l)
  have hsmall : C l * (lam * g l) ≤ 1 := by
    have hle : lam * g l ≤ 1 - lam * S l := by dsimp only [g]; linarith
    exact (mul_le_mul_of_nonneg_left hle (hpos l).le).trans_eq hcancel
  have hterm : 8 * C m * C p * (C l * (lam * g l)) ≤ 8 * C m * C p :=
    mul_le_of_le_one_right
      (mul_nonneg (mul_nonneg (by norm_num) (hpos m).le) (hpos p).le) hsmall
  calc
    _ ≤ (C m + C p) * C l * (lam * g k) +
        8 * (C m * C l * C p) * (lam * g l) * (lam * g k) := hraw
    _ = lam * g k *
        (C l * C m + C l * C p + 8 * C m * C p * (C l * (lam * g l))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add le_rfl hterm)
      (mul_nonneg hlam0 (hg k))

/-- The usual three-term bound for the actual random-walk reciprocal. -/
theorem abs_walk_cosine_reciprocal_second_difference_le
    (ha : HasSum a 1) (ha0 : ∀ i, 0 ≤ a i) {lam : ℝ}
    (hlam0 : 0 ≤ lam) (hlam1 : lam < 1) (l k : ι → ℝ) :
    let Cm := (1 - lam * (∑' i, a i * cos (l i - k i)))⁻¹
    let C0 := (1 - lam * (∑' i, a i * cos (l i)))⁻¹
    let Cp := (1 - lam * (∑' i, a i * cos (l i + k i)))⁻¹
    let gk := 1 - ∑' i, a i * cos (k i)
    |Cm + Cp - 2 * C0| ≤ gk * (C0 * Cm + C0 * Cp + 8 * Cm * Cp) := by
  dsimp only
  have hm := (walk_cosine_reciprocal_pos ha ha0 hlam0 hlam1 (fun i => l i - k i)).le
  have h0 := (walk_cosine_reciprocal_pos ha ha0 hlam0 hlam1 l).le
  have hp := (walk_cosine_reciprocal_pos ha ha0 hlam0 hlam1 (fun i => l i + k i)).le
  have hg := sub_nonneg.mpr (tsum_mul_cos_le_one_of_hasSum ha ha0 k)
  refine (abs_walk_cosine_reciprocal_second_difference_le_mul ha ha0 hlam0 hlam1 l k).trans ?_
  exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_left hg hlam1.le) (by positivity)

end PercLib.Analysis
