/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Taylor expansions of real powers along the integers. New for this project against pinned
mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; no upstream code is copied.
Mathematical reference: the binomial series `(1 + u)^a = ∑ₖ (a choose k) uᵏ` for `|u| < 1`.
-/
module

public import Mathlib.Analysis.Analytic.Binomial
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Expansions of `(R ± 1)^(-s)` along the integers

For real `s` and integers `R → ∞`,
`(R - 1)^(-s) - R^(-s) = s R^(-s-1) + O(R^(-s-2))` and
`((R - 1)^(-s) + (R + 1)^(-s)) / 2 - R^(-s) = s(s+1)/2 R^(-s-2) + O(R^(-s-4))`.
A sequence with a nonzero leading term `c R^a` is not `O(R^r)` for any `r < a`.

## Main results

* `isBigO_one_add_rpow_sub_sum`: the binomial series with a remainder `O(|u|^n)` at `0`.
* `isLittleO_natCast_rpow`: `R^b = o(R^a)` for `b < a`.
* `not_isBigO_natCast_rpow_of_isBigO_sub`: a nonzero leading term obstructs a smaller power
  bound.
* `isBigO_natCast_sub_one_rpow_neg_sub`: the first-order expansion of `(R - 1)^(-s)`.
* `isBigO_natCast_sub_one_add_add_one_rpow_neg_sub`: the second-order expansion of the
  symmetric average of `(R ∓ 1)^(-s)`.
-/

@[expose] public section

noncomputable section

open Filter Asymptotics Topology

namespace PercLib.Analysis

/-- **Binomial series with remainder.** `(1 + u)^a = ∑_{k<n} (a choose k) uᵏ + O(|u|ⁿ)` as
`u → 0`. -/
theorem isBigO_one_add_rpow_sub_sum (a : ℝ) (n : ℕ) :
    (fun u : ℝ => (1 + u) ^ a - ∑ k ∈ Finset.range n, Ring.choose a k * u ^ k) =O[𝓝 0]
      fun u => |u| ^ n := by
  have h := (Real.one_add_rpow_hasFPowerSeriesAt_zero (a := a)).isBigO_sub_partialSum_pow n
  simpa [FormalMultilinearSeries.partialSum, binomialSeries,
    FormalMultilinearSeries.coeff_ofScalars, mul_comm] using h

/-- `(a choose 2) = a (a - 1) / 2`. -/
theorem Real.choose_two (a : ℝ) : Ring.choose a 2 = a * (a - 1) / 2 := by
  rw [Ring.choose_eq_smul]
  simp [descPochhammer_succ_right, Polynomial.smeval_mul, Polynomial.smeval_X,
    Polynomial.smeval_sub, smul_eq_mul]
  ring

/-- `R^b = o(R^a)` along the integers for `b < a`. -/
theorem isLittleO_natCast_rpow {a b : ℝ} (hba : b < a) :
    (fun R : ℕ => (R : ℝ) ^ b) =o[atTop] fun R : ℕ => (R : ℝ) ^ a := by
  have ht : Tendsto (fun R : ℕ => (R : ℝ) ^ (-(a - b))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
  have h := (isBigO_refl (fun R : ℕ => (R : ℝ) ^ a) atTop).mul_isLittleO
    ((isLittleO_one_iff ℝ).2 ht)
  refine (h.congr' ?_ ?_)
  · filter_upwards [eventually_gt_atTop 0] with R hR
    have hR' : (0 : ℝ) < R := by exact_mod_cast hR
    rw [← Real.rpow_add hR']
    congr 1
    ring
  · exact Eventually.of_forall fun R => mul_one _

/-- `R^b = O(R^a)` along the integers for `b ≤ a`. -/
theorem isBigO_natCast_rpow {a b : ℝ} (hba : b ≤ a) :
    (fun R : ℕ => (R : ℝ) ^ b) =O[atTop] fun R : ℕ => (R : ℝ) ^ a := by
  rcases hba.eq_or_lt with rfl | h
  · exact isBigO_refl _ _
  · exact (isLittleO_natCast_rpow h).isBigO

/-- **A leading term obstructs smaller bounds.** If `X R = c R^a + O(R^b)` with `c ≠ 0` and
`b < a`, then `X` is not `O(R^r)` for any `r < a`. -/
theorem not_isBigO_natCast_rpow_of_isBigO_sub {X : ℕ → ℝ} {c a b : ℝ} (hc : c ≠ 0)
    (hba : b < a) (hX : (fun R => X R - c * (R : ℝ) ^ a) =O[atTop] fun R : ℕ => (R : ℝ) ^ b)
    {r : ℝ} (hra : r < a) : ¬ X =O[atTop] fun R : ℕ => (R : ℝ) ^ r := by
  intro h
  have h1 : X =O[atTop] fun R : ℕ => (R : ℝ) ^ max b r :=
    h.trans (isBigO_natCast_rpow (le_max_right b r))
  have h2 := hX.trans (isBigO_natCast_rpow (le_max_left b r))
  have h3 : (fun R : ℕ => c * (R : ℝ) ^ a) =O[atTop] fun R : ℕ => (R : ℝ) ^ max b r :=
    (h1.sub h2).congr_left fun R => by ring
  have h4 := h3.trans_isLittleO (isLittleO_natCast_rpow (max_lt hba hra))
  rw [isLittleO_const_mul_left_iff hc] at h4
  refine isLittleO_irrefl' ?_ h4
  refine (eventually_gt_atTop 0).frequently.mono fun R hR => ?_
  have hR' : (0 : ℝ) < R := by exact_mod_cast hR
  exact norm_ne_zero_iff.2 (Real.rpow_pos_of_pos hR' _).ne'

/-- For `R > 0`, `R^(-s) (1 + u/R)^(-s) = (R + u)^(-s)` when `R + u ≥ 0`. -/
theorem rpow_neg_mul_one_add_div {R u : ℝ} (hR : 0 < R) (hRu : 0 ≤ R + u) (s : ℝ) :
    R ^ (-s) * (1 + u / R) ^ (-s) = (R + u) ^ (-s) := by
  have h1 : 0 ≤ 1 + u / R := by
    have : 1 + u / R = (R + u) / R := by field_simp
    rw [this]
    positivity
  rw [← Real.mul_rpow hR.le h1]
  congr 1
  field_simp

/-- **First-order expansion.** `(R - 1)^(-s) - R^(-s) = s R^(-s-1) + O(R^(-s-2))` along the
integers. -/
theorem isBigO_natCast_sub_one_rpow_neg_sub (s : ℝ) :
    (fun R : ℕ => ((R : ℝ) - 1) ^ (-s) - (R : ℝ) ^ (-s) - s * (R : ℝ) ^ (-s - 1)) =O[atTop]
      fun R : ℕ => (R : ℝ) ^ (-s - 2) := by
  have hu : Tendsto (fun R : ℕ => -1 / (R : ℝ)) atTop (𝓝 0) := by
    simpa [neg_div] using (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).neg
  have h := (isBigO_refl (fun R : ℕ => (R : ℝ) ^ (-s)) atTop).mul
    ((isBigO_one_add_rpow_sub_sum (-s) 2).comp_tendsto hu)
  refine h.congr' ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with R hR
    have hR' : (1 : ℝ) ≤ R := by exact_mod_cast hR
    have hR0 : (0 : ℝ) < R := by linarith
    simp only [Function.comp_apply, Finset.sum_range_succ, Finset.sum_range_zero,
      Ring.choose_zero_right, Ring.choose_one_right, pow_zero, pow_one]
    rw [mul_sub, rpow_neg_mul_one_add_div hR0 (by linarith), Real.rpow_sub_one hR0.ne']
    field_simp
    ring_nf
  · filter_upwards [eventually_gt_atTop 0] with R hR
    have hR' : (0 : ℝ) < R := by exact_mod_cast hR
    simp only [Function.comp_apply]
    rw [abs_div, abs_neg, abs_one, abs_of_pos hR', one_div, inv_pow, sub_eq_add_neg,
      Real.rpow_add hR', Real.rpow_neg hR'.le 2, Real.rpow_two]

/-- **Second-order expansion of the symmetric average.**
`((R - 1)^(-s) + (R + 1)^(-s)) / 2 - R^(-s) = s (s + 1) / 2 R^(-s-2) + O(R^(-s-4))` along the
integers. -/
theorem isBigO_natCast_sub_one_add_add_one_rpow_neg_sub (s : ℝ) :
    (fun R : ℕ => (((R : ℝ) - 1) ^ (-s) + ((R : ℝ) + 1) ^ (-s)) / 2 - (R : ℝ) ^ (-s) -
        s * (s + 1) / 2 * (R : ℝ) ^ (-s - 2)) =O[atTop]
      fun R : ℕ => (R : ℝ) ^ (-s - 4) := by
  have hu : Tendsto (fun R : ℕ => 1 / (R : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hv : Tendsto (fun R : ℕ => -1 / (R : ℝ)) atTop (𝓝 0) := by
    simpa [neg_div] using hu.neg
  have hT := isBigO_one_add_rpow_sub_sum (-s) 4
  have hA := hT.comp_tendsto hu
  have hB : _ =O[atTop] fun R : ℕ => |1 / (R : ℝ)| ^ 4 :=
    (hT.comp_tendsto hv).congr_right fun R => by simp [neg_div, abs_neg]
  have hsum := (hB.add hA).const_mul_left (1 / 2)
  have h := (isBigO_refl (fun R : ℕ => (R : ℝ) ^ (-s)) atTop).mul hsum
  refine h.congr' ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with R hR
    have hR' : (1 : ℝ) ≤ R := by exact_mod_cast hR
    have hR0 : (0 : ℝ) < R := by linarith
    simp only [Function.comp_apply, Finset.sum_range_succ, Finset.sum_range_zero,
      Ring.choose_zero_right, Ring.choose_one_right, Real.choose_two, pow_zero, pow_one]
    have e1 := rpow_neg_mul_one_add_div hR0 (u := -1) (by linarith) s
    have e2 := rpow_neg_mul_one_add_div hR0 (u := 1) (by linarith) s
    have e3 : (R : ℝ) ^ (-s - 2) = (R : ℝ) ^ (-s) / (R : ℝ) ^ 2 := by
      rw [sub_eq_add_neg, Real.rpow_add hR0, Real.rpow_neg hR0.le 2, Real.rpow_two, div_eq_mul_inv]
    rw [show (R : ℝ) - 1 = R + -1 by ring, ← e1, ← e2, e3]
    field_simp
    ring
  · filter_upwards [eventually_gt_atTop 0] with R hR
    have hR' : (0 : ℝ) < R := by exact_mod_cast hR
    rw [abs_of_pos (by positivity), sub_eq_add_neg, Real.rpow_add hR', Real.rpow_neg hR'.le 4]
    norm_num [div_pow]

end PercLib.Analysis
