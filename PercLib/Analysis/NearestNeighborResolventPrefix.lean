/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New proofs for this project; no upstream Lean code is copied.
Mathematical reference: factorial pairing bounds and geometric comparison for the
finite even-moment expansion of the nearest-neighbour inverse-sixth resolvent.
-/
module

public import PercLib.Analysis.NearestNeighborResolvent
public import Mathlib.Data.Nat.Choose.Bounds

/-!
# An explicit inverse-sixth moment prefix bound

The inverse-sixth binomial weight times the factorial pairing bound has an exact
rational successive-term ratio. Through order `⌊d / 2⌋`, this ratio is at most `3/5`
when `d ≥ 1000`. Keeping the first three terms separately gives an explicit prefix
bound whose leading correction is the exact second-moment contribution `21/(2d)`.

## Main results

* `sum_nearestNeighbor_pairing_inv_six_prefix_le`: the scalar factorial prefix bound.
* `sum_nearestNeighbor_moment_inv_six_prefix_le`: the bound for the actual moments.
-/

@[expose] public section

noncomputable section

open MeasureTheory Metric Set Real Finset

namespace PercLib.Analysis

/-- Beyond order 65, the inverse-sixth even binomial weight is bounded by one third
of the fifth power of the order. This bound uses the standard factorial denominator. -/
theorem choose_two_mul_add_five_le_pow_five {m : ℕ} (hm : 65 ≤ m) :
    ((2 * m + 5).choose 5 : ℝ) ≤ (m : ℝ) ^ 5 / 3 := by
  have hmR : (65 : ℝ) ≤ m := by exact_mod_cast hm
  have hlinear : (2 * m + 5 : ℝ) ≤ (27 / 13 : ℝ) * m := by linarith
  have hpower := pow_le_pow_left₀ (by positivity) hlinear 5
  have hcoeff : (27 / 13 : ℝ) ^ 5 / 120 ≤ 1 / 3 := by norm_num
  calc
    _ ≤ ((2 * m + 5 : ℕ) : ℝ) ^ 5 / ((5 : ℕ).factorial : ℝ) :=
      Nat.choose_le_pow_div 5 (2 * m + 5)
    _ ≤ ((27 / 13 : ℝ) * m) ^ 5 / 120 := by
      norm_num only [Nat.factorial, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat,
        Nat.cast_one, Nat.reduceMul]
      exact div_le_div_of_nonneg_right hpower (by norm_num)
    _ = ((27 / 13 : ℝ) ^ 5 / 120) * (m : ℝ) ^ 5 := by ring
    _ ≤ (1 / 3 : ℝ) * (m : ℝ) ^ 5 := mul_le_mul_of_nonneg_right hcoeff (by positivity)
    _ = _ := by ring

private theorem pairing_inv_six_eq_factorial {d : ℝ} (hd : 0 < d) (m : ℕ) :
    ((2 * m + 5).choose 5 : ℝ) *
        (((2 * m).factorial : ℝ) / ((m.factorial : ℝ) * (4 * d) ^ m)) =
      ((2 * m + 5).factorial : ℝ) / (120 * (m.factorial : ℝ) * (4 * d) ^ m) := by
  have hnat := Nat.choose_mul_factorial_mul_factorial (n := 2 * m + 5)
    (k := 5) (by omega)
  have hchoose : ((2 * m + 5).choose 5 : ℝ) * 120 * ((2 * m).factorial : ℝ) =
      ((2 * m + 5).factorial : ℝ) := by
    change (2 * m + 5).choose 5 * 120 * (2 * m).factorial =
      (2 * m + 5).factorial at hnat
    exact_mod_cast hnat
  rw [← hchoose]
  field_simp

private theorem pairing_inv_six_succ {d : ℝ} (hd : 0 < d) (m : ℕ) :
    ((2 * (m + 1) + 5).choose 5 : ℝ) *
        (((2 * (m + 1)).factorial : ℝ) /
          (((m + 1).factorial : ℝ) * (4 * d) ^ (m + 1))) =
      ((2 * m + 7 : ℝ) * (2 * m + 6) / (4 * d * (m + 1))) *
        (((2 * m + 5).choose 5 : ℝ) *
          (((2 * m).factorial : ℝ) / ((m.factorial : ℝ) * (4 * d) ^ m))) := by
  rw [pairing_inv_six_eq_factorial hd, pairing_inv_six_eq_factorial hd]
  rw [show 2 * (m + 1) + 5 = (2 * m + 5 + 1) + 1 by omega]
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat,
    Nat.cast_one, pow_succ]
  field_simp
  ring

private theorem pairing_inv_six_ratio_le {d m : ℕ} (hd : 1000 ≤ d)
    (hm : 2 ≤ m) (hmd : m ≤ d / 2) :
    (2 * m + 7 : ℝ) * (2 * m + 6) / (4 * (d : ℝ) * (m + 1)) ≤ 3 / 5 := by
  have hdR : (1000 : ℝ) ≤ d := by exact_mod_cast hd
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hmdR : (2 : ℝ) * m ≤ d := by
    exact_mod_cast (show 2 * m ≤ d by omega)
  have hprod₁ := mul_nonneg (sub_nonneg.mpr hmdR) (Nat.cast_nonneg (α := ℝ) m)
  have hprod₂ := mul_nonneg (show (0 : ℝ) ≤ d - 65 by linarith)
    (Nat.cast_nonneg (α := ℝ) m)
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/-- The factorial pairing majorant through order `⌊d/2⌋` has an explicit small
prefix bound, retaining the first three terms before the geometric comparison. -/
theorem sum_nearestNeighbor_pairing_inv_six_prefix_le {d : ℕ} (hd : 1000 ≤ d) :
    (∑ m ∈ range (d / 2 + 1), ((2 * m + 5).choose 5 : ℝ) *
      (((2 * m).factorial : ℝ) / ((m.factorial : ℝ) * (4 * (d : ℝ)) ^ m))) ≤
      1 + 21 / (2 * (d : ℝ)) + 189 / (2 * (d : ℝ) ^ 2) +
        (5 / 2 : ℝ) * (3465 / (4 * (d : ℝ) ^ 3)) := by
  let c : ℕ → ℝ := fun m => ((2 * m + 5).choose 5 : ℝ) *
    (((2 * m).factorial : ℝ) / ((m.factorial : ℝ) * (4 * (d : ℝ)) ^ m))
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hc_nonneg (m : ℕ) : 0 ≤ c m := by dsimp [c]; positivity
  have hstep (m : ℕ) (hm : 2 ≤ m) (hmd : m ≤ d / 2) :
      c (m + 1) ≤ (3 / 5 : ℝ) * c m := by
    rw [show c (m + 1) =
        ((2 * m + 7 : ℝ) * (2 * m + 6) / (4 * (d : ℝ) * (m + 1))) * c m from
      pairing_inv_six_succ hd0 m]
    exact mul_le_mul_of_nonneg_right (pairing_inv_six_ratio_le hd hm hmd) (hc_nonneg m)
  have hgeom (j : ℕ) (hj : j + 3 ≤ d / 2) : c (j + 3) ≤ (3 / 5 : ℝ) ^ j * c 3 := by
    apply le_geom (u := fun k => c (k + 3)) (by norm_num) j
    intro k hk
    exact hstep (k + 3) (by omega) (by omega)
  have hgeosum : (∑ j ∈ range (d / 2 - 2), (3 / 5 : ℝ) ^ j) ≤ 5 / 2 := by
    calc
      _ ≤ ∑' j : ℕ, (3 / 5 : ℝ) ^ j :=
        (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 3 / 5)
          (by norm_num)).sum_le_tsum _ (fun _ _ => by positivity)
      _ = _ := by rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; norm_num
  have htail : (∑ j ∈ range (d / 2 - 2), c (j + 3)) ≤ (5 / 2 : ℝ) * c 3 := by
    calc
      _ ≤ ∑ j ∈ range (d / 2 - 2), (3 / 5 : ℝ) ^ j * c 3 := by
        apply sum_le_sum
        intro j hj
        exact hgeom j (by have := mem_range.mp hj; omega)
      _ = (∑ j ∈ range (d / 2 - 2), (3 / 5 : ℝ) ^ j) * c 3 := (sum_mul _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hgeosum (hc_nonneg 3)
  have hc0 : c 0 = 1 := by norm_num [c]
  have hc1 : c 1 = 21 / (2 * (d : ℝ)) := by norm_num [c, Nat.choose]; ring
  have hc2 : c 2 = 189 / (2 * (d : ℝ) ^ 2) := by norm_num [c, Nat.choose]; ring
  have hc3 : c 3 = 3465 / (4 * (d : ℝ) ^ 3) := by norm_num [c, Nat.choose]; ring
  change (∑ m ∈ range (d / 2 + 1), c m) ≤ _
  rw [show d / 2 + 1 = 3 + (d / 2 - 2) by omega, sum_range_add]
  have hhead : (∑ m ∈ range 3, c m) =
      1 + 21 / (2 * (d : ℝ)) + 189 / (2 * (d : ℝ) ^ 2) := by
    simp only [sum_range_succ, sum_range_zero, zero_add, hc0, hc1, hc2]
  rw [hhead]
  have htail' : (∑ j ∈ range (d / 2 - 2), c (3 + j)) ≤
      (5 / 2 : ℝ) * (3465 / (4 * (d : ℝ) ^ 3)) := by
    simpa only [add_comm 3, hc3] using htail
  exact add_le_add le_rfl htail'

/-- The actual normalized inverse-sixth even-moment prefix satisfies the same
explicit bound; every moment is bounded by the proved factorial pairing theorem. -/
theorem sum_nearestNeighbor_moment_inv_six_prefix_le {d : ℕ} (hd : 1000 ≤ d) :
    (∑ m ∈ range (d / 2 + 1), ((2 * m + 5).choose 5 : ℝ) *
      (((2 * π) ^ d)⁻¹ * (∫ k in ball (0 : Fin d → ℝ) π,
        ((d : ℝ)⁻¹ * ∑ j, cos (k j)) ^ (2 * m)))) ≤
      1 + 21 / (2 * (d : ℝ)) + 189 / (2 * (d : ℝ) ^ 2) +
        (5 / 2 : ℝ) * (3465 / (4 * (d : ℝ) ^ 3)) := by
  apply le_trans _ (sum_nearestNeighbor_pairing_inv_six_prefix_le hd)
  apply sum_le_sum
  intro m _
  exact mul_le_mul_of_nonneg_left
    (integral_nearestNeighborSymbol_pow_even_le (show 0 < d by omega) m) (by positivity)

end PercLib.Analysis
