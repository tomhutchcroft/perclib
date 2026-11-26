/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New for this project. No upstream proof is copied.
-/
module

public import PercLib.Models.LongRange.PowerLaw
public import PercLib.Percolation.Bond.Intensity

/-!
# Two-sided tail bounds for power-law-like kernels on `ℤ^d`

`ℤ^d` is `Fin d → ℤ` with the sup norm. A kernel `k : ℤ^d → ℝ` is compared with the power law
`‖z‖^(-(d+α))` off the origin, from above with a constant `C` and from below with a constant
`c`. For every real `R ≥ 1` the strict tail `∑_{‖z‖ > R} k(z)` (an `ℝ≥0∞`-sum of
`ENNReal.ofReal`) is then bounded by `2d·3^(d-1)·C·2^α/α · R^(-α)` from above and by
`2d·c/(α 2^α) · R^(-α)` from below.

## Main results

* `tsum_ite_lt_rpow_le`, `le_tsum_ite_lt_rpow`: `R^(-α)/(α 2^α) ≤ ∑_{n > R} n^(-(1+α)) ≤
  2^α R^(-α)/α` for real `R ≥ 1`.
* `tsum_ofReal_kernel_tail_le`, `le_tsum_ofReal_kernel_tail`: the two kernel tail bounds.
* `tsum_ofReal_kernel_lt_top`, `rowSum_kernel_lt_top`: finiteness of the kernel row.
* `tsum_intensityProfile_tail_le`: the probability row of bonds longer than `R` in the
  exponential intensity family is at most `β` times the kernel tail bound.
-/

@[expose] public section

noncomputable section

open Finset Filter Topology PercLib.Percolation.Bond
open scoped ENNReal NNReal

namespace PercLib.Models.LongRange

variable {d : ℕ}

/-! ### Strict tails of the `p`-series -/

/-- The reverse one-step inequality: `x^(-α) - (x+1)^(-α) ≤ α x^(-(1+α))` for `x > 0`. -/
theorem sub_rpow_le_mul (α : ℝ) (hα : 0 ≤ α) {x : ℝ} (hx : 0 < x) :
    x ^ (-α) - (x + 1) ^ (-α) ≤ α * x ^ (-(1 + α)) := by
  have hy0 : 0 < x + 1 := by linarith
  have hlog : Real.log ((x + 1) / x) ≤ 1 / x := by
    have h := Real.log_le_sub_one_of_pos (div_pos hy0 hx)
    have : (x + 1) / x - 1 = 1 / x := by field_simp; ring
    linarith
  have hexp : 1 - α / x ≤ ((x + 1) / x) ^ (-α) := by
    rw [Real.rpow_def_of_pos (div_pos hy0 hx)]
    have h := Real.add_one_le_exp (Real.log ((x + 1) / x) * -α)
    have : α * Real.log ((x + 1) / x) ≤ α * (1 / x) := mul_le_mul_of_nonneg_left hlog hα
    rw [mul_one_div] at this
    linarith
  have hy' : (x + 1) ^ (-α) = x ^ (-α) * ((x + 1) / x) ^ (-α) := by
    rw [Real.div_rpow hy0.le hx.le, ← mul_div_assoc, mul_comm, mul_div_assoc,
      div_self (Real.rpow_pos_of_pos hx _).ne', mul_one]
  have hx' : x ^ (-(1 + α)) = x ^ (-α) / x := by
    rw [show -(1 + α) = -α + -1 by ring, Real.rpow_add hx, Real.rpow_neg_one, div_eq_mul_inv]
  rw [hy', hx']
  have h0 : 0 < x ^ (-α) := Real.rpow_pos_of_pos hx _
  have : α * (x ^ (-α) / x) = x ^ (-α) * (α / x) := by ring
  nlinarith

/-- Upper bound for the strict tail of the `p`-series with `p = 1 + α > 1`:
`∑_{n > R} n^(-(1+α)) ≤ 2^α R^(-α)/α` for real `R ≥ 1`. -/
theorem tsum_ite_lt_rpow_le (α : ℝ) (hα : 0 < α) {R : ℝ} (hR : 1 ≤ R) :
    ∑' n : ℕ, ENNReal.ofReal (if R < n then (n : ℝ) ^ (-(1 + α)) else 0) ≤
      ENNReal.ofReal (2 ^ α / α * R ^ (-α)) := by
  set m := ⌊R⌋₊ with hm
  have hm1 : 1 ≤ m := Nat.le_floor (by exact_mod_cast hR)
  have hiff : ∀ n : ℕ, R < n ↔ m < n := fun n => (Nat.floor_lt (by linarith)).symm
  set F : ℕ → ℝ := fun n => ((max n m : ℕ) : ℝ) ^ (-α) with hF
  have hterm : ∀ n : ℕ, (if m < n + 1 then ((n + 1 : ℕ) : ℝ) ^ (-(1 + α)) else 0) ≤
      (F n - F (n + 1)) / α := by
    intro n
    split_ifs with h
    · have hmn : m ≤ n := by omega
      have hn : (0 : ℝ) < n := Nat.cast_pos.2 (by omega)
      simp only [hF, max_eq_left hmn, max_eq_left (by omega : m ≤ n + 1)]
      rw [le_div_iff₀ hα]
      have := mul_rpow_le_sub α hα hn
      push_cast
      linarith
    · have hmn : n + 1 ≤ m := by omega
      simp only [hF, max_eq_right hmn, max_eq_right (by omega : n ≤ m), sub_self, zero_div,
        le_refl]
  have hFnn : ∀ n, 0 ≤ F n := fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hmR : (m : ℝ) ^ (-α) ≤ 2 ^ α * R ^ (-α) := by
    have hmpos : (0 : ℝ) < m := Nat.cast_pos.2 hm1
    have h2m : R / 2 ≤ m := by
      have := Nat.lt_floor_add_one R
      have : (1 : ℝ) ≤ m := by exact_mod_cast hm1
      rw [← hm] at *
      linarith
    calc (m : ℝ) ^ (-α) ≤ (R / 2) ^ (-α) :=
          Real.rpow_le_rpow_of_nonpos (by linarith) h2m (by linarith)
      _ = 2 ^ α * R ^ (-α) := by
          rw [Real.div_rpow (by linarith) (by norm_num), Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),
            div_eq_mul_inv, inv_inv, mul_comm]
  refine ENNReal.tsum_le_of_sum_range_le fun N => ?_
  rw [← ENNReal.ofReal_sum_of_nonneg fun n _ => by
    split_ifs
    · exact Real.rpow_nonneg (Nat.cast_nonneg _) _
    · exact le_rfl]
  refine ENNReal.ofReal_le_ofReal ?_
  simp_rw [hiff]
  rcases N with _ | N
  · simp only [range_zero, sum_empty]
    positivity
  rw [sum_range_succ']
  simp only [Nat.cast_zero, Nat.not_lt_zero, ite_false, add_zero]
  calc ∑ n ∈ range N, (if m < n + 1 then ((n + 1 : ℕ) : ℝ) ^ (-(1 + α)) else 0)
      ≤ ∑ n ∈ range N, (F n - F (n + 1)) / α := sum_le_sum fun n _ => hterm n
    _ = (F 0 - F N) / α := by rw [← sum_div, sum_range_sub']
    _ ≤ F 0 / α := div_le_div_of_nonneg_right (by linarith [hFnn N]) hα.le
    _ ≤ 2 ^ α / α * R ^ (-α) := by
        simp only [hF, Nat.zero_max]
        rw [div_mul_eq_mul_div, mul_comm (2 ^ α)]
        exact div_le_div_of_nonneg_right (by linarith) hα.le

/-- Lower bound for the strict tail of the `p`-series with `p = 1 + α > 1`:
`R^(-α)/(α 2^α) ≤ ∑_{n > R} n^(-(1+α))` for real `R ≥ 1`. -/
theorem le_tsum_ite_lt_rpow (α : ℝ) (hα : 0 < α) {R : ℝ} (hR : 1 ≤ R) :
    ENNReal.ofReal (1 / (α * 2 ^ α) * R ^ (-α)) ≤
      ∑' n : ℕ, ENNReal.ofReal (if R < n then (n : ℝ) ^ (-(1 + α)) else 0) := by
  set m := ⌊R⌋₊ with hm
  have hiff : ∀ n : ℕ, R < n ↔ m + 1 ≤ n := fun n =>
    (Nat.floor_lt (by linarith)).symm.trans Nat.lt_iff_add_one_le
  set G : ℕ → ℝ := fun n => ((max n (m + 1) : ℕ) : ℝ) ^ (-α) with hG
  set t : ℕ → ℝ := fun n => if R < n then (n : ℝ) ^ (-(1 + α)) else 0 with ht
  have htnn : ∀ n, 0 ≤ t n := fun n => by
    simp only [ht]; split_ifs
    · exact Real.rpow_nonneg (Nat.cast_nonneg _) _
    · exact le_rfl
  have hterm : ∀ n : ℕ, (G n - G (n + 1)) / α ≤ t n := by
    intro n
    simp only [ht, hiff]
    split_ifs with h
    · have hn : (0 : ℝ) < n := Nat.cast_pos.2 (by omega)
      simp only [hG, max_eq_left h, max_eq_left (by omega : m + 1 ≤ n + 1)]
      rw [div_le_iff₀ hα]
      have := sub_rpow_le_mul α hα.le hn
      push_cast
      linarith
    · have h1 : n + 1 ≤ m + 1 := by omega
      simp only [hG, max_eq_right h1, max_eq_right (by omega : n ≤ m + 1), sub_self, zero_div,
        le_refl]
  have hpart : ∀ N, ENNReal.ofReal ((G 0 - G N) / α) ≤ ∑' n, ENNReal.ofReal (t n) := by
    intro N
    refine le_trans ?_ (ENNReal.sum_le_tsum (range N))
    rw [← ENNReal.ofReal_sum_of_nonneg fun n _ => htnn n]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← sum_range_sub', sum_div]
    exact sum_le_sum fun n _ => hterm n
  have hlim : Tendsto (fun N => ENNReal.ofReal ((G 0 - G N) / α)) atTop
      (𝓝 (ENNReal.ofReal ((G 0 - 0) / α))) := by
    refine (ENNReal.continuous_ofReal.tendsto _).comp ?_
    refine ((tendsto_const_nhds.sub ?_).div_const α)
    have h0 : Tendsto (fun N : ℕ => (N : ℝ) ^ (-α)) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop hα).comp tendsto_natCast_atTop_atTop
    refine h0.congr' ?_
    filter_upwards [eventually_ge_atTop (m + 1)] with N hN
    simp only [hG, max_eq_left hN]
  refine le_trans ?_ (le_of_tendsto' hlim hpart)
  refine ENNReal.ofReal_le_ofReal ?_
  simp only [hG, Nat.zero_max, sub_zero]
  have hm2 : ((m + 1 : ℕ) : ℝ) ≤ 2 * R := by
    have := Nat.floor_le (show (0 : ℝ) ≤ R by linarith)
    rw [← hm] at this
    push_cast
    linarith
  have hpos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := Nat.cast_pos.2 (Nat.succ_pos m)
  calc 1 / (α * 2 ^ α) * R ^ (-α) = (2 * R) ^ (-α) / α := by
        rw [Real.mul_rpow (by norm_num) (by linarith), Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
        field_simp
    _ ≤ ((m + 1 : ℕ) : ℝ) ^ (-α) / α :=
        div_le_div_of_nonneg_right (Real.rpow_le_rpow_of_nonpos hpos hm2 (by linarith)) hα.le

/-! ### Kernel tails -/

/-- The shell sum of the strict power-law tail is the strict tail of the `p`-series. -/
theorem shell_mul_ite_lt_rpow (hd : 1 ≤ d) (α R : ℝ) (hR : 0 ≤ R) (n : ℕ) :
    ((n ^ (d - 1) : ℕ) : ℝ≥0∞) *
        ENNReal.ofReal (if R < n then (n : ℝ) ^ (-((d : ℝ) + α)) else 0) =
      ENNReal.ofReal (if R < n then (n : ℝ) ^ (-(1 + α)) else 0) := by
  split_ifs with hn
  · have hn0 : n ≠ 0 := by
      rintro rfl
      exact absurd hn (not_lt.2 (by exact_mod_cast hR))
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
      pow_mul_rpow_neg hd α hn0]
  · simp

/-- Upper bound on the strict power-law tail: `∑_{‖z‖ > R} ‖z‖^(-(d+α)) ≤
2d·3^(d-1)·2^α R^(-α)/α`. -/
theorem tsum_ofReal_powerLaw_strict_tail_le (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α) {R : ℝ}
    (hR : 1 ≤ R) :
    ∑' z : Fin d → ℤ, ENNReal.ofReal (if R < ‖z‖ then ‖z‖ ^ (-((d : ℝ) + α)) else 0) ≤
      ((2 * d * 3 ^ (d - 1) : ℕ) : ℝ≥0∞) * ENNReal.ofReal (2 ^ α / α * R ^ (-α)) := by
  set g : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal (if R < (n : ℝ) then (n : ℝ) ^ (-((d : ℝ) + α))
    else 0) with hg
  have hz : ∀ z : Fin d → ℤ, ENNReal.ofReal (if R < ‖z‖ then ‖z‖ ^ (-((d : ℝ) + α)) else 0) =
      g ⌊‖z‖⌋₊ := fun z => by simp only [hg, natCast_floor_norm]
  rw [tsum_congr hz]
  refine (tsum_comp_floor_norm_bounds hd g (by
    simp only [hg, Nat.cast_zero]
    rw [ite_eq_right (by linarith), ENNReal.ofReal_zero])).2.trans ?_
  simp_rw [hg, shell_mul_ite_lt_rpow hd α R (by linarith)]
  gcongr
  exact tsum_ite_lt_rpow_le α hα hR

/-- Lower bound on the strict power-law tail: `2d R^(-α)/(α 2^α) ≤
∑_{‖z‖ > R} ‖z‖^(-(d+α))`. -/
theorem le_tsum_ofReal_powerLaw_strict_tail (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α) {R : ℝ}
    (hR : 1 ≤ R) :
    ((2 * d : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 / (α * 2 ^ α) * R ^ (-α)) ≤
      ∑' z : Fin d → ℤ, ENNReal.ofReal (if R < ‖z‖ then ‖z‖ ^ (-((d : ℝ) + α)) else 0) := by
  set g : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal (if R < (n : ℝ) then (n : ℝ) ^ (-((d : ℝ) + α))
    else 0) with hg
  have hz : ∀ z : Fin d → ℤ, ENNReal.ofReal (if R < ‖z‖ then ‖z‖ ^ (-((d : ℝ) + α)) else 0) =
      g ⌊‖z‖⌋₊ := fun z => by simp only [hg, natCast_floor_norm]
  rw [tsum_congr hz]
  rw [tsum_comp_floor_norm g]
  simp only [hg]
  refine le_trans ?_ (ENNReal.tsum_le_tsum fun n => (?_ : ((2 * d : ℕ) : ℝ≥0∞) *
    (((n ^ (d - 1) : ℕ) : ℝ≥0∞) *
      ENNReal.ofReal (if R < n then (n : ℝ) ^ (-((d : ℝ) + α)) else 0)) ≤ _))
  · simp_rw [shell_mul_ite_lt_rpow hd α R (by linarith), ENNReal.tsum_mul_left]
    gcongr
    exact le_tsum_ite_lt_rpow α hα hR
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [show ¬ R < 0 by linarith]
    · rw [← mul_assoc, ← Nat.cast_mul]
      gcongr
      calc 2 * d * n ^ (d - 1) ≤ 2 * d * (2 * n - 1) ^ (d - 1) := by
            gcongr; omega
        _ ≤ _ := (card_norm_eq_bounds hd hn).1

/-- **Upper kernel tail.** If `k z ≤ C ‖z‖^(-(d+α))` for `z ≠ 0`, then for every real `R ≥ 1`,
`∑_{‖z‖ > R} k z ≤ 2d·3^(d-1)·C·2^α/α · R^(-α)`. Only the upper bound on `k` is used. -/
theorem tsum_ofReal_kernel_tail_le (hd : 1 ≤ d) {α C : ℝ} (hα : 0 < α) {k : (Fin d → ℤ) → ℝ}
    (hk : ∀ z, z ≠ 0 → k z ≤ C * ‖z‖ ^ (-((d : ℝ) + α))) {R : ℝ} (hR : 1 ≤ R) :
    ∑' z : Fin d → ℤ, ENNReal.ofReal (if R < ‖z‖ then k z else 0) ≤
      ENNReal.ofReal ((2 * d * 3 ^ (d - 1) : ℕ) * C * 2 ^ α / α * R ^ (-α)) := by
  have hpt : ∀ z : Fin d → ℤ, ENNReal.ofReal (if R < ‖z‖ then k z else 0) ≤
      ENNReal.ofReal C *
        ENNReal.ofReal (if R < ‖z‖ then ‖z‖ ^ (-((d : ℝ) + α)) else 0) := by
    intro z
    split_ifs with h
    · have hz : z ≠ 0 := by rintro rfl; simp at h; linarith
      rw [← ENNReal.ofReal_mul' (Real.rpow_nonneg (norm_nonneg _) _)]
      exact ENNReal.ofReal_le_ofReal (hk z hz)
    · simp
  refine (ENNReal.tsum_le_tsum hpt).trans ?_
  rw [ENNReal.tsum_mul_left]
  refine (mul_le_mul' le_rfl (tsum_ofReal_powerLaw_strict_tail_le hd hα hR)).trans_eq ?_
  have h1 : (0 : ℝ) ≤ 2 ^ α / α * R ^ (-α) := by positivity
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
    ← ENNReal.ofReal_mul' (by positivity)]
  congr 1
  ring

/-- **Lower kernel tail.** If `c ‖z‖^(-(d+α)) ≤ k z` for `z ≠ 0`, then for every real `R ≥ 1`,
`2d·c/(α 2^α) · R^(-α) ≤ ∑_{‖z‖ > R} k z`. -/
theorem le_tsum_ofReal_kernel_tail (hd : 1 ≤ d) {α c : ℝ} (hα : 0 < α) {k : (Fin d → ℤ) → ℝ}
    (hk : ∀ z, z ≠ 0 → c * ‖z‖ ^ (-((d : ℝ) + α)) ≤ k z) {R : ℝ} (hR : 1 ≤ R) :
    ENNReal.ofReal (2 * d * c / (α * 2 ^ α) * R ^ (-α)) ≤
      ∑' z : Fin d → ℤ, ENNReal.ofReal (if R < ‖z‖ then k z else 0) := by
  have hpt : ∀ z : Fin d → ℤ, ENNReal.ofReal c *
      ENNReal.ofReal (if R < ‖z‖ then ‖z‖ ^ (-((d : ℝ) + α)) else 0) ≤
        ENNReal.ofReal (if R < ‖z‖ then k z else 0) := by
    intro z
    split_ifs with h
    · have hz : z ≠ 0 := by rintro rfl; simp at h; linarith
      rw [← ENNReal.ofReal_mul' (Real.rpow_nonneg (norm_nonneg _) _)]
      exact ENNReal.ofReal_le_ofReal (hk z hz)
    · simp
  refine le_trans ?_ (ENNReal.tsum_le_tsum hpt)
  rw [ENNReal.tsum_mul_left]
  refine le_trans (le_of_eq ?_)
    (mul_le_mul' le_rfl (le_tsum_ofReal_powerLaw_strict_tail hd hα hR))
  have h1 : (0 : ℝ) ≤ 1 / (α * 2 ^ α) * R ^ (-α) := by positivity
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
    ← ENNReal.ofReal_mul' (by positivity)]
  congr 1
  push_cast
  field_simp

/-! ### Rows -/

/-- Under the upper power-law bound with `α > 0`, the off-diagonal kernel row is finite. -/
theorem tsum_ofReal_kernel_lt_top (hd : 1 ≤ d) {α C : ℝ} (hα : 0 < α) {k : (Fin d → ℤ) → ℝ}
    (hk : ∀ z, z ≠ 0 → k z ≤ C * ‖z‖ ^ (-((d : ℝ) + α))) :
    ∑' z : Fin d → ℤ, ENNReal.ofReal (if z = 0 then 0 else k z) < ∞ := by
  have hpt : ∀ z : Fin d → ℤ, ENNReal.ofReal (if z = 0 then 0 else k z) ≤
      ENNReal.ofReal C * ENNReal.ofReal (if z = 0 then 0 else ‖z‖ ^ (-((d : ℝ) + α))) := by
    intro z
    split_ifs with h
    · simp
    · rw [← ENNReal.ofReal_mul' (Real.rpow_nonneg (norm_nonneg _) _)]
      exact ENNReal.ofReal_le_ofReal (hk z h)
  refine lt_of_le_of_lt (ENNReal.tsum_le_tsum hpt) ?_
  rw [ENNReal.tsum_mul_left]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ((tsum_ofReal_powerLaw_lt_top_iff hd α).2 hα)

/-- Reindexing a sum over `ℤ^d` by the displacement from `x`. -/
theorem tsum_sub_right_eq (f : (Fin d → ℤ) → ℝ≥0∞) (x : Fin d → ℤ) :
    ∑' y, f (y - x) = ∑' z, f z :=
  (Equiv.subRight x).tsum_eq f

/-- A translation-invariant intensity `J s(x,y) = k (y - x)` whose kernel satisfies the upper
power-law bound with `α > 0` has a finite intensity row at every vertex. -/
theorem rowSum_kernel_lt_top (hd : 1 ≤ d) {α C : ℝ} (hα : 0 < α) {k : (Fin d → ℤ) → ℝ}
    (hk : ∀ z, z ≠ 0 → k z ≤ C * ‖z‖ ^ (-((d : ℝ) + α))) {J : Sym2 (Fin d → ℤ) → ℝ≥0}
    (hJ : ∀ x y, (J s(x, y) : ℝ) = k (y - x)) (x : Fin d → ℤ) :
    rowSum (fun e => (J e : ℝ≥0∞)) x < ∞ := by
  classical
  rw [rowSum_def]
  have h : ∀ y, (if y = x then 0 else (J s(x, y) : ℝ≥0∞)) =
      (fun z => ENNReal.ofReal (if z = 0 then 0 else k z)) (y - x) := by
    intro y
    dsimp only
    by_cases hy : y = x
    · simp [hy]
    · rw [ite_eq_right hy, ite_eq_right (sub_ne_zero.2 hy), ← hJ, ENNReal.ofReal_coe_nnreal]
  rw [tsum_congr h]
  exact (tsum_sub_right_eq (fun z => ENNReal.ofReal (if z = 0 then 0 else k z)) x).trans_lt
    (tsum_ofReal_kernel_lt_top hd hα hk)

/-- **Omitted probability row.** For a translation-invariant intensity `J s(x,y) = k (y - x)`
whose kernel satisfies the upper power-law bound, closing every bond longer than `R ≥ 1` in the
exponential intensity family at `β` omits, at every vertex, a probability row of at most
`β · 2d·3^(d-1)·C·2^α/α · R^(-α)`. -/
theorem tsum_intensityProfile_tail_le (hd : 1 ≤ d) {α C : ℝ} (hα : 0 < α)
    {k : (Fin d → ℤ) → ℝ} (hk : ∀ z, z ≠ 0 → k z ≤ C * ‖z‖ ^ (-((d : ℝ) + α)))
    {J : Sym2 (Fin d → ℤ) → ℝ≥0} (hJ : ∀ x y, (J s(x, y) : ℝ) = k (y - x)) (β : ℝ≥0)
    {R : ℝ} (hR : 1 ≤ R) (x : Fin d → ℤ) :
    ∑' y, (if R < ‖y - x‖ then unitInterval.toENNReal (intensityProfile J β s(x, y)) else 0) ≤
      β * ENNReal.ofReal ((2 * d * 3 ^ (d - 1) : ℕ) * C * 2 ^ α / α * R ^ (-α)) := by
  have hpt : ∀ y, (if R < ‖y - x‖ then unitInterval.toENNReal (intensityProfile J β s(x, y))
      else 0) ≤ β * (fun z => ENNReal.ofReal (if R < ‖z‖ then k z else 0)) (y - x) := by
    intro y
    dsimp only
    split_ifs with h
    · rw [← hJ, ENNReal.ofReal_coe_nnreal, ← unitInterval.coe_toNNReal_eq_toENNReal,
        ← ENNReal.coe_mul, ENNReal.coe_le_coe]
      exact intensityProfile_toNNReal_le J β _
    · simp
  refine (ENNReal.tsum_le_tsum hpt).trans ?_
  rw [ENNReal.tsum_mul_left]
  gcongr
  exact (tsum_sub_right_eq (fun z => ENNReal.ofReal (if R < ‖z‖ then k z else 0)) x).trans_le
    (tsum_ofReal_kernel_tail_le hd hα hk hR)

end PercLib.Models.LongRange
