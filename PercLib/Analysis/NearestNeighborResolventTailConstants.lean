/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New proofs for this project; no upstream Lean code is copied.
Mathematical reference: explicit Gaussian tail bounds for the inverse-sixth
nearest-neighbour resolvent moment series.
-/
module

public import PercLib.Analysis.NearestNeighborResolventTail
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# An explicit dimension threshold for the Gaussian resolvent tail

At cutoff `⌊d/2⌋`, the Gaussian tail is bounded by
`d^5 (4/5)^(d/2) / 64`. A successive-dimension comparison makes the associated
quantity `d^6 (4/5)^(d/2)` decreasing from dimension 1000 onward. One fixed rational
power bound at dimension 1000 therefore controls every subsequent dimension.

## Main results

* `nearestNeighbor_resolvent_gaussian_tail_half_le_small`: the explicit Gaussian
  tail at the half-dimension cutoff is at most `1/(400d)` for `d ≥ 1000`.
* `nearestNeighbor_resolvent_gaussian_tail_half_le`: the weaker `1/(4d)` bound.
-/

@[expose] public section

noncomputable section

open Real

namespace PercLib.Analysis

private theorem pow_six_mul_rpow_four_fifths_succ_le {d : ℕ} (hd : 1000 ≤ d) :
    ((d + 1 : ℕ) : ℝ) ^ 6 * (4 / 5 : ℝ) ^ (((d + 1 : ℕ) : ℝ) / 2) ≤
      (d : ℝ) ^ 6 * (4 / 5 : ℝ) ^ ((d : ℝ) / 2) := by
  have hdR : (1000 : ℝ) ≤ d := by exact_mod_cast hd
  have hlinear : (d : ℝ) + 1 ≤ (1001 / 1000 : ℝ) * d := by linarith
  have hpower := pow_le_pow_left₀ (by positivity) hlinear 6
  have hroot : (4 / 5 : ℝ) ^ (1 / 2 : ℝ) ≤ 9 / 10 := by
    rw [← sqrt_eq_rpow, sqrt_le_iff]
    norm_num
  have hratio : (1001 / 1000 : ℝ) ^ 6 * (9 / 10) ≤ 1 := by norm_num
  rw [Nat.cast_add, Nat.cast_one,
    show ((d : ℝ) + 1) / 2 = (d : ℝ) / 2 + 1 / 2 by ring,
    rpow_add (by norm_num : (0 : ℝ) < 4 / 5)]
  calc
    _ ≤ ((1001 / 1000 : ℝ) * d) ^ 6 *
        ((4 / 5 : ℝ) ^ ((d : ℝ) / 2) * (9 / 10)) := by
      apply mul_le_mul hpower
        (mul_le_mul_of_nonneg_left hroot (by positivity)) (by positivity) (by positivity)
    _ = ((1001 / 1000 : ℝ) ^ 6 * (9 / 10)) *
        ((d : ℝ) ^ 6 * (4 / 5 : ℝ) ^ ((d : ℝ) / 2)) := by ring
    _ ≤ 1 * ((d : ℝ) ^ 6 * (4 / 5 : ℝ) ^ ((d : ℝ) / 2)) :=
      mul_le_mul_of_nonneg_right hratio (by positivity)
    _ = _ := one_mul _

private theorem pow_six_mul_rpow_four_fifths_le {d : ℕ} (hd : 1000 ≤ d) :
    (d : ℝ) ^ 6 * (4 / 5 : ℝ) ^ ((d : ℝ) / 2) ≤ 4 / 25 := by
  have hmono : AntitoneOn (fun n : ℕ =>
      (n : ℝ) ^ 6 * (4 / 5 : ℝ) ^ ((n : ℝ) / 2)) {n | 1000 ≤ n} :=
    antitoneOn_nat_Ici_of_succ_le fun n hn => pow_six_mul_rpow_four_fifths_succ_le hn
  have hbase : (1000 : ℝ) ^ 6 * (4 / 5 : ℝ) ^ ((1000 : ℝ) / 2) ≤ 4 / 25 := by
    have hblock : (4 / 5 : ℝ) ^ (10 : ℕ) ≤ 1 / 8 := by norm_num
    have hblocks := pow_le_pow_left₀ (by positivity) hblock 50
    have hpow : (4 / 5 : ℝ) ^ (500 : ℕ) ≤ (1 / 8 : ℝ) ^ (50 : ℕ) := by
      simpa only [← pow_mul] using hblocks
    rw [show (1000 : ℝ) / 2 = (500 : ℕ) by norm_num, rpow_natCast]
    calc
      _ ≤ (1000 : ℝ) ^ 6 * (1 / 8 : ℝ) ^ (50 : ℕ) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
      _ ≤ 4 / 25 := by norm_num
  exact (hmono (by simp) hd hd).trans hbase

private theorem pow_five_mul_rpow_four_fifths_le {d : ℕ} (hd : 1000 ≤ d) :
    (d : ℝ) ^ 5 / 64 * (4 / 5 : ℝ) ^ ((d : ℝ) / 2) ≤ 1 / (400 * (d : ℝ)) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have h := pow_six_mul_rpow_four_fifths_le hd
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 400 * d)).2
  nlinarith

/-- The explicit Gaussian inverse-sixth tail at cutoff `⌊d/2⌋` is at most
`1/(400d)` in every dimension at least 1000. -/
theorem nearestNeighbor_resolvent_gaussian_tail_half_le_small {d : ℕ} (hd : 1000 ≤ d) :
    (((π * d / 8) ^ ((d : ℝ) / 2) *
      ((d / 2 : ℕ) : ℝ) ^ (6 - (d : ℝ) / 2) / ((d : ℝ) / 2 - 6)) / 3) ≤
      1 / (400 * (d : ℝ)) := by
  have hdR : (1000 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  have hden0 : (0 : ℝ) < (d : ℝ) / 2 - 6 := by linarith
  have hN0 : (0 : ℝ) < ((d / 2 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < d / 2 by omega)
  have hNlower : (99 / 200 : ℝ) * d ≤ ((d / 2 : ℕ) : ℝ) := by
    have h : (d : ℝ) ≤ 2 * ((d / 2 : ℕ) : ℝ) + 1 := by
      exact_mod_cast (show d ≤ 2 * (d / 2) + 1 by omega)
    linarith
  have hNupper : ((d / 2 : ℕ) : ℝ) ≤ (d : ℝ) / 2 := by
    have h : (2 : ℝ) * ((d / 2 : ℕ) : ℝ) ≤ d := by
      exact_mod_cast (show 2 * (d / 2) ≤ d by omega)
    linarith
  have hbase : (π * d / 8) / ((d / 2 : ℕ) : ℝ) ≤ 4 / 5 := by
    apply (div_le_iff₀ hN0).2
    have hpi := mul_le_mul_of_nonneg_right pi_lt_d2.le hd0.le
    nlinarith
  have hdecay := rpow_le_rpow (by positivity) hbase
    (show (0 : ℝ) ≤ (d : ℝ) / 2 by positivity)
  have hfactor : ((d / 2 : ℕ) : ℝ) ^ (6 : ℕ) / (3 * ((d : ℝ) / 2 - 6)) ≤
      (d : ℝ) ^ 5 / 64 := by
    calc
      _ ≤ ((d : ℝ) / 2) ^ (6 : ℕ) / (3 * ((d : ℝ) / 2 - 6)) :=
        div_le_div_of_nonneg_right (pow_le_pow_left₀ hN0.le hNupper 6) (by positivity)
      _ ≤ ((d : ℝ) / 2) ^ (6 : ℕ) / (d : ℝ) :=
        div_le_div_of_nonneg_left (by positivity) hd0 (by linarith)
      _ = _ := by field_simp; ring
  have hrewrite :
      ((π * d / 8) ^ ((d : ℝ) / 2) *
        ((d / 2 : ℕ) : ℝ) ^ (6 - (d : ℝ) / 2) / ((d : ℝ) / 2 - 6)) / 3 =
      (((d / 2 : ℕ) : ℝ) ^ (6 : ℕ) / (3 * ((d : ℝ) / 2 - 6))) *
        ((π * d / 8) / ((d / 2 : ℕ) : ℝ)) ^ ((d : ℝ) / 2) := by
    rw [rpow_sub hN0, rpow_ofNat, div_rpow (by positivity) hN0.le]
    field_simp
  rw [hrewrite]
  exact (mul_le_mul hfactor hdecay (by positivity) (by positivity)).trans
    (pow_five_mul_rpow_four_fifths_le hd)

/-- The Gaussian inverse-sixth tail also satisfies the original `1/(4d)` bound. -/
theorem nearestNeighbor_resolvent_gaussian_tail_half_le {d : ℕ} (hd : 1000 ≤ d) :
    (((π * d / 8) ^ ((d : ℝ) / 2) *
      ((d / 2 : ℕ) : ℝ) ^ (6 - (d : ℝ) / 2) / ((d : ℝ) / 2 - 6)) / 3) ≤
      1 / (4 * (d : ℝ)) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  apply (nearestNeighbor_resolvent_gaussian_tail_half_le_small hd).trans
  exact one_div_le_one_div_of_le (by positivity) (by nlinarith)

end PercLib.Analysis
