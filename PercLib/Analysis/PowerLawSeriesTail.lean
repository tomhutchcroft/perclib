/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New proofs for this project; no upstream Lean code is copied.
-/
module

public import Mathlib.Analysis.SumIntegralComparisons
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.PSeries

/-!
# Explicit tails for polynomially weighted power laws

## Main results

The integral test gives an explicit tail bound for a polynomial times a
decaying power. In particular, degree five controls the Gaussian tail in
the inverse-sixth nearest-neighbour walk moment series.
-/

@[expose] public section

open MeasureTheory Set

namespace PercLib.Analysis

/-- Polynomially weighted power-law tails are summable above their integrability
exponent. The cutoff need not be positive for summability. -/
theorem summable_pow_mul_div_rpow (N k : ℕ)
    {a p : ℝ} (ha : 0 ≤ a) (hp : (k : ℝ) + 1 < p) :
    Summable (fun n : ℕ => (((n + N + 1 : ℕ) : ℝ) ^ k) *
      (a / ((n + N + 1 : ℕ) : ℝ)) ^ p) := by
  have hs := (Real.summable_nat_rpow.mpr
    (show (k : ℝ) - p < -1 by linarith)).comp_injective
      (show Function.Injective (fun n : ℕ => n + N + 1) by
        intro m n h
        dsimp only at h
        omega)
  apply (hs.mul_left (a ^ p)).congr
  intro n
  dsimp only [Function.comp_apply]
  have hx : (0 : ℝ) < ((n + N + 1 : ℕ) : ℝ) := by positivity
  rw [Real.div_rpow ha hx.le, Real.rpow_sub hx, Real.rpow_natCast]
  ring

/-- The power-law tail after a positive integer cutoff, with its exact
integral-test constant. -/
theorem tsum_nat_add_rpow_le {N : ℕ} (hN : 0 < N) {p : ℝ} (hp : p < -1) :
    (∑' n : ℕ, ((n + N + 1 : ℕ) : ℝ) ^ p) ≤
      -(N : ℝ) ^ (p + 1) / (p + 1) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hanti : AntitoneOn (fun x : ℝ => x ^ p) (Ici (N : ℝ)) := by
    intro x hx y _ hxy
    exact Real.rpow_le_rpow_of_nonpos (hN'.trans_le hx) hxy (by linarith)
  have h := hanti.tsum_comp_add_le_integral N
    (integrableOn_Ioi_rpow_of_lt hp hN')
    (fun x hx => Real.rpow_nonneg (hN'.trans hx).le p)
  rwa [integral_Ioi_rpow_of_lt hp hN'] at h

/-- A polynomially weighted power-law tail. The cutoff is excluded from the
sum, so no extra endpoint term is paid. -/
theorem tsum_pow_mul_div_rpow_le {N k : ℕ} (hN : 0 < N)
    {a p : ℝ} (ha : 0 ≤ a) (hp : (k : ℝ) + 1 < p) :
    (∑' n : ℕ, (((n + N + 1 : ℕ) : ℝ) ^ k) *
      (a / ((n + N + 1 : ℕ) : ℝ)) ^ p) ≤
      a ^ p * (N : ℝ) ^ ((k : ℝ) + 1 - p) / (p - k - 1) := by
  have heq (n : ℕ) : (((n + N + 1 : ℕ) : ℝ) ^ k) *
      (a / ((n + N + 1 : ℕ) : ℝ)) ^ p =
      a ^ p * ((n + N + 1 : ℕ) : ℝ) ^ ((k : ℝ) - p) := by
    have hx : (0 : ℝ) < ((n + N + 1 : ℕ) : ℝ) := by positivity
    rw [Real.div_rpow ha hx.le, Real.rpow_sub hx, Real.rpow_natCast]
    ring
  simp_rw [heq]
  rw [tsum_mul_left]
  have h := mul_le_mul_of_nonneg_left
    (tsum_nat_add_rpow_le hN (show (k : ℝ) - p < -1 by linarith))
    (Real.rpow_nonneg ha p)
  convert h using 1
  rw [show (k : ℝ) - p + 1 = (k : ℝ) + 1 - p by ring]
  rw [show p - (k : ℝ) - 1 = -((k : ℝ) - p + 1) by ring, div_neg]
  ring

end PercLib.Analysis
