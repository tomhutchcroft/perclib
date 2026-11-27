/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New proofs for this project; no upstream Lean code is copied.
-/
module

public import PercLib.Percolation.Bond.Lace.Bootstrap.Intensity.Defs
public import PercLib.Percolation.Bond.Lace.Bootstrap.Control

/-!
# Unit row mass and continuity of the lattice intensity family

## Main results

In positive dimension the normalized nearest-neighbour rate has row sum exactly
one at every vertex. Thus the actual Fourier bootstrap is continuous wherever
the canonical susceptibility is finite, with all finite-range and transitivity
hypotheses discharged by the lattice geometry.
-/

@[expose] public section
noncomputable section

open PercLib.Models.Site
open scoped ENNReal NNReal

namespace PercLib.Percolation.Bond.Lace

/-- The normalized rate has total incident mass exactly one. -/
theorem rowSum_nearestNeighborIntensity {d : ℕ} (hd : 0 < d) (x : Fin d → ℤ) :
    rowSum (fun e => (nearestNeighborIntensity d e : ℝ≥0∞)) x = 1 := by
  classical
  have hzero : rowSum (fun e => (nearestNeighborIntensity d e : ℝ≥0∞)) 0 = 1 := by
    have hfun : (fun e => (nearestNeighborIntensity d e : ℝ≥0∞)) =
        fun e => (((2 * (d : ℝ≥0))⁻¹ : ℝ≥0) : ℝ≥0∞) *
          unitInterval.toENNReal (homogeneousProfile (zdGraph d) 1 e) := by
      funext e
      by_cases he : e ∈ (zdGraph d).edgeSet <;>
        simp [nearestNeighborIntensity, homogeneousProfile, he]
    rw [hfun, rowSum_const_mul, rowSum_homogeneous_zdGraph]
    have hcoe : ENNReal.ofReal (2 * (d : ℝ) * (1 : unitInterval)) =
        ((2 * (d : ℝ≥0) : ℝ≥0) : ℝ≥0∞) := by simp
    rw [hcoe, ← ENNReal.coe_mul, inv_mul_cancel₀ (by positivity), ENNReal.coe_one]
  obtain ⟨σ, hσ0, hσ⟩ := nearestNeighborIntensity_transitive d 0 x
  have hrow := rowSum_comp_equiv σ (fun e => (nearestNeighborIntensity d e : ℝ≥0∞)) 0
  simp only [Function.comp_def, hσ, hσ0] at hrow
  exact hrow.symm.trans hzero

/-- Every dimension has normalized row mass at most one; dimension zero has mass zero. -/
theorem rowSum_nearestNeighborIntensity_le_one (d : ℕ) (x : Fin d → ℤ) :
    rowSum (fun e => (nearestNeighborIntensity d e : ℝ≥0∞)) x ≤ 1 := by
  obtain rfl | hd := Nat.eq_zero_or_pos d
  · simp [rowSum_fun_zero]
  · exact (rowSum_nearestNeighborIntensity hd x).le

/-- Every real rate row is summable, including its zero diagonal. -/
theorem summable_nearestNeighborIntensity (d : ℕ) (x : Fin d → ℤ) :
    Summable (fun y => (nearestNeighborIntensity d s(x, y) : ℝ)) := by
  classical
  have heq : (∑' y, (nearestNeighborIntensity d s(x, y) : ℝ≥0∞)) =
      rowSum (fun e => (nearestNeighborIntensity d e : ℝ≥0∞)) x := by
    rw [rowSum_def]
    apply tsum_congr
    intro y
    by_cases hy : y = x <;> simp [hy]
  have hfin : (∑' y, (nearestNeighborIntensity d s(x, y) : ℝ≥0∞)) ≠ ⊤ := by
    rw [heq]
    exact ne_top_of_le_ne_top ENNReal.one_ne_top
      (rowSum_nearestNeighborIntensity_le_one d x)
  simpa only [ENNReal.coe_toReal] using ENNReal.summable_toReal hfin

/-- Continuity of the actual nearest-neighbour bootstrap at finite susceptibility. -/
theorem continuousAt_fourierBootstrap_nearestNeighborIntensity {d : ℕ} (hd : 0 < d)
    {β : ℝ≥0} (hchi : chi (intensityProfile (nearestNeighborIntensity d) β) 0 ≠ ⊤) :
    ContinuousAt (fun b : ℝ≥0 => fourierBootstrap
      (intensityProfile (nearestNeighborIntensity d) b)) β := by
  exact continuousAt_fourierBootstrap_intensity hd (nearestNeighborIntensity d)
    (nearestNeighborIntensity_transitive d)
    (by rw [rowSum_nearestNeighborIntensity hd]; exact ENNReal.one_lt_top)
    (by norm_num : (0 : ℝ) ≤ 1)
    (nearestNeighborIntensity_eq_zero_of_one_lt_norm d) hchi

/-- The exponential edge probability dominates its rational lower bound. -/
theorem nearestNeighborProbability_ge_div {d : ℕ} (hd : 0 < d) (β : ℝ≥0) :
    (β : ℝ) / (2 * d + β) ≤ (nearestNeighborProbability d β : ℝ) := by
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have ht : 0 ≤ (β : ℝ) / (2 * d) := by positivity
  have he : Real.exp (-((β : ℝ) / (2 * d))) ≤
      1 / (1 + (β : ℝ) / (2 * d)) := by
    rw [Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (by positivity)
      (by linarith [Real.add_one_le_exp ((β : ℝ) / (2 * d))])
  rw [nearestNeighborProbability_coe]
  calc
    (β : ℝ) / (2 * d + β) = 1 - 1 / (1 + (β : ℝ) / (2 * d)) := by
      field_simp
      ring
    _ ≤ 1 - Real.exp (-(β : ℝ) / (2 * d)) := by
      simpa only [neg_div] using sub_le_sub_left he 1

/-- At normalized intensity two the actual step mass is at least `4/3`.
This supplies a finite upper endpoint once the subcritical bootstrap is closed. -/
theorem four_thirds_le_step_mass_at_two {d : ℕ} (hd : 2 ≤ d) :
    (4 : ℝ) / 3 ≤ 2 * d * (nearestNeighborProbability d 2 : ℝ) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hp := nearestNeighborProbability_ge_div (show 0 < d by omega) (2 : ℝ≥0)
  calc
    (4 : ℝ) / 3 ≤ 2 * d * ((2 : ℝ) / (2 * d + 2)) := by
      rw [← mul_div_assoc]
      apply (le_div_iff₀ (by positivity)).mpr
      nlinarith
    _ ≤ _ := mul_le_mul_of_nonneg_left hp (by positivity)

/-- An upper bound on the actual open-step mass gives an explicit bound on
normalized intensity, retaining the finite-dimensional correction. -/
theorem intensity_le_of_nearestNeighbor_step_mass_le {d : ℕ} (hd : 0 < d)
    (β : ℝ≥0) {m : ℝ} (hm : m < 2 * d)
    (hstep : 2 * d * (nearestNeighborProbability d β : ℝ) ≤ m) :
    (β : ℝ) ≤ 2 * d * m / (2 * d - m) := by
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hprob := mul_le_mul_of_nonneg_left (nearestNeighborProbability_ge_div hd β)
    (show (0 : ℝ) ≤ 2 * d by positivity)
  rw [← mul_div_assoc] at hprob
  have hmul := (div_le_iff₀ (show (0 : ℝ) < 2 * d + β by positivity)).mp
    (hprob.trans hstep)
  apply (le_div_iff₀ (sub_pos.mpr hm)).mpr
  nlinarith

end PercLib.Percolation.Bond.Lace
