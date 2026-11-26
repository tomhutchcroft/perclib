/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New proofs for this project; no upstream Lean code is copied.
-/
module

public import PercLib.Analysis.NearestNeighborMoments
public import Mathlib.Analysis.Fourier.AddCircleMulti
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Normalized torus integration in physical frequencies

## Main results

Normalized Haar integrals on the unit torus equal normalized Lebesgue integrals
on the physical Fourier box `(-pi, pi)^d`. Scalar change of variables supplies
the exact normalization; half-open box boundaries do not change the measure.
-/

@[expose] public section
noncomputable section

open MeasureTheory Metric Set Real

namespace PercLib.Analysis

/-- Positive dilation of a ball, with the exact Haar Jacobian. -/
theorem integral_ball_comp_smul {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (μ : Measure E) [Measure.IsAddHaarMeasure μ] (f : E → F)
    {c : ℝ} (hc : 0 < c) (r : ℝ) :
    (∫ x in ball (0 : E) r, f (c • x) ∂μ) =
      (c ^ Module.finrank ℝ E)⁻¹ • ∫ x in ball (0 : E) (c * r), f x ∂μ := by
  have hpoint (x : E) :
      (ball (0 : E) (c * r)).indicator f (c • x) =
        (ball (0 : E) r).indicator (fun x => f (c • x)) x := by
    simp [Set.indicator, mem_ball, dist_zero_right, norm_smul,
      Real.norm_eq_abs, abs_of_pos hc, mul_lt_mul_iff_right₀ hc]
  have h := Measure.integral_comp_smul_of_nonneg μ
    ((ball (0 : E) (c * r)).indicator f) c (hR := hc.le)
  simp_rw [hpoint] at h
  simpa only [integral_indicator measurableSet_ball] using h

/-- Replacing coordinate half-open intervals by open intervals does not change
the restricted volume of a positive-radius sup-norm ball. -/
theorem volume_restrict_pi_Ioc_eq_ball (d : ℕ) {r : ℝ} (hr : 0 < r) :
    (volume : Measure (Fin d → ℝ)).restrict
      {x : Fin d → ℝ | ∀ i, x i ∈ Ioc (-r) r} = volume.restrict (ball 0 r) := by
  have hs : {x : Fin d → ℝ | ∀ i, x i ∈ Ioc (-r) r} =
      Set.univ.pi (fun _ => Ioc (-r) r) := by ext x; simp
  rw [hs, volume_pi, Measure.restrict_pi_pi,
    ← volume_pi, volume_restrict_pi_ball_eq_pi_Ioo_of_pos d hr]
  congr 1
  funext i
  exact Measure.restrict_congr_set (Ioo_ae_eq_Ioc (μ := volume)).symm

/-- The normalized unit-torus integral in the physical frequency convention. -/
theorem integral_unitTorus_eq_normalized_box {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (d : ℕ)
    (f : UnitAddTorus (Fin d) → F) :
    (∫ t : UnitAddTorus (Fin d), f t
      ∂Measure.pi (fun _ => AddCircle.haarAddCircle)) =
      ((2 * π) ^ d)⁻¹ • ∫ k in ball (0 : Fin d → ℝ) π,
        f (fun i => ((k i / (2 * π) : ℝ) : UnitAddCircle)) := by
  have hunit := UnitAddTorus.integral_preimage f (fun _ => -(1 / 2 : ℝ))
  change (∫ t : UnitAddTorus (Fin d), f t
      ∂Measure.pi (fun _ => AddCircle.haarAddCircle)) = _ at hunit
  have hbox : {x : Fin d → ℝ | ∀ i, x i ∈ Ioc (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + 1)} =
      {x : Fin d → ℝ | ∀ i, x i ∈ Ioc (-(1 / 2 : ℝ)) (1 / 2)} := by norm_num
  rw [hbox, volume_restrict_pi_Ioc_eq_ball d (by norm_num)] at hunit
  rw [hunit]
  have hc : (0 : ℝ) < 2 * π := by positivity
  have h := integral_ball_comp_smul volume
    (fun k : Fin d → ℝ => f (fun i => ((k i / (2 * π) : ℝ) : UnitAddCircle))) hc (1 / 2)
  have hcancel (x : Fin d → ℝ) :
      (fun i => ((((2 * π) • x) i / (2 * π) : ℝ) : UnitAddCircle)) =
        fun i => (x i : UnitAddCircle) := by
    funext i
    congr 1
    simp [Pi.smul_apply, smul_eq_mul, hc.ne']
  simpa only [hcancel, Module.finrank_fintype_fun_eq_card, Fintype.card_fin,
    show 2 * π * (1 / 2) = π by ring] using h

end PercLib.Analysis
