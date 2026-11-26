/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-21. No upstream proof is copied and no definition is added.
Mathematical reference: the radial integrability step in the standard Fourier proof of
finiteness of Green, bubble and triangle diagrams for power-law lattice walks (integrals of
`ρ^{d-1-jb}` and `ρ^{d-1-2j} (log 1/ρ)^{-j}` near `ρ = 0`).
-/
module

public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.MeasureTheory.Integral.ExpDecay
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-!
# Radial integrability with a logarithmic factor

The finiteness criterion for long-range Green-function diagrams reduces, through the Fourier
symbol estimate, to integrability near the origin of `‖k‖^{-a} (log 1/‖k‖)^{-t}` in dimension
`d`. This file proves the exact criterion: integrable on a small ball if and only if `a < d`,
or `a = d` and `t > 1`. The case `t = 0` is the pure power case.

## Main results

* `integrableOn_Ioi_exp_mul_mul_rpow_neg_iff`: `e^{cu} u^{-t}` is integrable on `(a, ∞)`,
  `a > 0`, `t ≥ 0`, iff `c < 0`, or `c = 0` and `t > 1`.
* `integrableOn_Ioo_rpow_mul_neg_log_rpow_neg_iff`: `y^s (-log y)^{-t}` is integrable on
  `(0, δ)`, `0 < δ < 1`, `t ≥ 0`, iff `s > -1`, or `s = -1` and `t > 1`.
* `integrableOn_ball_norm_rpow_neg_mul_neg_log_rpow_neg_iff`: for an additive Haar measure on
  a finite-dimensional real normed space `E`, `‖x‖^{-a} (-log ‖x‖)^{-t}` is integrable on
  `ball 0 δ` iff `a < finrank E`, or `a = finrank E` and `t > 1`.
-/

@[expose] public section

noncomputable section

open Real MeasureTheory Set Metric

namespace PercLib.Probability

/-- `u ↦ e^{cu} u^{-t}` (`t ≥ 0`) is integrable on `(a, ∞)`, `a > 0`, iff `c < 0`, or
`c = 0` and `t > 1`. -/
theorem integrableOn_Ioi_exp_mul_mul_rpow_neg_iff {a c t : ℝ} (ha : 0 < a) (ht : 0 ≤ t) :
    IntegrableOn (fun u => exp (c * u) * u ^ (-t)) (Ioi a) ↔ c < 0 ∨ (c = 0 ∧ 1 < t) := by
  rcases lt_trichotomy c 0 with hc | rfl | hc
  · simp only [hc, true_or, iff_true]
    have h1 : IntegrableOn (fun u => exp (-(-c) * u) * a ^ (-t)) (Ioi a) :=
      (exp_neg_integrableOn_Ioi a (neg_pos.2 hc)).mul_const _
    refine h1.mono' ?_ ?_
    · exact ((continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul
        (continuousOn_id.rpow_const fun u hu => Or.inl (ne_of_gt (ha.trans hu)))
        ).aestronglyMeasurable measurableSet_Ioi
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun u hu => ?_)
      have hu0 : 0 < u := ha.trans hu
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), neg_neg]
      exact mul_le_mul_of_nonneg_left (rpow_le_rpow_of_nonpos ha hu.le (neg_nonpos.2 ht))
        (exp_pos _).le
  · simp only [zero_mul, exp_zero, one_mul, lt_irrefl, false_or, true_and]
    exact (integrableOn_Ioi_rpow_iff ha).trans (by constructor <;> intro h <;> linarith)
  · simp only [hc.not_gt, hc.ne', false_or, false_and, iff_false]
    intro hint
    set n := ⌈t⌉₊
    have hpos : 0 < c ^ n / (n.factorial : ℝ) := by positivity
    have hconst : IntegrableOn (fun _ : ℝ => c ^ n / (n.factorial : ℝ)) (Ioi (max a 1)) := by
      refine (hint.mono_set (Ioi_subset_Ioi (le_max_left _ _))).mono'
        aestronglyMeasurable_const ?_
      refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun u hu => ?_)
      have hu1 : 1 ≤ u := (le_max_right _ _).trans (le_of_lt hu)
      have hu0 : 0 < u := by linarith
      rw [Real.norm_eq_abs, abs_of_pos hpos]
      calc c ^ n / (n.factorial : ℝ) = (c * u) ^ n / n.factorial * u ^ (-(n : ℝ)) := by
            rw [mul_pow, rpow_neg hu0.le, rpow_natCast]
            field_simp
        _ ≤ exp (c * u) * u ^ (-t) :=
            mul_le_mul (pow_div_factorial_le_exp _ (by positivity) n)
              (rpow_le_rpow_of_exponent_le hu1 (neg_le_neg (Nat.le_ceil t)))
              (by positivity) (exp_pos _).le
    rw [integrableOn_const_iff] at hconst
    simp [hpos.ne'] at hconst

/-- `y ↦ y^s (-log y)^{-t}` (`t ≥ 0`) is integrable on `(0, δ)`, `0 < δ < 1`, iff `s > -1`,
or `s = -1` and `t > 1`. -/
theorem integrableOn_Ioo_rpow_mul_neg_log_rpow_neg_iff {δ s t : ℝ} (hδ0 : 0 < δ)
    (hδ1 : δ < 1) (ht : 0 ≤ t) :
    IntegrableOn (fun y => y ^ s * (-log y) ^ (-t)) (Ioo 0 δ) ↔
      -1 < s ∨ (s = -1 ∧ 1 < t) := by
  have himage : (fun u => exp (-u)) '' Ioi (-log δ) = Ioo 0 δ := by
    ext y
    constructor
    · rintro ⟨u, hu, rfl⟩
      refine ⟨exp_pos _, ?_⟩
      calc exp (-u) < exp (log δ) := exp_lt_exp.2 (by rw [mem_Ioi] at hu; linarith)
        _ = δ := exp_log hδ0
    · rintro ⟨hy0, hyδ⟩
      refine ⟨-log y, ?_, by simp [exp_log hy0]⟩
      rw [mem_Ioi, neg_lt_neg_iff]
      exact log_lt_log hy0 hyδ
  have hlogδ : 0 < -log δ := neg_pos.2 (log_neg hδ0 hδ1)
  rw [← himage, integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi
    (fun u _ => ((hasDerivAt_neg u).exp).hasDerivWithinAt)
    (exp_injective.comp neg_injective).injOn]
  rw [integrableOn_congr_fun (g := fun u => exp (-(s + 1) * u) * u ^ (-t)) ?_ measurableSet_Ioi,
    integrableOn_Ioi_exp_mul_mul_rpow_neg_iff hlogδ ht]
  · constructor
    · rintro (h | ⟨h1, h2⟩)
      · exact Or.inl (by linarith)
      · exact Or.inr ⟨by linarith, h2⟩
    · rintro (h | ⟨h1, h2⟩)
      · exact Or.inl (by linarith)
      · exact Or.inr ⟨by linarith, h2⟩
  · intro u _
    simp only [smul_eq_mul]
    rw [abs_mul, abs_neg, abs_one, mul_one, abs_of_pos (exp_pos _),
      rpow_def_of_pos (exp_pos _), log_exp, neg_neg, ← mul_assoc, ← exp_add]
    congr 2
    ring

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E] (μ : Measure E) [μ.IsAddHaarMeasure]

/-- For an additive Haar measure on a nontrivial finite-dimensional real normed space `E`,
`x ↦ ‖x‖^{-a} (-log ‖x‖)^{-t}` (`t ≥ 0`) is integrable on `ball 0 δ`, `0 < δ < 1`, iff
`a < finrank E`, or `a = finrank E` and `t > 1`. With `t = 0` this is the power criterion;
with `a = 2j`, `t = j` it is the logarithmic boundary of long-range diagrams. -/
theorem integrableOn_ball_norm_rpow_neg_mul_neg_log_rpow_neg_iff {δ a t : ℝ} (hδ0 : 0 < δ)
    (hδ1 : δ < 1) (ht : 0 ≤ t) :
    IntegrableOn (fun x : E => ‖x‖ ^ (-a) * (-log ‖x‖) ^ (-t)) (ball 0 δ) μ ↔
      a < Module.finrank ℝ E ∨ (a = Module.finrank ℝ E ∧ 1 < t) := by
  have hd : 1 ≤ Module.finrank ℝ E := Module.finrank_pos
  rw [integrableOn_fun_norm_addHaar μ (f := fun y => y ^ (-a) * (-log y) ^ (-t)),
    integrableOn_congr_fun
      (g := fun y => y ^ ((Module.finrank ℝ E : ℝ) - 1 - a) * (-log y) ^ (-t)) ?_
      measurableSet_Ioo,
    integrableOn_Ioo_rpow_mul_neg_log_rpow_neg_iff hδ0 hδ1 ht]
  · constructor
    · rintro (h | ⟨h1, h2⟩)
      · exact Or.inl (by linarith)
      · exact Or.inr ⟨by linarith, h2⟩
    · rintro (h | ⟨h1, h2⟩)
      · exact Or.inl (by linarith)
      · exact Or.inr ⟨by linarith, h2⟩
  · intro y hy
    simp only [smul_eq_mul]
    rw [← mul_assoc, ← rpow_natCast, ← rpow_add hy.1, Nat.cast_sub hd, Nat.cast_one]
    congr 2

end PercLib.Probability
