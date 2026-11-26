/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Ported from the source repository `yujinhkim/lrp`, branch `critical-lrp-1`, commit
`d382e4c28d92dd4e698ebf4f2aaf0bc932ae73fc`, files `PercLib/CriticalLRP/LevyAnalysis/Radial.lean`
(blob `bde47c1551`), `PercLib/CriticalLRP/LevyAnalysis/Rpow.lean` (blob `bc4e3f889a`) and
`PercLib/CriticalLRP/LevyAnalysis/Homogeneous.lean` (blob `2858fcb2a7`), contributed by `yujinhkim`;
licence Apache-2.0 as declared in that commit's file headers and
`third_party/critical-lrp/NOTICE.md`. Upstream origin `yujinhkim/Critical-Long-range-percolation` at
`3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf` (not independently verified). Formalization derived from
T. Hutchcroft, "Critical long-range percolation I: High effective dimension", arXiv:2508.18807v1,
Section I.5.2. Changes: the three files are merged into one, focused imports, no disabled linters or
`autoImplicit`, namespace `PercLib.Analysis`, and the helper `measurable_rpow_const'` replaced by
mathlib's `Measurable.pow_const`.
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import PercLib.Meta.Tag

/-!
# Radial (homogeneous) integration on a finite-dimensional real normed space

This file develops the elementary "polar-coordinates-free" radial integration
lemmas used to compute the moments of the Lévy measures `Π₁`, `Π_λ`, `Π_∞` of
Section I.5.2 of the paper, and the moment bounds for the Riesz/Green kernels.

The ambient setting is deliberately general, matching Definition I.1.3: `E` is a
finite-dimensional real normed space (the paper allows an arbitrary norm
`‖·‖`), `μ` is an additive Haar measure (Lebesgue measure), and the paper's
normalization (∗) `|B₁| = 1` is *not* used in the identities below: the unit
ball mass `μ (ball 0 1)` appears as an explicit constant.

Main results:

* `lintegral_ball_hom`: for `P` nonnegative, measurable, homogeneous of
  degree `k`, `∫⁻ x in ball 0 r, P x = r ^ (k + d) * ∫⁻ x in ball 0 1, P x`.
* `ofReal_rpow_neg_eq_add_lintegral`, `lintegral_Ioc_zero_rpow`: one-dimensional power
  integrals;
* `lintegral_ball_hom_rpow`: for `0 < s < k + d`,
  `∫⁻ x in ball 0 R, P x ‖x‖^{-s} = ((k+d)/(k+d-s)) R^{k+d-s} ∫⁻ x in ball 0 1, P x`.
-/

@[expose] public section

open MeasureTheory Metric Set Filter
open Module
open scoped ENNReal NNReal Topology Pointwise Interval

namespace PercLib.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Change of variables `x ↦ c⁻¹ • x` for a nonnegative `c`, for Lebesgue
integrals of nonnegative functions. -/
theorem lintegral_inv_smul (μ : Measure E) [μ.IsAddHaarMeasure] (c : ℝ) (hc : 0 < c)
    (g : E → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ x, g (c⁻¹ • x) ∂μ = ENNReal.ofReal (c ^ (finrank ℝ E : ℕ)) * ∫⁻ x, g x ∂μ := by
  rw [← lintegral_map (f := g) (g := fun x : E => c⁻¹ • x) hg (measurable_const_smul _)]
  rw [Measure.map_addHaar_smul μ (inv_ne_zero hc.ne'), lintegral_smul_measure]
  congr 1
  rw [abs_of_nonneg (by positivity), inv_pow, inv_inv]

/-- The change of variables `x = c • y` on a ball: the ball of radius `c` maps to the
unit ball. -/
theorem lintegral_ball_comp_smul (μ : Measure E) [μ.IsAddHaarMeasure] (F : E → ℝ≥0∞)
    (hF : Measurable F) {c : ℝ} (hc : 0 < c) :
    ∫⁻ x in ball (0 : E) c, F x ∂μ
      = ENNReal.ofReal (c ^ (finrank ℝ E : ℕ)) * ∫⁻ y in ball (0 : E) 1, F (c • y) ∂μ := by
  set g : E → ℝ≥0∞ := (ball (0 : E) 1).indicator (fun y => F (c • y)) with hg_def
  have hg : Measurable g := (hF.comp (measurable_const_smul c)).indicator measurableSet_ball
  have hmem : ∀ x : E, c⁻¹ • x ∈ ball (0 : E) 1 ↔ x ∈ ball (0 : E) c := by
    intro x
    simp only [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_inv,
      abs_of_pos hc, inv_mul_lt_iff₀ hc, mul_one]
  have key : ∫⁻ x in ball (0 : E) c, F x ∂μ = ∫⁻ x, g (c⁻¹ • x) ∂μ := by
    rw [← lintegral_indicator measurableSet_ball (f := F)]
    apply lintegral_congr
    intro x
    by_cases hx : x ∈ ball (0 : E) c
    · rw [indicator_of_mem hx, hg_def]
      simp only [indicator_of_mem (hmem x |>.2 hx), smul_inv_smul₀ hc.ne' x]
    · rw [indicator_of_notMem hx, hg_def]
      simp only [indicator_of_notMem (fun h => hx (hmem x |>.1 h))]
  rw [key, lintegral_inv_smul μ c hc g hg, hg_def, lintegral_indicator measurableSet_ball]

/-- Radial scaling of the integral of a homogeneous function over a ball. -/
theorem lintegral_ball_hom (μ : Measure E) [μ.IsAddHaarMeasure] {P : E → ℝ}
    (_hP : ∀ x, 0 ≤ P x) (hPm : Measurable P) {k : ℝ}
    (hhom : ∀ (c : ℝ), 0 < c → ∀ x, P (c • x) = c ^ k * P x)
    {r : ℝ} (hr : 0 < r) :
    ∫⁻ x in ball (0 : E) r, ENNReal.ofReal (P x) ∂μ
      = ENNReal.ofReal (r ^ (k + (finrank ℝ E : ℝ)))
        * ∫⁻ x in ball (0 : E) 1, ENNReal.ofReal (P x) ∂μ := by
  have hPt : ∀ y, ENNReal.ofReal (P (r • y)) = ENNReal.ofReal (r ^ k) * ENNReal.ofReal (P y) := by
    intro y
    rw [hhom r hr y, ENNReal.ofReal_mul (Real.rpow_nonneg hr.le k)]
  have hinner : ∫⁻ y in ball (0 : E) 1, ENNReal.ofReal (P (r • y)) ∂μ
      = ENNReal.ofReal (r ^ k) * ∫⁻ y in ball (0 : E) 1, ENNReal.ofReal (P y) ∂μ := by
    rw [lintegral_congr hPt]
    exact lintegral_const_mul'' _ hPm.ennreal_ofReal.aemeasurable
  rw [lintegral_ball_comp_smul μ _ hPm.ennreal_ofReal hr, hinner, ← mul_assoc,
    ← ENNReal.ofReal_mul (by positivity), ← Real.rpow_natCast, ← Real.rpow_add hr, add_comm]

/-- The elementary identity `a ^ (-s) = R ^ (-s) + ∫_a^R s t ^ (-s-1) dt` for `0 < a ≤ R`,
in Lebesgue-integral (`ℝ≥0∞`) form. -/
theorem ofReal_rpow_neg_eq_add_lintegral {s R a : ℝ} (hs : 0 < s) (ha : 0 < a) (haR : a ≤ R) :
    ENNReal.ofReal (a ^ (-s))
      = ENNReal.ofReal (R ^ (-s)) + ∫⁻ t in Ioc a R, ENNReal.ofReal (s * t ^ (-s - 1)) := by
  have hcont : ContinuousOn (fun t : ℝ => s * t ^ (-s - 1)) (uIcc a R) := by
    refine ContinuousOn.const_mul ?_ s
    refine ContinuousOn.rpow_const continuousOn_id ?_
    intro t ht
    left
    have : a ≤ t := (uIcc_of_le haR).symm ▸ ht |>.1
    linarith
  have hint : IntervalIntegrable (fun t : ℝ => s * t ^ (-s - 1)) volume a R :=
    hcont.intervalIntegrable
  have hkey : ∫ t in a..R, s * t ^ (-s - 1) = a ^ (-s) - R ^ (-s) := by
    have h0 : (0 : ℝ) ∉ uIcc a R := by
      rw [uIcc_of_le haR]
      simp only [mem_Icc, not_and]
      intro h; linarith
    rw [intervalIntegral.integral_const_mul,
      integral_rpow (Or.inr ⟨by linarith, h0⟩)]
    have h1 : (-s - 1 + 1 : ℝ) = -s := by ring
    rw [h1, mul_div_assoc']
    field_simp
    ring
  have hnn : 0 ≤ᵐ[volume.restrict (Ioc a R)] fun t : ℝ => s * t ^ (-s - 1) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have ht0 : 0 < t := lt_trans ha ht.1
    exact mul_nonneg hs.le (Real.rpow_nonneg ht0.le _)
  have hInt : Integrable (fun t : ℝ => s * t ^ (-s - 1)) (volume.restrict (Ioc a R)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le haR).1 hint
  have h1 : ∫⁻ t in Ioc a R, ENNReal.ofReal (s * t ^ (-s - 1))
      = ENNReal.ofReal (a ^ (-s) - R ^ (-s)) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hInt hnn]
    congr 1
    rw [← intervalIntegral.integral_of_le haR]
    exact hkey
  rw [h1, ← ENNReal.ofReal_add (Real.rpow_pos_of_pos (by linarith) (-s)).le (sub_nonneg.2 ?_)]
  · ring_nf
  · calc R ^ (-s) ≤ a ^ (-s) := by
          exact Real.rpow_le_rpow_of_nonpos ha haR (by linarith)

/-- The integral of `x ^ q` over `Ioc 0 R`, as a `ℝ≥0∞`-valued Lebesgue integral. -/
theorem lintegral_Ioc_zero_rpow {q R : ℝ} (hq : -1 < q) (hR : 0 ≤ R) :
    ∫⁻ t in Ioc (0 : ℝ) R, ENNReal.ofReal (t ^ q)
      = ENNReal.ofReal (R ^ (q + 1) / (q + 1)) := by
  have hint : IntervalIntegrable (fun t : ℝ => t ^ q) volume 0 R :=
    intervalIntegral.intervalIntegrable_rpow' hq
  have hnn : 0 ≤ᵐ[volume.restrict (Ioc (0:ℝ) R)] fun t : ℝ => t ^ q := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact Real.rpow_nonneg ht.1.le q
  have hInt : Integrable (fun t : ℝ => t ^ q) (volume.restrict (Ioc (0:ℝ) R)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hR).1 hint
  rw [← ofReal_integral_eq_lintegral_ofReal hInt hnn]
  congr 1
  rw [← intervalIntegral.integral_of_le hR, integral_rpow (Or.inl hq),
    Real.zero_rpow (by linarith : q + 1 ≠ 0), sub_zero]

/-- **Radial integration with a homogeneous weight.**
For `P` nonnegative, measurable and homogeneous of degree `k` (`P (c • x) = c ^ k * P x` for
`c > 0`) on a finite-dimensional real normed space of dimension `d` with additive Haar measure
`μ`, and for `0 < s < k + d`:

  `∫⁻ x in ball 0 R, P x * ‖x‖ ^ (-s) = ((k+d) / (k+d-s)) * R ^ (k+d-s) * ∫⁻ x in ball 0 1, P x`.

This is the "polar coordinates free" radial computation underlying the moments of the Lévy
measure `Π₁` of (I.5.16) and the Green function (Riesz kernel) bounds. -/
@[tag "MWLQ"]
theorem lintegral_ball_hom_rpow (μ : Measure E) [μ.IsAddHaarMeasure] [Nontrivial E]
    {P : E → ℝ} (hP : ∀ x, 0 ≤ P x) (hPm : Measurable P) {k s : ℝ}
    (hhom : ∀ (c : ℝ), 0 < c → ∀ x, P (c • x) = c ^ k * P x)
    (hs : 0 < s) (hsk : s < k + (finrank ℝ E : ℝ)) {R : ℝ} (hR : 0 < R) :
    ∫⁻ x in ball (0 : E) R, ENNReal.ofReal (P x * ‖x‖ ^ (-s)) ∂μ
      = ENNReal.ofReal ((k + (finrank ℝ E : ℝ)) / (k + (finrank ℝ E : ℝ) - s)
          * R ^ (k + (finrank ℝ E : ℝ) - s))
        * ∫⁻ x in ball (0 : E) 1, ENNReal.ofReal (P x) ∂μ := by
  have hdpos : (0 : ℝ) < (finrank ℝ E : ℝ) := by
    have := Module.finrank_pos (R := ℝ) (M := E)
    exact_mod_cast this
  have hkds : (0 : ℝ) < k + (finrank ℝ E : ℝ) - s := by linarith
  -- the singleton `{0}` is null
  have hsing : μ ({(0 : E)} : Set E) = 0 := by
    have h := Measure.addHaar_smul μ (r := (0 : ℝ)) (s := (Set.univ : Set E))
    rw [zero_smul_set (Set.univ_nonempty (α := E)),
      zero_pow (Nat.pos_iff_ne_zero.mp (Module.finrank_pos (R := ℝ) (M := E))), abs_zero,
          ENNReal.ofReal_zero, zero_mul] at h
    exact h
  have haeμ : ∀ᵐ x ∂μ, x ≠ (0 : E) := by
    rw [MeasureTheory.ae_iff]
    simp [hsing]
  -- generic measurability
  have hg_meas : Measurable (fun t : ℝ => ENNReal.ofReal (s * t ^ (-s - 1))) :=
    (measurable_const.mul (measurable_id'.pow_const (-s - 1))).ennreal_ofReal
  -- Step 1: the ball formula at all radii
  have hball : ∀ ρ : ℝ, 0 < ρ → ∫⁻ x in ball (0 : E) ρ, ENNReal.ofReal (P x) ∂μ
      = ENNReal.ofReal (ρ ^ (k + (finrank ℝ E : ℝ)))
        * ∫⁻ x in ball (0 : E) 1, ENNReal.ofReal (P x) ∂μ := by
    intro ρ hρ
    exact lintegral_ball_hom μ hP hPm hhom hρ
  -- Step 2: the pointwise decomposition, almost everywhere on the ball
  have hpt : ∀ᵐ x ∂(μ.restrict (ball (0 : E) R)),
      ENNReal.ofReal (P x * ‖x‖ ^ (-s))
        = ENNReal.ofReal (P x * R ^ (-s))
          + ∫⁻ t, (if ‖x‖ < t ∧ t ≤ R then
              ENNReal.ofReal (P x) * ENNReal.ofReal (s * t ^ (-s - 1)) else 0) := by
    filter_upwards [ae_mono Measure.restrict_le_self haeμ, ae_restrict_mem measurableSet_ball]
      with x hx0 hxmem
    have hxR : ‖x‖ < R := by simpa [mem_ball, dist_zero_right] using hxmem
    have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    have hbase := ofReal_rpow_neg_eq_add_lintegral (s := s) (R := R) (a := ‖x‖) hs hxpos hxR.le
    have hmul : ENNReal.ofReal (P x) * ENNReal.ofReal (‖x‖ ^ (-s))
        = ENNReal.ofReal (P x) * ENNReal.ofReal (R ^ (-s))
          + ENNReal.ofReal (P x) * ∫⁻ t in Ioc ‖x‖ R,
              ENNReal.ofReal (s * t ^ (-s - 1)) := by
      rw [hbase, mul_add]
    rw [← ENNReal.ofReal_mul (hP x), ← ENNReal.ofReal_mul (hP x)] at hmul
    have hsupp_fun : (fun t => if ‖x‖ < t ∧ t ≤ R then
          ENNReal.ofReal (P x) * ENNReal.ofReal (s * t ^ (-s - 1)) else 0)
        = (Ioc ‖x‖ R).indicator
            (fun t => ENNReal.ofReal (P x) * ENNReal.ofReal (s * t ^ (-s - 1))) := by
      ext t; simp only [mem_Ioc, Set.indicator_apply]
    have hsupp : (∫⁻ t, (if ‖x‖ < t ∧ t ≤ R then
          ENNReal.ofReal (P x) * ENNReal.ofReal (s * t ^ (-s - 1)) else 0))
        = ENNReal.ofReal (P x) * ∫⁻ t in Ioc ‖x‖ R,
            ENNReal.ofReal (s * t ^ (-s - 1)) := by
      rw [hsupp_fun, lintegral_indicator measurableSet_Ioc, lintegral_const_mul _ hg_meas]
    rw [hsupp, hmul]
  -- Step 3: integrate the decomposition
  rw [lintegral_congr_ae hpt]
  have hm1 : Measurable (fun a : E => ENNReal.ofReal (P a * R ^ (-s))) := by
    simpa only [Pi.mul_apply] using (hPm.mul_const (R ^ (-s))).ennreal_ofReal
  rw [lintegral_add_left hm1]
  -- Term 1
  have hterm1 : ∫⁻ x in ball (0 : E) R, ENNReal.ofReal (P x * R ^ (-s)) ∂μ
      = ENNReal.ofReal (R ^ (-s)) * (ENNReal.ofReal (R ^ (k + (finrank ℝ E : ℝ)))
          * ∫⁻ x in ball (0 : E) 1, ENNReal.ofReal (P x) ∂μ) := by
    have hmul' : ∀ x : E, ENNReal.ofReal (P x * R ^ (-s))
        = ENNReal.ofReal (P x) * ENNReal.ofReal (R ^ (-s)) := fun x =>
      ENNReal.ofReal_mul (hP x)
    rw [lintegral_congr hmul', lintegral_mul_const _ hPm.ennreal_ofReal, hball R hR,
      mul_comm]
  -- Term 2: Tonelli
  set G : E → ℝ → ℝ≥0∞ := fun x t =>
    if ‖x‖ < t ∧ t ≤ R then ENNReal.ofReal (P x) * ENNReal.ofReal (s * t ^ (-s - 1)) else 0 with hG
  have hG_meas : AEMeasurable (Function.uncurry G) (μ.prod volume) := by
    have huncurry : Function.uncurry G = fun p : E × ℝ =>
        if ‖p.1‖ < p.2 ∧ p.2 ≤ R then
          ENNReal.ofReal (P p.1) * ENNReal.ofReal (s * p.2 ^ (-s - 1)) else 0 := by
      funext p
      obtain ⟨x, t⟩ := p
      simp only [Function.uncurry_apply_pair, hG]
    rw [huncurry]
    refine Measurable.ite ?_ ?_ measurable_const |>.aemeasurable
    · exact (measurableSet_lt (measurable_norm.comp measurable_fst) measurable_snd).inter
        (measurableSet_le measurable_snd measurable_const)
    · exact ((hPm.comp measurable_fst).ennreal_ofReal).mul
        ((measurable_const.mul
          ((measurable_id'.pow_const (-s - 1)).comp measurable_snd)).ennreal_ofReal)
  have hG_off : ∀ x : E, x ∉ ball (0 : E) R → ∀ t : ℝ, G x t = 0 := by
    intro x hx t
    simp only [hG]
    have h : ¬ (‖x‖ < t ∧ t ≤ R) := by
      rintro ⟨h1, h2⟩
      exact hx (by simpa [mem_ball, dist_zero_right] using lt_of_lt_of_le h1 h2)
    simp [h]
  have hterm2 : ∫⁻ x in ball (0 : E) R, (∫⁻ t, G x t) ∂μ
      = ∫⁻ t, ∫⁻ x, G x t ∂μ := by
    have h1 : ∫⁻ x in ball (0 : E) R, (∫⁻ t, G x t) ∂μ = ∫⁻ x, (∫⁻ t, G x t) ∂μ := by
      rw [← lintegral_indicator measurableSet_ball]
      apply lintegral_congr
      intro x
      by_cases hx : x ∈ ball (0 : E) R
      · rw [indicator_of_mem hx]
      · rw [indicator_of_notMem hx]
        simp only [hG_off x hx, lintegral_zero]
    rw [h1, lintegral_lintegral_swap (μ := μ) (ν := volume) hG_meas]
  -- compute the inner integral for each t
  have hinner : ∀ t : ℝ, (∫⁻ x, G x t ∂μ) = if 0 < t ∧ t ≤ R then
      ENNReal.ofReal (s * t ^ (-s - 1)) * (ENNReal.ofReal (t ^ (k + (finrank ℝ E : ℝ)))
        * ∫⁻ x in ball (0 : E) 1, ENNReal.ofReal (P x) ∂μ) else 0 := by
    intro t
    by_cases ht : 0 < t ∧ t ≤ R
    · rw [ite_eq_left ht]
      have hfun : ∀ x : E, G x t = (ball (0 : E) t).indicator
          (fun x => ENNReal.ofReal (P x) * ENNReal.ofReal (s * t ^ (-s - 1))) x := by
        intro x
        by_cases hx : x ∈ ball (0 : E) t
        · have h1 : ‖x‖ < t := by simpa [mem_ball, dist_zero_right] using hx
          rw [hG]
          simp only [h1, ht.2, and_self, ite_eq_left, indicator_of_mem hx]
        · have h1 : ¬ (‖x‖ < t) := by simpa [mem_ball, dist_zero_right] using hx
          rw [hG]
          simp only [h1, false_and, ite_false, indicator_of_notMem hx]
      rw [lintegral_congr hfun, lintegral_indicator measurableSet_ball,
        lintegral_mul_const _ hPm.ennreal_ofReal, hball t ht.1, mul_comm]
    · rw [ite_eq_right ht]
      have hzero : ∀ x : E, G x t = 0 := by
        intro x
        rw [hG]
        by_cases h : ‖x‖ < t ∧ t ≤ R
        · exact absurd ⟨lt_of_le_of_lt (norm_nonneg x) h.1, h.2⟩ ht
        · simp [h]
      simp [hzero]
  rw [hterm1, hterm2, lintegral_congr hinner]
  -- the remaining 1-D computation
  have h1d : ∀ t : ℝ, (if 0 < t ∧ t ≤ R then
      ENNReal.ofReal (s * t ^ (-s - 1)) * (ENNReal.ofReal (t ^ (k + (finrank ℝ E : ℝ)))
        * ∫⁻ x in ball (0 : E) 1, ENNReal.ofReal (P x) ∂μ) else 0)
      = (Ioc (0 : ℝ) R).indicator (fun t =>
          ENNReal.ofReal (s * t ^ (k + (finrank ℝ E : ℝ) - s - 1))
            * ∫⁻ x in ball (0 : E) 1, ENNReal.ofReal (P x) ∂μ) t := by
    intro t
    by_cases ht : t ∈ Ioc (0 : ℝ) R
    · rw [indicator_of_mem ht, ite_eq_left ⟨ht.1, ht.2⟩]
      have hexp : -s - 1 + (k + (finrank ℝ E : ℝ)) = k + (finrank ℝ E : ℝ) - s - 1 := by ring
      rw [← mul_assoc, ← ENNReal.ofReal_mul (mul_nonneg hs.le (Real.rpow_nonneg ht.1.le _)),
        mul_assoc s, ← Real.rpow_add ht.1, hexp]
    · rw [indicator_of_notMem ht, ite_eq_right]
      intro h; exact ht ⟨h.1, h.2⟩
  have hm2 : Measurable (fun a : ℝ =>
      ENNReal.ofReal (s * a ^ (k + (finrank ℝ E : ℝ) - s - 1))) := by
    simpa only [Pi.mul_apply] using
      (measurable_const.mul (measurable_id'.pow_const
          (k + (finrank ℝ E : ℝ) - s - 1))).ennreal_ofReal
  have hm3 : Measurable (fun a : ℝ =>
      ENNReal.ofReal (a ^ (k + (finrank ℝ E : ℝ) - s - 1))) :=
    (measurable_id'.pow_const _).ennreal_ofReal
  have hsplit : (∫⁻ a in Ioc (0 : ℝ) R,
      ENNReal.ofReal (s * a ^ (k + (finrank ℝ E : ℝ) - s - 1)))
      = ENNReal.ofReal s * ∫⁻ a in Ioc (0 : ℝ) R,
          ENNReal.ofReal (a ^ (k + (finrank ℝ E : ℝ) - s - 1)) := by
    rw [← lintegral_const_mul (ENNReal.ofReal s) hm3]
    apply lintegral_congr
    intro a
    rw [ENNReal.ofReal_mul hs.le]
  rw [lintegral_congr h1d, lintegral_indicator measurableSet_Ioc,
    lintegral_mul_const _ hm2, hsplit,
    lintegral_Ioc_zero_rpow (by linarith) hR.le]
  -- final arithmetic
  have hRs : R ^ (-s) * R ^ (k + (finrank ℝ E : ℝ)) = R ^ (k + (finrank ℝ E : ℝ) - s) := by
    rw [← Real.rpow_add hR]
    norm_num [show -s + (k + (finrank ℝ E : ℝ)) = k + (finrank ℝ E : ℝ) - s from by ring]
  have hb : (0 : ℝ) ≤ s * (R ^ (k + (finrank ℝ E : ℝ) - s - 1 + 1)
      / (k + (finrank ℝ E : ℝ) - s - 1 + 1)) := by
    have h1 : (0 : ℝ) < R ^ (k + (finrank ℝ E : ℝ) - s - 1 + 1) := Real.rpow_pos_of_pos hR _
    have h2 : (0 : ℝ) < k + (finrank ℝ E : ℝ) - s - 1 + 1 := by linarith
    positivity
  have hq : (k + (finrank ℝ E : ℝ) - s - 1 + 1) = k + (finrank ℝ E : ℝ) - s := by ring
  have hreal : R ^ (-s) * R ^ (k + (finrank ℝ E : ℝ))
      + s * (R ^ (k + (finrank ℝ E : ℝ) - s - 1 + 1)
          / (k + (finrank ℝ E : ℝ) - s - 1 + 1))
      = (k + (finrank ℝ E : ℝ)) / (k + (finrank ℝ E : ℝ) - s)
          * R ^ (k + (finrank ℝ E : ℝ) - s) := by
    rw [hq, hRs]
    have hK : k + (finrank ℝ E : ℝ) - s ≠ 0 := by linarith
    field_simp
    ring
  rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_pos_of_pos hR (-s)).le,
    ← ENNReal.ofReal_mul hs.le, ← add_mul,
    ← ENNReal.ofReal_add (by positivity) hb, hreal]

/-! ### Non-vacuity -/

/-- Non-vacuity: `E = ℝ`, `P = 1` (`k = 0`), `s = 1/2`: the hypotheses hold, and
`∫⁻_{(-R, R)} |x|^{-1/2} = 2 R^{1/2} · vol(ball 0 1)`. -/
example {R : ℝ} (hR : 0 < R) :
    ∫⁻ x in ball (0 : ℝ) R, ENNReal.ofReal ((fun _ : ℝ => (1 : ℝ)) x * ‖x‖ ^ (-(1 / 2 : ℝ)))
      = ENNReal.ofReal ((0 + (Module.finrank ℝ ℝ : ℝ)) / (0 + (Module.finrank ℝ ℝ : ℝ) - 1 / 2)
          * R ^ (0 + (Module.finrank ℝ ℝ : ℝ) - 1 / 2))
        * ∫⁻ x in ball (0 : ℝ) 1, ENNReal.ofReal ((fun _ : ℝ => (1 : ℝ)) x) :=
  lintegral_ball_hom_rpow volume (fun _ => zero_le_one) measurable_const
    (fun c _ x => by simp) (by norm_num) (by norm_num) hR

end PercLib.Analysis
