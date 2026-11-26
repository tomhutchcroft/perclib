/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Driven linear differential equations with a regularly varying forcing term: Lemmas I.4.21,
I.4.22 and the case `b < a` of Lemma I.5.5 of T. Hutchcroft, *Critical long-range percolation I:
High effective dimension*, arXiv:2508.18807v1, §I.4.3 and §I.5.1.

Adapted from the repository `yujinhkim/lrp`, branch `critical-lrp-1`, commit
`d382e4c28d92dd4e698ebf4f2aaf0bc932ae73fc`, files
`PercLib/CriticalLRP/Analysis/Lemma_I_4_21.lean`, `PercLib/CriticalLRP/Analysis/Lemma_I_4_22.lean`
and `PercLib/CriticalLRP/Analysis/Lemma_I_5_5_lt.lean`; licence Apache-2.0 as declared in that
commit's file headers and `third_party/critical-lrp/NOTICE.md`; upstream
`yujinhkim/Critical-Long-range-percolation` at `3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf`.
Modified: `RegularlyVaryingAtTop f ρ` becomes `RegularlyVarying ρ f` of
`PercLib/Analysis/RegularVariation/Defs.lean`; the structure `RVPosData` is unbundled into the
hypotheses of `PercLib/Analysis/RegularVariation/GeneralInverse.lean`, and in the final
statements it is replaced by `Measurable h`, `RegularlyVarying b h` and `0 < b`, from which a
threshold exists (`RegularlyVarying.exists_threshold`); the definitions `errorTail` and
`powerExpWeight` are written out; the positivity hypothesis on `f` (and on `h`) is removed from
the asymptotic form of Lemma I.4.21 and from `exists_shared_error_of_tendsto`, whose proofs do
not need it; `measurable_ite_pos_of_hasDerivAt`, `measurable_errorTail`,
`regularlyVarying_of_tendsto_one`, `regularlyVarying_of_tendsto_pos` and
`RegularlyVaryingAtTop.congr_of_eventuallyEq` are replaced by mathlib and library lemmas;
declarations are renamed; `autoImplicit`, disabled linters and `#print` lines are removed.
-/
module

public import PercLib.Analysis.RegularVariation.LevelInverse
public import PercLib.Analysis.RegularVariation.LogScaling
public import PercLib.Analysis.LogarithmicCorrections
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

/-! # Driven linear ODEs with a regularly varying forcing term

Let `h` be measurable and regularly varying of index `b > 0`, and let `a > 0`. This file studies
`f' = (1 - δ) (a f + h) / r` for a measurable error `δ → 0` with `|δ| ≤ 1` on a tail `[r₀, ∞)`.
The integrating weight is written out as
`w r = r ^ a * exp (-(a * ∫ s in r₀..r, (Ioi r₀).indicator δ s / s))`;
it solves `w' = a (1 - δ) w / r` almost everywhere on `[r₀, ∞)` and is regularly varying of
index `a`. Then `f / w` is absolutely continuous with
`(f / w)(R) - (f / w)(r₀) = ∫ s in r₀..R, (1 - δ s) * (h s / (s * w s))`, and Karamata's
theorem gives the asymptotics.

## Main results

* `normalized_increment_of_driving_ode`: the exact normalized solution.
* `tendsto_div_of_driving_ode`: for `a < b`, `f / h → 1 / (b - a)`.
* `tendsto_div_of_tendsto_deriv_ratio`, `regularlyVarying_of_tendsto_deriv_ratio`: the
  asymptotic form of Lemma I.4.21, `f' / ((a f + h) / r) → 1` and `a < b` give
  `f ~ h / (b - a)`, and `f` is regularly varying of index `b`. No sign condition on `f` is
  assumed.
* `eventually_le_one_add_mul_div_of_deriv_le`: Lemma I.4.22, the one-sided estimate
  `f ≤ (1 + ε) h / (b - a)` from `f' ≤ (1 + ε) (a f + h) / r`, for `f > 0`.
* `regularlyVarying_and_tendsto_of_tendsto_deriv_ratio_of_lt`: Lemma I.5.5 for `b < a` and
  `f > 0`: `f` is regularly varying of index `a`, `h / f → 0` and `f' / (a f / r) → 1`.
-/

@[expose] public section

open Filter Set MeasureTheory
open scoped Topology

namespace PercLib.Analysis

/-! ## Absolute continuity -/

/-- A function whose derivative exists and is bounded in norm by `C` at every point of
`uIcc a b` is absolutely continuous on `uIcc a b`. -/
theorem absolutelyContinuousOnInterval_of_hasDerivAt_of_norm_le {f f' : ℝ → ℝ} {a b C : ℝ}
    (hderiv : ∀ x ∈ uIcc a b, HasDerivAt f (f' x) x)
    (hbound : ∀ x ∈ uIcc a b, ‖f' x‖ ≤ C) :
    AbsolutelyContinuousOnInterval f a b := by
  have hC : 0 ≤ C := le_trans (norm_nonneg (f' a)) (hbound a left_mem_uIcc)
  apply LipschitzOnWith.absolutelyContinuousOnInterval (K := ⟨C, hC⟩)
  apply (convex_uIcc a b).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
  · intro x hx
    exact (hderiv x hx).hasDerivWithinAt
  · intro x hx
    exact_mod_cast hbound x hx

/-- A real power is absolutely continuous on an interval not containing `0`. -/
theorem absolutelyContinuousOnInterval_rpow {a b : ℝ} (α : ℝ) (h0 : ∀ x ∈ uIcc a b, x ≠ 0) :
    AbsolutelyContinuousOnInterval (fun x : ℝ => x ^ α) a b :=
  ContDiffOn.absolutelyContinuousOnInterval fun x hx =>
    (Real.contDiffAt_rpow_const_of_ne (h0 x hx)).contDiffWithinAt

/-- The exponential of an absolutely continuous function is absolutely continuous. -/
theorem AbsolutelyContinuousOnInterval.exp {H : ℝ → ℝ} {a b : ℝ}
    (hH : AbsolutelyContinuousOnInterval H a b) :
    AbsolutelyContinuousOnInterval (fun x => Real.exp (H x)) a b := by
  obtain ⟨B, hB⟩ := hH.exists_bound
  let K : NNReal := ⟨Real.exp B, (Real.exp_pos B).le⟩
  have hK : LipschitzOnWith K Real.exp (Icc (-B) B) := by
    apply (convex_Icc _ _).lipschitzOnWith_of_nnnorm_deriv_le
    · intro x _
      exact (Real.hasDerivAt_exp x).differentiableAt
    · intro x hx
      rw [Real.deriv_exp]
      have hnorm : ‖Real.exp x‖ ≤ (K : ℝ) := by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos x)]
        exact Real.exp_le_exp.2 hx.2
      exact_mod_cast hnorm
  have hmap : MapsTo H (uIcc a b) (Icc (-B) B) := fun x hx =>
    abs_le.1 (by simpa [Real.norm_eq_abs] using hB x hx)
  simpa [Function.comp_def] using hK.comp_absolutelyContinuousOnInterval hmap hH

/-! ## A measurable extension -/

/-- A function differentiable on `(c, ∞)` agrees there with a globally measurable function
with the same derivatives. -/
theorem exists_measurable_eq_and_hasDerivAt_of_hasDerivAt_Ioi {f f' : ℝ → ℝ} {c : ℝ}
    (hderiv : ∀ x, c < x → HasDerivAt f (f' x) x) :
    ∃ g : ℝ → ℝ, Measurable g ∧ (∀ x, c < x → g x = f x) ∧
      ∀ x, c < x → HasDerivAt g (f' x) x := by
  classical
  refine ⟨(Ioi c).piecewise f 0, ?_, fun x hx => piecewise_eq_of_mem _ _ _ (mem_Ioi.2 hx),
    fun x hx => ?_⟩
  · exact ContinuousOn.measurable_piecewise
      (fun x hx => (hderiv x hx).continuousAt.continuousWithinAt) continuousOn_const
      measurableSet_Ioi
  · apply (hderiv x hx).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact piecewise_eq_of_mem _ _ _ hy

/-! ## The integrating weight -/

/-- The error, set to zero up to `r₀` and divided by `s`, is interval integrable. -/
theorem intervalIntegrable_indicator_Ioi_div {δ : ℝ → ℝ} {r₀ C : ℝ} (hr₀ : 0 < r₀)
    (hδm : Measurable δ) (hδ1 : ∀ x, r₀ ≤ x → |δ x| ≤ C) (a b : ℝ) :
    IntervalIntegrable (fun s => (Ioi r₀).indicator δ s / s) volume a b := by
  have hfun : (fun s => (Ioi r₀).indicator δ s / s) = (Ioi r₀).indicator (fun s => δ s / s) := by
    funext s
    by_cases hs : r₀ < s <;> simp [hs]
  rw [hfun]
  apply intervalIntegrable_indicator_Ioi_of_intervalIntegrable
  intro x y hx hxy
  exact (intervalIntegrable_div_of_bounded (lt_of_lt_of_le hr₀ hx) hxy hδm
    (fun t ht => hδ1 t (le_trans hx ht))).1

/-- The error primitive is continuous on the whole line. -/
theorem continuous_intervalIntegral_indicator_Ioi_div {δ : ℝ → ℝ} {r₀ C : ℝ} (hr₀ : 0 < r₀)
    (hδm : Measurable δ) (hδ1 : ∀ x, r₀ ≤ x → |δ x| ≤ C) :
    Continuous (fun r => ∫ s in r₀..r, (Ioi r₀).indicator δ s / s) :=
  intervalIntegral.continuous_primitive (intervalIntegrable_indicator_Ioi_div hr₀ hδm hδ1) r₀

/-- The integrating weight is measurable. -/
theorem measurable_rpow_mul_exp_neg_integral {δ : ℝ → ℝ} {r₀ C : ℝ} (a : ℝ) (hr₀ : 0 < r₀)
    (hδm : Measurable δ) (hδ1 : ∀ x, r₀ ≤ x → |δ x| ≤ C) :
    Measurable (fun r : ℝ => r ^ a * Real.exp (-(a * ∫ s in r₀..r, (Ioi r₀).indicator δ s / s))) :=
  (measurable_id.pow_const a).mul (Real.measurable_exp.comp
    ((measurable_const.mul (continuous_intervalIntegral_indicator_Ioi_div hr₀ hδm
        hδ1).measurable).neg))

/-- The integrating weight is positive on the positive axis. -/
theorem rpow_mul_exp_neg_integral_pos {δ : ℝ → ℝ} {r₀ a r : ℝ} (hr : 0 < r) :
    0 < r ^ a * Real.exp (-(a * ∫ s in r₀..r, (Ioi r₀).indicator δ s / s)) :=
  mul_pos (Real.rpow_pos_of_pos hr a) (Real.exp_pos _)

/-- On `[r₀, ∞)` the integrating weight is `r₀ ^ a` times the integrating factor
`exp (∫ s in r₀..r, (1 - δ s) a / s)`. -/
theorem rpow_mul_exp_neg_integral_eq_of_le {δ : ℝ → ℝ} {r₀ a r : ℝ} (hr₀ : 0 < r₀)
    (hδm : Measurable δ) (hδ1 : ∀ x, r₀ ≤ x → |δ x| ≤ 1) (hr : r₀ ≤ r) :
    r ^ a * Real.exp (-(a * ∫ s in r₀..r, (Ioi r₀).indicator δ s / s)) = r₀ ^ a *
      Real.exp (∫ s in r₀..r, (1 - (Ioi r₀).indicator δ s) * a / s) := by
  have hrpos : 0 < r := lt_of_lt_of_le hr₀ hr
  set H : ℝ := ∫ s in r₀..r, (Ioi r₀).indicator δ s / s
  have herr : IntervalIntegrable (fun s => (Ioi r₀).indicator δ s / s) volume r₀ r :=
    intervalIntegrable_indicator_Ioi_div hr₀ hδm hδ1 r₀ r
  have herr' : IntervalIntegrable (fun s => a * ((Ioi r₀).indicator δ s / s)) volume r₀ r :=
    herr.const_mul a
  have hbase : IntervalIntegrable (fun s => a / s) volume r₀ r := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hr]
    intro s hs
    exact (continuousAt_const.div continuousAt_id
      (ne_of_gt (lt_of_lt_of_le hr₀ hs.1))).continuousWithinAt
  have hlog : (∫ s in r₀..r, a / s) = Real.log (r / r₀) * a := by
    rw [show (fun s : ℝ => a / s) = (fun s => a * (1 / s)) by
      funext s; rw [mul_one_div], intervalIntegral.integral_const_mul,
      integral_one_div_of_pos hr₀ hrpos]
    ring
  have hsplit : (∫ s in r₀..r, (1 - (Ioi r₀).indicator δ s) * a / s) =
      Real.log (r / r₀) * a - a * H := by
    calc (∫ s in r₀..r, (1 - (Ioi r₀).indicator δ s) * a / s)
        = ∫ s in r₀..r, a / s - a * ((Ioi r₀).indicator δ s / s) := by
          apply intervalIntegral.integral_congr
          intro s _
          ring
      _ = (∫ s in r₀..r, a / s) - ∫ s in r₀..r, a * ((Ioi r₀).indicator δ s / s) :=
        intervalIntegral.integral_sub hbase herr'
      _ = Real.log (r / r₀) * a - a * H := by rw [hlog, intervalIntegral.integral_const_mul]
  have hW : Real.exp (∫ s in r₀..r, (1 - (Ioi r₀).indicator δ s) * a / s) =
      (r / r₀) ^ a * Real.exp (-(a * H)) := by
    rw [hsplit, show Real.log (r / r₀) * a - a * H =
      Real.log (r / r₀) * a + -(a * H) by ring,
      Real.exp_add, ← Real.rpow_def_of_pos (div_pos hrpos hr₀) a]
  rw [hW, Real.div_rpow hrpos.le hr₀.le]
  field_simp

/-- **The integrating weight is regularly varying of index `a`.** -/
theorem regularlyVarying_rpow_mul_exp_neg_integral {δ : ℝ → ℝ} {r₀ a : ℝ}
    (ha : 0 < a) (hr₀ : 0 < r₀) (hδm : Measurable δ) (hδ0 : Tendsto δ atTop (𝓝 0))
    (hδ1 : ∀ x, r₀ ≤ x → |δ x| ≤ 1) :
    RegularlyVarying a
      (fun r : ℝ => r ^ a * Real.exp (-(a * ∫ s in r₀..r, (Ioi r₀).indicator δ s / s))) := by
  set d := (Ioi r₀).indicator δ
  have hdm : Measurable d := hδm.indicator measurableSet_Ioi
  have hdb : ∀ x, |d x| ≤ 1 := by
    intro x
    by_cases hx : r₀ < x
    · simpa [d, hx] using hδ1 x hx.le
    · simp [d, hx]
  have hd0 : Tendsto d atTop (𝓝 0) := by
    apply hδ0.congr'
    filter_upwards [eventually_gt_atTop r₀] with x hx
    simp [d, hx]
  have hint : ∀ x y : ℝ, r₀ ≤ x → x ≤ y →
      IntervalIntegrable (fun s => (1 - d s) * a / s) volume x y := by
    intro x y hx hxy
    apply intervalIntegrable_div_of_bounded (g := fun s => (1 - d s) * a) (C := 2 * a)
      (lt_of_lt_of_le hr₀ hx) hxy ((measurable_const.sub hdm).mul_const a)
    intro s _
    have hfac : |1 - d s| ≤ 2 := by
      calc |1 - d s| ≤ |1| + |d s| := abs_sub _ _
        _ ≤ 2 := by have hb := hdb s; rw [abs_one]; linarith
    calc |(1 - d s) * a| = |1 - d s| * a := by rw [abs_mul, abs_of_pos ha]
      _ ≤ 2 * a := mul_le_mul_of_nonneg_right hfac ha.le
  refine ((regularlyVarying_exp_integral_of_tendsto_zero ha hr₀ hdm hd0 hint).const_mul
    (Real.rpow_pos_of_pos hr₀ a)).congr' ?_
  filter_upwards [eventually_ge_atTop r₀] with r hr
  exact (rpow_mul_exp_neg_integral_eq_of_le hr₀ hδm hδ1 hr).symm

/-- Almost everywhere on `(r₀, R]`, the integrating weight solves `w' = a (1 - δ) w / r`. -/
theorem ae_hasDerivAt_rpow_mul_exp_neg_integral {δ : ℝ → ℝ} {r₀ a R C : ℝ}
    (hr₀ : 0 < r₀) (hR : r₀ ≤ R) (hδm : Measurable δ) (hδ1 : ∀ x, r₀ ≤ x → |δ x| ≤ C) :
    ∀ᵐ x, x ∈ Ioc r₀ R →
      HasDerivAt (fun r : ℝ => r ^ a * Real.exp (-(a * ∫ s in r₀..r, (Ioi r₀).indicator δ s / s)))
        (a * (1 - δ x) * (x ^ a * Real.exp (-(a * ∫ s in r₀..x, (Ioi r₀).indicator δ s / s))) / x)
        x := by
  have hint := intervalIntegrable_indicator_Ioi_div hr₀ hδm hδ1 r₀ R
  filter_upwards [IntervalIntegrable.ae_hasDerivAt_integral hint] with x hx hxmem
  have hxuIcc : x ∈ uIcc r₀ R := by
    rw [uIcc_of_le hR]
    exact Ioc_subset_Icc_self hxmem
  have hxpos : 0 < x := lt_of_lt_of_le hr₀ hxmem.1.le
  have hh := hx hxuIcc r₀ left_mem_uIcc
  have hp := Real.hasDerivAt_rpow_const (x := x) (p := a) (Or.inl hxpos.ne')
  have hmul := hp.mul (hh.const_mul a).neg.exp
  apply hmul.congr_deriv
  simp only [Pi.neg_apply]
  have hdx : (Ioi r₀).indicator δ x = δ x := by simp [hxmem.1]
  have hpow : x ^ a = x ^ (a - 1) * x := by
    rw [← Real.rpow_add_one hxpos.ne', sub_add_cancel]
  rw [hdx, hpow]
  field_simp
  ring

/-! ## The exact solution and Lemma I.4.21 -/

/-- **The exact normalized solution** of `f' = (1 - δ) (a f + h) / r` on `[r₀, R]`, with `w` the
integrating weight: `f R / w R - f r₀ / w r₀ = ∫ s in r₀..R, (1 - δ s) (h s / (s w s))`. Here
`x₀ ≤ r₀` is a threshold above which `h` is positive and locally bounded. -/
theorem normalized_increment_of_driving_ode {f f' h δ : ℝ → ℝ} {a x₀ r₀ R : ℝ}
    (ha : 0 < a) (hr₀ : 0 < r₀) (hR : r₀ ≤ R)
    (hpos : ∀ x, x₀ ≤ x → 0 < h x) (hbdd : ∀ M, ∃ C, ∀ x, x₀ ≤ x → x ≤ M → h x ≤ C)
    (hrD : x₀ ≤ r₀)
    (hderiv : ∀ x, r₀ ≤ x → HasDerivAt f (f' x) x)
    (hδm : Measurable δ) (hδ1 : ∀ x, r₀ ≤ x → |δ x| ≤ 1)
    (hode : ∀ x, r₀ ≤ x → f' x = (1 - δ x) * (a * f x + h x) / x) :
    f R * (R ^ a * Real.exp (-(a * ∫ s in r₀..R, (Ioi r₀).indicator δ s / s)))⁻¹ -
        f r₀ * (r₀ ^ a * Real.exp (-(a * ∫ s in r₀..r₀, (Ioi r₀).indicator δ s / s)))⁻¹ =
      ∫ s in r₀..R, (1 - δ s) *
        (h s / (s * (s ^ a * Real.exp (-(a * ∫ t in r₀..s, (Ioi r₀).indicator δ t / t))))) := by
  set w : ℝ → ℝ := fun r => r ^ a * Real.exp (-(a * ∫ s in r₀..r, (Ioi r₀).indicator δ s / s))
    with hw_def
  set q : ℝ → ℝ := fun r => f r * (w r)⁻¹ with hq_def
  have hwpos : ∀ x, 0 < x → 0 < w x := fun x hx => rpow_mul_exp_neg_integral_pos hx
  have hHac : AbsolutelyContinuousOnInterval
      (fun r => ∫ s in r₀..r, (Ioi r₀).indicator δ s / s) r₀ R :=
    (intervalIntegrable_indicator_Ioi_div hr₀ hδm hδ1 r₀
        R).absolutelyContinuousOnInterval_intervalIntegral
      left_mem_uIcc
  have h0 : ∀ x ∈ uIcc r₀ R, x ≠ 0 := by
    intro x hx
    rw [uIcc_of_le hR] at hx
    exact (lt_of_lt_of_le hr₀ hx.1).ne'
  have hwAC : AbsolutelyContinuousOnInterval w r₀ R :=
    (absolutelyContinuousOnInterval_rpow a h0).mul
      (AbsolutelyContinuousOnInterval.exp (hHac.const_mul a).neg)
  have hwiAC : AbsolutelyContinuousOnInterval (fun x => (w x)⁻¹) r₀ R :=
    absolutelyContinuousOnInterval_inv hR hwAC fun x hx => hwpos x (lt_of_lt_of_le hr₀ hx.1)
  have hfc : ContinuousOn f (Icc r₀ R) := fun x hx =>
    (hderiv x hx.1).continuousAt.continuousWithinAt
  obtain ⟨Cf, hCf⟩ := isCompact_Icc.exists_bound_of_continuousOn hfc
  obtain ⟨Ch, hCh⟩ := hbdd R
  have hf'bound : ∀ x ∈ uIcc r₀ R, ‖f' x‖ ≤ 2 * (a * Cf + Ch) / r₀ := by
    intro x hx
    rw [uIcc_of_le hR] at hx
    have hx0 : 0 < x := lt_of_lt_of_le hr₀ hx.1
    have hfx : |f x| ≤ Cf := hCf x hx
    have hhx : |h x| ≤ Ch := by
      rw [abs_of_pos (hpos x (le_trans hrD hx.1))]
      exact hCh x (le_trans hrD hx.1) hx.2
    have hfac : |1 - δ x| ≤ 2 := by
      calc |1 - δ x| ≤ |1| + |δ x| := abs_sub _ _
        _ ≤ 2 := by have hd := hδ1 x hx.1; rw [abs_one]; linarith
    have hsum : |a * f x + h x| ≤ a * Cf + Ch := by
      calc |a * f x + h x| ≤ |a * f x| + |h x| := abs_add_le _ _
        _ = a * |f x| + |h x| := by rw [abs_mul, abs_of_pos ha]
        _ ≤ a * Cf + Ch := add_le_add (mul_le_mul_of_nonneg_left hfx ha.le) hhx
    have hmul : |1 - δ x| * |a * f x + h x| ≤ 2 * (a * Cf + Ch) :=
      mul_le_mul hfac hsum (abs_nonneg _) (by norm_num)
    have hnn : 0 ≤ 2 * (a * Cf + Ch) := (mul_nonneg (abs_nonneg _) (abs_nonneg _)).trans hmul
    rw [hode x hx.1, Real.norm_eq_abs, abs_div, abs_of_pos hx0, abs_mul]
    calc |1 - δ x| * |a * f x + h x| / x ≤ 2 * (a * Cf + Ch) / x :=
          div_le_div_of_nonneg_right hmul hx0.le
      _ ≤ 2 * (a * Cf + Ch) / r₀ := div_le_div_of_nonneg_left hnn hr₀ hx.1
  have hfAC : AbsolutelyContinuousOnInterval f r₀ R :=
    absolutelyContinuousOnInterval_of_hasDerivAt_of_norm_le
      (fun x hx => hderiv x (by rw [uIcc_of_le hR] at hx; exact hx.1)) hf'bound
  have hqAC : AbsolutelyContinuousOnInterval q r₀ R := hfAC.mul hwiAC
  have hqderiv : ∀ᵐ x, x ∈ Ioc r₀ R →
      deriv q x = (1 - δ x) * (h x / (x * w x)) := by
    filter_upwards [ae_hasDerivAt_rpow_mul_exp_neg_integral (a := a) hr₀ hR hδm hδ1]
      with x hx hxmem
    have hxpos : 0 < x := lt_of_lt_of_le hr₀ hxmem.1.le
    have hwx := hwpos x hxpos
    have hq : HasDerivAt q (f' x * (w x)⁻¹ +
        f x * (-(a * (1 - δ x) * w x / x) / (w x) ^ 2)) x :=
      (hderiv x hxmem.1.le).mul ((hx hxmem).inv hwx.ne')
    rw [hq.deriv, hode x hxmem.1.le]
    field_simp
    ring
  calc _ = q R - q r₀ := rfl
    _ = ∫ s in r₀..R, deriv q s := hqAC.integral_deriv_eq_sub.symm
    _ = _ := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [hqderiv] with x hx hxmem
        exact hx (by rwa [uIoc_of_le hR] at hxmem)

/-- **Lemma I.4.21 under the shared-error ODE.** If `f' = (1 - δ) (a f + h) / r` on `[r₀, ∞)`
with a measurable `δ → 0`, `|δ| ≤ 1`, and `h` measurable and regularly varying of index
`b > a > 0`, then `f / h → 1 / (b - a)`. -/
theorem tendsto_div_of_driving_ode {f f' h δ : ℝ → ℝ} {a b x₀ r₀ : ℝ}
    (hhm : Measurable h) (hh : RegularlyVarying b h)
    (ha : 0 < a) (hab : a < b) (hr₀ : 0 < r₀) (hr₀1 : 1 ≤ r₀)
    (hpos : ∀ x, x₀ ≤ x → 0 < h x) (hbdd : ∀ M, ∃ C, ∀ x, x₀ ≤ x → x ≤ M → h x ≤ C)
    (hrD : x₀ ≤ r₀)
    (hderiv : ∀ x, r₀ ≤ x → HasDerivAt f (f' x) x)
    (hδm : Measurable δ) (hδ0 : Tendsto δ atTop (𝓝 0))
    (hδ1 : ∀ x, r₀ ≤ x → |δ x| ≤ 1)
    (hode : ∀ x, r₀ ≤ x → f' x = (1 - δ x) * (a * f x + h x) / x) :
    Tendsto (fun r => f r / h r) atTop (𝓝 (1 / (b - a))) := by
  set w : ℝ → ℝ := fun r => r ^ a * Real.exp (-(a * ∫ s in r₀..r, (Ioi r₀).indicator δ s / s))
    with hw_def
  set v : ℝ → ℝ := fun s => h s / w s with hv_def
  set g : ℝ → ℝ := fun s => v s / s with hg_def
  set q : ℝ → ℝ := fun r => f r * (w r)⁻¹ with hq_def
  have hwrv : RegularlyVarying a w := regularlyVarying_rpow_mul_exp_neg_integral ha hr₀ hδm hδ0 hδ1
  have hwm : Measurable w := measurable_rpow_mul_exp_neg_integral a hr₀ hδm hδ1
  have hwpos : ∀ s, 0 < s → 0 < w s := fun s hs => rpow_mul_exp_neg_integral_pos hs
  have hvrv : RegularlyVarying (b - a) v := by
    have h1 := hh.mul hwrv.inv
    rw [← sub_eq_add_neg] at h1
    simpa [v, div_eq_mul_inv] using h1
  have hvm : Measurable v := hhm.div hwm
  have hvpos : ∀ᶠ s in atTop, 0 < v s := by
    filter_upwards [eventually_ge_atTop r₀] with s hs
    exact div_pos (hpos s (le_trans hrD hs)) (hwpos s (lt_of_lt_of_le hr₀ hs))
  have hgrv : RegularlyVarying (b - a - 1) g := by
    have h1 := hvrv.mul (regularlyVarying_rpow 1).inv
    rw [← sub_eq_add_neg] at h1
    refine h1.congr' ?_
    filter_upwards with s
    simp [g, div_eq_mul_inv, Real.rpow_one]
  have hgm : Measurable g := hvm.div measurable_id
  have hgp : ∀ᶠ s in atTop, 0 < g s := by
    filter_upwards [hvpos, eventually_gt_atTop (0 : ℝ)] with s hs hs0
    exact div_pos hs hs0
  have hwcont : ContinuousOn w (Ici r₀) := by
    intro s hs
    have hs0 : 0 < s := lt_of_lt_of_le hr₀ hs
    exact ((Real.continuousAt_rpow_const s a (Or.inl hs0.ne')).mul
      (Real.continuous_exp.continuousAt.comp
        (((continuous_intervalIntegral_indicator_Ioi_div hr₀ hδm hδ1).continuousAt.const_mul
          a).neg))).continuousWithinAt
  have hgint : ∀ x y : ℝ, r₀ ≤ x → x ≤ y → IntervalIntegrable g volume x y := by
    intro x y hx hxy
    obtain ⟨C, hC⟩ := hbdd y
    have hIc : IntegrableOn h (Icc x y) volume := by
      refine IntegrableOn.of_bound measure_Icc_lt_top hhm.aestronglyMeasurable C ?_
      filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
      rw [Real.norm_eq_abs, abs_of_pos (hpos s ((le_trans hrD hx).trans hs.1))]
      exact hC s ((le_trans hrD hx).trans hs.1) hs.2
    have hcont : ContinuousOn (fun s => (s * w s)⁻¹) (Icc x y) := by
      apply (continuousOn_id.mul (hwcont.mono (fun s hs => le_trans hx hs.1))).inv₀
      intro s hs
      have hs0 : 0 < s := (lt_of_lt_of_le hr₀ hx).trans_le hs.1
      exact (mul_pos hs0 (hwpos s hs0)).ne'
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hxy]
    refine (hIc.mul_continuousOn hcont isCompact_Icc).congr_fun (fun s _ => ?_) measurableSet_Icc
    simp only [g, v, div_eq_mul_inv, mul_inv]
    ring
  have hK : Tendsto (fun r => (∫ s in r₀..r, (1 - δ s) * g s) / (r * g r))
      atTop (𝓝 (1 / (b - a))) := by
    have hk := tendsto_mul_one_sub_karamata_integral_tail (by linarith : -1 < b - a - 1)
      hr₀ hr₀1 hgm hgrv hgint hδm hδ0 hδ1
    convert hk using 3
    ring
  have hvinf : Tendsto v atTop atTop :=
    RegularlyVarying.tendsto_atTop (by linarith) hvm hvrv
  have hq0 : Tendsto (fun r => q r₀ / (r * g r)) atTop (𝓝 0) := by
    have hq0' : Tendsto (fun r => q r₀ / v r) atTop (𝓝 0) := by
      simpa [div_eq_mul_inv] using hvinf.inv_tendsto_atTop.const_mul (q r₀)
    apply hq0'.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    simp only [g]
    field_simp
  have hinc : ∀ᶠ r in atTop, q r - q r₀ = ∫ s in r₀..r, (1 - δ s) * g s := by
    filter_upwards [eventually_ge_atTop r₀] with r hr
    have h1 := normalized_increment_of_driving_ode ha hr₀ hr hpos hbdd hrD hderiv hδm hδ1 hode
    simp only [q, w, g, v]
    rw [h1]
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [div_eq_mul_inv, mul_inv]
    ring
  have hq : Tendsto (fun r => q r / (r * g r)) atTop (𝓝 (1 / (b - a))) := by
    have hqdiff : Tendsto (fun r => (q r - q r₀) / (r * g r)) atTop (𝓝 (1 / (b - a))) :=
      hK.congr' (by filter_upwards [hinc] with r hr; rw [hr])
    have hl := hqdiff.add hq0
    rw [add_zero] at hl
    apply hl.congr'
    filter_upwards with r
    rw [← add_div, sub_add_cancel]
  apply hq.congr'
  filter_upwards [eventually_ge_atTop r₀] with r hr
  have hrpos : 0 < r := lt_of_lt_of_le hr₀ hr
  have hwr := hwpos r hrpos
  have hhr := hpos r (le_trans hrD hr)
  simp only [q, g, v]
  field_simp

/-- **The shared error of the asymptotic driving ODE.** If `f` is differentiable on `(0, ∞)`,
`h` is measurable and `f' / ((a f + h) / r) → 1`, then there are `r₀ ≥ max 1 x₀` and a
measurable `δ → 0` with `|δ| ≤ 1` and `f' = (1 - δ) (a f + h) / r` on `[r₀, ∞)`. -/
theorem exists_shared_error_of_tendsto {f f' h : ℝ → ℝ} {a : ℝ} (x₀ : ℝ) (hhm : Measurable h)
    (hderiv : ∀ x, 0 < x → HasDerivAt f (f' x) x)
    (hasym : Tendsto (fun r => f' r / ((a * f r + h r) / r)) atTop (𝓝 1)) :
    ∃ r₀ δ, 0 < r₀ ∧ 1 ≤ r₀ ∧ x₀ ≤ r₀ ∧ Measurable δ ∧
      Tendsto δ atTop (𝓝 0) ∧ (∀ x, r₀ ≤ x → |δ x| ≤ 1) ∧
      ∀ x, r₀ ≤ x → f' x = (1 - δ x) * (a * f x + h x) / x := by
  obtain ⟨f₀, hf0m, hf0eq, hf0d⟩ := exists_measurable_eq_and_hasDerivAt_of_hasDerivAt_Ioi hderiv
  set δ : ℝ → ℝ := fun r => 1 - deriv f₀ r * r / (a * f₀ r + h r) with hδ_def
  have hδm : Measurable δ :=
    measurable_const.sub (((measurable_deriv f₀).mul measurable_id).div
      ((measurable_const.mul hf0m).add hhm))
  have hδ0 : Tendsto δ atTop (𝓝 0) := by
    have hq : Tendsto (fun r => deriv f₀ r * r / (a * f₀ r + h r)) atTop (𝓝 1) := by
      apply hasym.congr'
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      rw [(hf0d x hx).deriv, hf0eq x hx, div_div_eq_mul_div]
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hq
  have hne : ∀ᶠ r in atTop, a * f r + h r ≠ 0 := by
    filter_upwards [hasym.eventually (eventually_ne_nhds one_ne_zero)] with r hr hzero
    simp [hzero] at hr
  obtain ⟨B, hB⟩ := eventually_atTop.1
    (hne.and (hδ0.eventually (Icc_mem_nhds (by norm_num : (-1 : ℝ) < 0) one_pos)))
  set R₀ := max (max 1 x₀) B
  have hR₀1 : 1 ≤ R₀ := le_trans (le_max_left 1 x₀) (le_max_left _ _)
  have hR₀pos : 0 < R₀ := lt_of_lt_of_le one_pos hR₀1
  refine ⟨R₀, δ, hR₀pos, hR₀1, le_trans (le_max_right 1 x₀) (le_max_left _ _), hδm, hδ0,
    fun x hx => abs_le.2 (hB x (le_trans (le_max_right _ _) hx)).2, fun x hx => ?_⟩
  have hx0 : 0 < x := lt_of_lt_of_le hR₀pos hx
  have hden : a * f x + h x ≠ 0 := (hB x (le_trans (le_max_right _ _) hx)).1
  simp only [δ, (hf0d x hx0).deriv, hf0eq x hx0]
  field_simp
  ring

/-- **Lemma I.4.21, asymptotic-ratio form.** Let `h` be measurable and regularly varying of index
`b`, let `0 < a < b`, and let `f` be differentiable on `(0, ∞)` with
`f' / ((a f + h) / r) → 1`. Then `f / (h / (b - a)) → 1`. -/
theorem tendsto_div_of_tendsto_deriv_ratio {f f' h : ℝ → ℝ} {a b : ℝ}
    (hhm : Measurable h) (hh : RegularlyVarying b h) (ha : 0 < a) (hab : a < b)
    (hderiv : ∀ x, 0 < x → HasDerivAt f (f' x) x)
    (hasym : Tendsto (fun r => f' r / ((a * f r + h r) / r)) atTop (𝓝 1)) :
    Tendsto (fun r => f r / (h r / (b - a))) atTop (𝓝 1) := by
  obtain ⟨x₀, -, hpos, hbdd⟩ := hh.exists_threshold (by linarith) hhm
  obtain ⟨r₀, δ, hr₀, hr₀1, hrD, hδm, hδ0, hδ1, hode⟩ :=
    exists_shared_error_of_tendsto x₀ hhm hderiv hasym
  have hlim := tendsto_div_of_driving_ode hhm hh ha hab hr₀ hr₀1 hpos hbdd hrD
    (fun x hx => hderiv x (lt_of_lt_of_le hr₀ hx)) hδm hδ0 hδ1 hode
  have hne : b - a ≠ 0 := (sub_pos.mpr hab).ne'
  have hmul := hlim.const_mul (b - a)
  rw [mul_one_div_cancel hne] at hmul
  apply hmul.congr'
  filter_upwards [hh.eventually_pos] with r hr
  field_simp

/-- **Lemma I.4.21, regular-variation conclusion**: under the hypotheses of
`tendsto_div_of_tendsto_deriv_ratio`, `f` is regularly varying of index `b`. -/
theorem regularlyVarying_of_tendsto_deriv_ratio {f f' h : ℝ → ℝ} {a b : ℝ}
    (hhm : Measurable h) (hh : RegularlyVarying b h) (ha : 0 < a) (hab : a < b)
    (hderiv : ∀ x, 0 < x → HasDerivAt f (f' x) x)
    (hasym : Tendsto (fun r => f' r / ((a * f r + h r) / r)) atTop (𝓝 1)) :
    RegularlyVarying b f := by
  have hG : RegularlyVarying b (fun r => h r / (b - a)) := by
    refine (hh.const_mul (inv_pos.2 (sub_pos.2 hab))).congr' (Eventually.of_forall fun r => ?_)
    simp only [div_eq_inv_mul]
  have hfc : ContinuousOn f (Ici 1) := fun x hx =>
    (hderiv x (lt_of_lt_of_le one_pos hx)).continuousAt.continuousWithinAt
  exact RegularlyVarying.of_tendsto_div hG
    (tendsto_div_of_tendsto_deriv_ratio hhm hh ha hab hderiv hasym)
    ⟨1, hfc.domRestrict.measurable⟩

/-! ## Lemma I.4.22: the one-sided estimate -/

/-- **The increment bound for the one-sided driving inequality**, at an intermediate power `c`:
if `f > 0`, `f' ≤ θ (a f + h) / r` and `1 ≤ θ ≤ min 2 (c / a)` on `[r₀, R]`, then
`f R / R ^ c - f r₀ / r₀ ^ c ≤ ∫ s in r₀..R, θ s h s / s ^ (c + 1)`, and the integrand is
interval integrable. -/
theorem normalized_increment_le_of_driving_bound {f f' h θ : ℝ → ℝ} {a c x₀ r₀ : ℝ}
    (ha : 0 < a) (hr₀ : 0 < r₀) (hhm : Measurable h)
    (hpos : ∀ x, x₀ ≤ x → 0 < h x) (hbdd : ∀ M, ∃ C, ∀ x, x₀ ≤ x → x ≤ M → h x ≤ C)
    (hrD : x₀ ≤ r₀)
    (hderiv : ∀ x, r₀ ≤ x → HasDerivAt f (f' x) x)
    (hfpos : ∀ x, r₀ ≤ x → 0 < f x)
    (hθm : Measurable θ) (hθlower : ∀ x, r₀ ≤ x → 1 ≤ θ x)
    (hθupper : ∀ x, r₀ ≤ x → θ x ≤ min 2 (c / a))
    (hfbd : ∀ x, r₀ ≤ x → f' x ≤ θ x * (a * f x + h x) / x)
    {R : ℝ} (hR : r₀ ≤ R) :
    (f R / R ^ c - f r₀ / r₀ ^ c ≤ ∫ s in r₀..R, θ s * h s / s ^ (c + 1)) ∧
      IntervalIntegrable (fun s => θ s * h s / s ^ (c + 1)) volume r₀ R := by
  set q : ℝ → ℝ := fun r => f r / r ^ c with hq_def
  set g : ℝ → ℝ := fun s => θ s * h s / s ^ (c + 1) with hg_def
  have hw : ∀ x ∈ Icc r₀ R, HasDerivAt q ((f' x * x - c * f x) / x ^ (c + 1)) x := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le hr₀ hx.1
    have hp : x ^ c ≠ 0 := (Real.rpow_pos_of_pos hx0 c).ne'
    have hd := (hderiv x hx.1).div (Real.hasDerivAt_rpow_const (x := x) (p := c)
      (Or.inl hx0.ne')) hp
    apply hd.congr_deriv
    rw [Real.rpow_add hx0, Real.rpow_one, Real.rpow_sub_one hx0.ne' c]
    field_simp
  have hqbound : ∀ x ∈ Ioo r₀ R, (f' x * x - c * f x) / x ^ (c + 1) ≤ g x := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le hr₀ hx.1.le
    have hf := hfpos x hx.1.le
    have haθ : a * θ x ≤ c := by
      have ht' : θ x ≤ c / a := (hθupper x hx.1.le).trans (min_le_right _ _)
      calc a * θ x ≤ a * (c / a) := mul_le_mul_of_nonneg_left ht' ha.le
        _ = c := by field_simp
    have hf1 : f' x * x ≤ θ x * (a * f x + h x) := (le_div_iff₀ hx0).mp (hfbd x hx.1.le)
    have he : f' x * x - c * f x ≤ θ x * h x := by
      have hθα : a * θ x * f x ≤ c * f x := mul_le_mul_of_nonneg_right haθ hf.le
      nlinarith
    exact (div_le_div_iff_of_pos_right (Real.rpow_pos_of_pos hx0 (c + 1))).2 he
  have hgint : IntervalIntegrable g volume r₀ R := by
    obtain ⟨C, hC⟩ := hbdd R
    have hIc : IntegrableOn (fun s => θ s * h s) (Icc r₀ R) volume := by
      refine IntegrableOn.of_bound measure_Icc_lt_top (hθm.mul hhm).aestronglyMeasurable
        (2 * C) ?_
      filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
      have hxD := le_trans hrD hx.1
      have hhpos := hpos x hxD
      have hθpos : 0 < θ x := zero_lt_one.trans_le (hθlower x hx.1)
      have hθle : θ x ≤ 2 := (hθupper x hx.1).trans (min_le_left _ _)
      rw [Real.norm_eq_abs, abs_of_pos (mul_pos hθpos hhpos)]
      exact mul_le_mul hθle (hC x hxD hx.2) hhpos.le (by norm_num)
    have hcont : ContinuousOn (fun x : ℝ => (x ^ (c + 1))⁻¹) (Icc r₀ R) := by
      intro x hx
      have hx0 : 0 < x := lt_of_lt_of_le hr₀ hx.1
      exact ((Real.continuousAt_rpow_const x (c + 1) (Or.inl hx0.ne')).inv₀
        (Real.rpow_pos_of_pos hx0 _).ne').continuousWithinAt
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hR]
    simpa [g, div_eq_mul_inv] using hIc.mul_continuousOn hcont isCompact_Icc
  have hqcont : ContinuousOn q (Icc r₀ R) := fun x hx =>
    (hw x hx).continuousAt.continuousWithinAt
  refine ⟨?_, hgint⟩
  exact intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le hR hqcont
    (fun x hx => (hw x ⟨hx.1.le, hx.2.le⟩).hasDerivWithinAt)
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hR).1 hgint) hqbound

/-- **The intermediate-power estimate** for the one-sided driving inequality: for `c < b`,
`f / h ≤ 1 / (b - c) + ε` eventually, for every `ε > 0`. -/
theorem eventually_ratio_le_of_driving_bound {f f' h θ : ℝ → ℝ} {a b c x₀ r₀ : ℝ}
    (hhm : Measurable h) (hh : RegularlyVarying b h)
    (ha : 0 < a) (hcb : c < b)
    (hr₀ : 0 < r₀) (hr₀1 : 1 ≤ r₀)
    (hpos : ∀ x, x₀ ≤ x → 0 < h x) (hbdd : ∀ M, ∃ C, ∀ x, x₀ ≤ x → x ≤ M → h x ≤ C)
    (hrD : x₀ ≤ r₀)
    (hderiv : ∀ x, r₀ ≤ x → HasDerivAt f (f' x) x)
    (hfpos : ∀ x, r₀ ≤ x → 0 < f x)
    (hθm : Measurable θ) (hθlower : ∀ x, r₀ ≤ x → 1 ≤ θ x)
    (hθupper : ∀ x, r₀ ≤ x → θ x ≤ min 2 (c / a))
    (hθ0 : Tendsto θ atTop (𝓝 1))
    (hfbd : ∀ x, r₀ ≤ x → f' x ≤ θ x * (a * f x + h x) / x) :
    ∀ ε > 0, ∀ᶠ r in atTop, f r / h r ≤ 1 / (b - c) + ε := by
  set B : ℝ → ℝ := fun s => h s / s ^ (c + 1) with hB_def
  set V : ℝ → ℝ := fun r => h r / r ^ c with hV_def
  set q : ℝ → ℝ := fun r => f r / r ^ c with hq_def
  set g : ℝ → ℝ := fun s => θ s * B s with hg_def
  have hBrv : RegularlyVarying (b - c - 1) B := by
    have h1 := hh.mul (regularlyVarying_rpow (c + 1)).inv
    rw [show b + -(c + 1) = b - c - 1 by ring] at h1
    simpa [B, div_eq_mul_inv] using h1
  have hBm : Measurable B := hhm.div (by fun_prop)
  have hBp : ∀ᶠ s in atTop, 0 < B s := by
    filter_upwards [eventually_ge_atTop r₀] with s hs
    exact div_pos (hpos s (le_trans hrD hs)) (Real.rpow_pos_of_pos (lt_of_lt_of_le hr₀ hs) _)
  have hBint : ∀ x y : ℝ, r₀ ≤ x → x ≤ y → IntervalIntegrable B volume x y := by
    intro x y hx hxy
    obtain ⟨C, hC⟩ := hbdd y
    have hIc : IntegrableOn h (Icc x y) volume := by
      refine IntegrableOn.of_bound measure_Icc_lt_top hhm.aestronglyMeasurable C ?_
      filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
      rw [Real.norm_eq_abs, abs_of_pos (hpos s ((le_trans hrD hx).trans hs.1))]
      exact hC s ((le_trans hrD hx).trans hs.1) hs.2
    have hcont : ContinuousOn (fun s : ℝ => (s ^ (c + 1))⁻¹) (Icc x y) := by
      intro s hs
      have hs0 : 0 < s := (lt_of_lt_of_le hr₀ hx).trans_le hs.1
      exact ((Real.continuousAt_rpow_const s (c + 1) (Or.inl hs0.ne')).inv₀
        (Real.rpow_pos_of_pos hs0 _).ne').continuousWithinAt
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hxy]
    simpa [B, div_eq_mul_inv] using hIc.mul_continuousOn hcont isCompact_Icc
  have hδm : Measurable (fun s => 1 - θ s) := measurable_const.sub hθm
  have hδ0 : Tendsto (fun s => 1 - θ s) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hθ0
  have hδ1 : ∀ x, r₀ ≤ x → |1 - θ x| ≤ 1 := by
    intro x hx
    have hlo := hθlower x hx
    have hhi := (hθupper x hx).trans (min_le_left _ _)
    rw [abs_le]
    constructor <;> linarith
  have hK : Tendsto (fun r => (∫ s in r₀..r, g s) / (r * B r)) atTop (𝓝 (1 / (b - c))) := by
    have hk := tendsto_mul_one_sub_karamata_integral_tail (g := B) (δ := fun s => 1 - θ s)
      (by linarith : -1 < b - c - 1) hr₀ hr₀1 hBm hBrv hBint hδm hδ0 hδ1
    simpa only [sub_sub_cancel, sub_add_cancel, g] using hk
  have hq0 : Tendsto (fun r => q r₀ / (r * B r)) atTop (𝓝 0) := by
    have hVrv : RegularlyVarying (b - c) V := by
      have h1 := hh.mul (regularlyVarying_rpow c).inv
      rw [← sub_eq_add_neg] at h1
      simpa [V, div_eq_mul_inv] using h1
    have hi := ((RegularlyVarying.tendsto_atTop (sub_pos.2 hcb) (hhm.div (by fun_prop))
      hVrv).inv_tendsto_atTop).const_mul (q r₀)
    rw [mul_zero] at hi
    apply hi.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    simp only [B, Pi.inv_apply, Pi.div_apply, inv_div]
    rw [Real.rpow_add hr, Real.rpow_one]
    field_simp
  have hbound : ∀ᶠ r in atTop, q r / (r * B r) ≤
      (∫ s in r₀..r, g s) / (r * B r) + q r₀ / (r * B r) := by
    filter_upwards [eventually_ge_atTop r₀] with r hr
    have hi := (normalized_increment_le_of_driving_bound ha hr₀ hhm hpos hbdd hrD hderiv hfpos
      hθm hθlower hθupper hfbd hr).1
    have hq : q r ≤ (∫ s in r₀..r, g s) + q r₀ := by
      simp only [q, g, B, mul_div_assoc] at hi ⊢
      linarith
    have hposden : 0 < r * B r :=
      mul_pos (lt_of_lt_of_le hr₀ hr) (div_pos (hpos r (le_trans hrD hr))
        (Real.rpow_pos_of_pos (lt_of_lt_of_le hr₀ hr) _))
    rw [← add_div]
    exact div_le_div_of_nonneg_right hq hposden.le
  have hlim : Tendsto (fun r => (∫ s in r₀..r, g s) / (r * B r) + q r₀ / (r * B r))
      atTop (𝓝 (1 / (b - c))) := by
    simpa using hK.add hq0
  have hbase : ∀ᶠ r in atTop, q r / (r * B r) = f r / h r := by
    filter_upwards [eventually_ge_atTop r₀] with r hr
    have hrpos : 0 < r := lt_of_lt_of_le hr₀ hr
    have hhr := hpos r (le_trans hrD hr)
    simp only [q, B]
    rw [Real.rpow_add hrpos, Real.rpow_one]
    field_simp
  intro ε hε
  have hupper : ∀ᶠ r in atTop,
      (∫ s in r₀..r, g s) / (r * B r) + q r₀ / (r * B r) < 1 / (b - c) + ε :=
    hlim.eventually (Iio_mem_nhds (by linarith))
  filter_upwards [hbound, hupper, hbase] with r hb hu heq
  rw [← heq]
  exact hb.trans hu.le

/-- **The normalized one-sided error** from the eventual `(1 + ε)` bound: a measurable `θ ≥ 1`
on `(0, ∞)` with `θ → 1` and `f' ≤ θ (a f + h) / r` on `(0, ∞)`. -/
theorem exists_normalized_error_of_bounded_ratio {f f' h : ℝ → ℝ} {a : ℝ} (ha : 0 < a)
    (hhm : Measurable h)
    (hpos : ∀ x, 0 < x → 0 < h x) (hfpos : ∀ x, 0 < x → 0 < f x)
    (hderiv : ∀ x, 0 < x → HasDerivAt f (f' x) x)
    (hfbd : ∀ ε > 0, ∀ᶠ x in atTop, f' x ≤ (1 + ε) * (a * f x + h x) / x) :
    ∃ θ, Measurable θ ∧ (∀ x, 0 < x → 1 ≤ θ x) ∧ Tendsto θ atTop (𝓝 1) ∧
      ∀ x, 0 < x → f' x ≤ θ x * (a * f x + h x) / x := by
  obtain ⟨f₀, hf0m, hf0eq, hf0d⟩ := exists_measurable_eq_and_hasDerivAt_of_hasDerivAt_Ioi hderiv
  have hden : ∀ x, 0 < x → 0 < a * f x + h x := fun x hx =>
    add_pos (mul_pos ha (hfpos x hx)) (hpos x hx)
  have hratio : ∀ x, 0 < x → deriv f₀ x * x / (a * f₀ x + h x) = f' x * x / (a * f x + h x) :=
    fun x hx => by rw [(hf0d x hx).deriv, hf0eq x hx]
  have hq : ∀ ε > 0, ∀ᶠ x in atTop, deriv f₀ x * x / (a * f₀ x + h x) ≤ 1 + ε := by
    intro ε hε
    filter_upwards [hfbd ε hε, eventually_gt_atTop (0 : ℝ)] with x hx hxpos
    rw [hratio x hxpos, div_le_iff₀ (hden x hxpos)]
    exact (le_div_iff₀ hxpos).mp hx
  set θ : ℝ → ℝ := (Ioi 0).indicator (fun r => max 1 (deriv f₀ r * r / (a * f₀ r + h r)))
    with hθ_def
  have hθx : ∀ x, 0 < x → θ x = max 1 (deriv f₀ x * x / (a * f₀ x + h x)) := fun x hx => by
    simp [θ, hx]
  have hθm : Measurable θ :=
    (measurable_const.max (((measurable_deriv f₀).mul measurable_id).div
      ((measurable_const.mul hf0m).add hhm))).indicator measurableSet_Ioi
  refine ⟨θ, hθm, fun x hx => (hθx x hx).symm ▸ le_max_left _ _, ?_, fun x hx => ?_⟩
  · rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨R, hR⟩ := eventually_atTop.1 (hq (ε / 2) (by linarith))
    refine ⟨max R 1, fun x hx => ?_⟩
    have hxpos : 0 < x := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hx)
    have hnear : θ x ≤ 1 + ε / 2 := by
      rw [hθx x hxpos]
      exact max_le (by linarith) (hR x (le_trans (le_max_left _ _) hx))
    have hge : 1 ≤ θ x := (hθx x hxpos).symm ▸ le_max_left _ _
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hge)]
    linarith
  · have hz : f' x * x / (a * f x + h x) ≤ θ x := (hratio x hx) ▸ (hθx x hx).symm ▸ le_max_right _ _
    rw [le_div_iff₀ hx]
    rw [div_le_iff₀ (hden x hx)] at hz
    exact hz

/-- **Lemma I.4.22.** Let `h > 0` be measurable and regularly varying of index `b`, let
`0 < a < b`, and let `f > 0` be differentiable on `(0, ∞)` with, for every `ε > 0`,
`f' ≤ (1 + ε) (a f + h) / r` eventually. Then for every `ε > 0`,
`f ≤ (1 + ε) h / (b - a)` eventually. -/
theorem eventually_le_one_add_mul_div_of_deriv_le {f f' h : ℝ → ℝ} {a b : ℝ}
    (hhm : Measurable h) (hh : RegularlyVarying b h) (ha : 0 < a) (hab : a < b)
    (hpos : ∀ x, 0 < x → 0 < h x) (hfpos : ∀ x, 0 < x → 0 < f x)
    (hderiv : ∀ x, 0 < x → HasDerivAt f (f' x) x)
    (hfbd : ∀ ε > 0, ∀ᶠ x in atTop, f' x ≤ (1 + ε) * (a * f x + h x) / x) :
    ∀ ε > 0, ∀ᶠ r in atTop, f r ≤ (1 + ε) * (h r / (b - a)) := by
  obtain ⟨x₀, -, hpos₀, hbdd⟩ := hh.exists_threshold (by linarith) hhm
  obtain ⟨θ, hθm, hθlower, hθ0, hfθbound⟩ :=
    exists_normalized_error_of_bounded_ratio ha hhm hpos hfpos hderiv hfbd
  intro ε hε
  set t : ℝ := Real.sqrt (1 + ε) - 1 with ht_def
  have hsq : (1 + t) ^ 2 = 1 + ε := by
    rw [ht_def, add_sub_cancel, Real.sq_sqrt (by linarith)]
  have hsqrt : 1 < Real.sqrt (1 + ε) := by
    rw [Real.lt_sqrt zero_le_one]
    linarith
  have ht : 0 < t := sub_pos.mpr hsqrt
  set c : ℝ := b - (b - a) / (1 + t) with hc_def
  have hgap : 0 < b - a := sub_pos.mpr hab
  have hgt0 : 0 < 1 + t := by linarith
  have hlt : (b - a) / (1 + t) < b - a := by
    apply (div_lt_iff₀ hgt0).2
    nlinarith [mul_pos hgap ht]
  have hq0 : 0 < (b - a) / (1 + t) := div_pos hgap hgt0
  have hca : a < c := by linarith
  have hcb : c < b := by linarith
  have hbcc : b - c = (b - a) / (1 + t) := by rw [hc_def]; ring
  have hsmall : 0 < min (c / a - 1) 1 :=
    lt_min (sub_pos.mpr ((lt_div_iff₀ ha).2 (by linarith))) one_pos
  obtain ⟨R, hR⟩ := Metric.tendsto_atTop.1 hθ0 (min (c / a - 1) 1) hsmall
  have hupper : ∀ x, R ≤ x → θ x ≤ min 2 (c / a) := by
    intro x hx
    have hd0 : |θ x - 1| < min (c / a - 1) 1 := by rw [← Real.dist_eq]; exact hR x hx
    have hd := abs_lt.1 hd0
    have h1 := min_le_left (c / a - 1) 1
    have h2 := min_le_right (c / a - 1) 1
    exact le_min (by linarith [hd.2]) (by linarith [hd.2])
  set R₀ := max 1 (max x₀ R)
  have hR₀1 : 1 ≤ R₀ := le_max_left _ _
  have hR₀pos : 0 < R₀ := lt_of_lt_of_le one_pos hR₀1
  have hR₀D : x₀ ≤ R₀ := le_trans (le_max_left _ _) (le_max_right _ _)
  have hR₀R : R ≤ R₀ := le_trans (le_max_right _ _) (le_max_right _ _)
  have hu := eventually_ratio_le_of_driving_bound hhm hh ha hcb hR₀pos hR₀1 hpos₀ hbdd hR₀D
    (fun x hx => hderiv x (lt_of_lt_of_le hR₀pos hx))
    (fun x hx => hfpos x (lt_of_lt_of_le hR₀pos hx)) hθm
    (fun x hx => hθlower x (lt_of_lt_of_le hR₀pos hx))
    (fun x hx => hupper x (le_trans hR₀R hx)) hθ0
    (fun x hx => hfθbound x (lt_of_lt_of_le hR₀pos hx))
    (t / (b - a)) (div_pos ht hgap)
  filter_upwards [hu, eventually_gt_atTop (0 : ℝ)] with r hu hr
  have hhr := hpos r hr
  have hbc : 0 < b - c := sub_pos.mpr hcb
  -- `(b - a) (1 / (b - c) + t / (b - a)) = 1 + 2 t ≤ (1 + t) ^ 2 = 1 + ε`
  have hbudget : (b - a) * (1 / (b - c) + t / (b - a)) = 1 + 2 * t := by
    rw [hbcc]
    field_simp
    ring
  have hgf : (b - a) * (f r / h r) ≤ 1 + ε := by
    calc (b - a) * (f r / h r) ≤ (b - a) * (1 / (b - c) + t / (b - a)) :=
          mul_le_mul_of_nonneg_left hu hgap.le
      _ = 1 + 2 * t := hbudget
      _ ≤ 1 + ε := by nlinarith [sq_nonneg t]
  rw [mul_div_assoc', le_div_iff₀ hgap]
  rw [mul_div_assoc', div_le_iff₀ hhr] at hgf
  linarith

/-! ## Lemma I.5.5 in the case `b < a` -/

/-- **Lemma I.5.5 for `b < a`, with `f` measurable**: the forcing term is negligible. If `h` is
measurable, positive and regularly varying of index `b`, `0 < b < a`, and `f > 0` is measurable
and differentiable on `(0, ∞)` with `f' / ((a f + h) / r) → 1`, then `f` is regularly varying of
index `a`, `h / f → 0` and `f' / (a f / r) → 1`. -/
theorem regularlyVarying_and_tendsto_of_tendsto_deriv_ratio_of_lt_of_measurable
    {f f' h : ℝ → ℝ} {a b : ℝ}
    (hhm : Measurable h) (hh : RegularlyVarying b h) (hb : 0 < b) (ha : 0 < a) (hab : b < a)
    (hpos : ∀ x, 0 < x → 0 < h x) (hfpos : ∀ x, 0 < x → 0 < f x)
    (hfm : Measurable f)
    (hderiv : ∀ x, 0 < x → HasDerivAt f (f' x) x)
    (hasym : Tendsto (fun r => f' r / ((a * f r + h r) / r)) atTop (𝓝 1)) :
    RegularlyVarying a f ∧ Tendsto (fun r => h r / f r) atTop (𝓝 0) ∧
      Tendsto (fun r => f' r / (a * f r / r)) atTop (𝓝 1) := by
  obtain ⟨x₀, -, hpos₀, hbdd⟩ := hh.exists_threshold hb hhm
  obtain ⟨r₀, δ, hr₀, -, hrD, hδm, hδ0, hδ1, hode⟩ :=
    exists_shared_error_of_tendsto x₀ hhm hderiv hasym
  set w : ℝ → ℝ := fun r => r ^ a * Real.exp (-(a * ∫ s in r₀..r, (Ioi r₀).indicator δ s / s))
    with hw_def
  set g : ℝ → ℝ := fun s => h s / w s / s with hg_def
  set T : ℝ → ℝ := (Ioi r₀).indicator g with hT_def
  set q : ℝ → ℝ := fun r => f r * (w r)⁻¹ with hq_def
  have hwrv : RegularlyVarying a w := regularlyVarying_rpow_mul_exp_neg_integral ha hr₀ hδm hδ0 hδ1
  have hwm : Measurable w := measurable_rpow_mul_exp_neg_integral a hr₀ hδm hδ1
  have hwpos : ∀ s, 0 < s → 0 < w s := fun s hs => rpow_mul_exp_neg_integral_pos hs
  have hgrv : RegularlyVarying (b - a - 1) g := by
    have h1 := (hh.mul hwrv.inv).mul (regularlyVarying_rpow 1).inv
    rw [show b + -a + -1 = b - a - 1 by ring] at h1
    refine h1.congr' (Eventually.of_forall fun s => ?_)
    simp [g, div_eq_mul_inv, Real.rpow_one]
  have hgm : Measurable g := (hhm.div hwm).div measurable_id
  have hgpos : ∀ s, 0 < s → 0 < g s := fun s hs => div_pos (div_pos (hpos s hs) (hwpos s hs)) hs
  have hwcont : ContinuousOn w (Ici r₀) := by
    intro s hs
    have hs0 : 0 < s := lt_of_lt_of_le hr₀ hs
    exact ((Real.continuousAt_rpow_const s a (Or.inl hs0.ne')).mul
      (Real.continuous_exp.continuousAt.comp
        (((continuous_intervalIntegral_indicator_Ioi_div hr₀ hδm hδ1).continuousAt.const_mul
          a).neg))).continuousWithinAt
  have hgint : ∀ x y : ℝ, r₀ ≤ x → x ≤ y → IntervalIntegrable g volume x y := by
    intro x y hx hxy
    obtain ⟨C, hC⟩ := hbdd y
    have hIc : IntegrableOn h (Icc x y) volume := by
      refine IntegrableOn.of_bound measure_Icc_lt_top hhm.aestronglyMeasurable C ?_
      filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
      rw [Real.norm_eq_abs, abs_of_pos (hpos₀ s ((le_trans hrD hx).trans hs.1))]
      exact hC s ((le_trans hrD hx).trans hs.1) hs.2
    have hcont : ContinuousOn (fun s => (s * w s)⁻¹) (Icc x y) := by
      apply (continuousOn_id.mul (hwcont.mono (fun s hs => le_trans hx hs.1))).inv₀
      intro s hs
      have hs0 : 0 < s := (lt_of_lt_of_le hr₀ hx).trans_le hs.1
      exact (mul_pos hs0 (hwpos s hs0)).ne'
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hxy]
    refine (hIc.mul_continuousOn hcont isCompact_Icc).congr_fun (fun s _ => ?_) measurableSet_Icc
    simp only [g, div_eq_mul_inv, mul_inv]
    ring
  have hTloc : LocallyIntegrableOn T (Ioi 0) :=
    locallyIntegrableOn_indicator_Ioi_of_intervalIntegrable hgint
  have hTm : Measurable T := hgm.indicator measurableSet_Ioi
  have hbase : IntegrableOn T (Ioi r₀) :=
    integrableOn_Ioi_of_regularlyVarying (by linarith) hTm hTloc
      (regularlyVarying_indicator_Ioi hgrv) r₀ hr₀
  have hweighted : IntegrableOn (fun s => (1 - δ s) * g s) (Ioi r₀) := by
    refine Integrable.mono' (hbase.norm.const_mul 2)
      ((measurable_const.sub hδm).mul hgm).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hd := hδ1 x (le_of_lt hx)
    have hfac : |1 - δ x| ≤ 2 := by
      calc |1 - δ x| ≤ |1| + |δ x| := abs_sub _ _
        _ ≤ 2 := by rw [abs_one]; linarith
    rw [show T x = g x by simp [T, mem_Ioi.1 hx], norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right hfac (norm_nonneg _)
  have hqinc : ∀ᶠ R in atTop, q R - q r₀ = ∫ s in r₀..R, (1 - δ s) * g s := by
    filter_upwards [eventually_ge_atTop r₀] with R hR
    have h1 := normalized_increment_of_driving_ode ha hr₀ hR hpos₀ hbdd hrD
      (fun x hx => hderiv x (lt_of_lt_of_le hr₀ hx)) hδm hδ1 hode
    simp only [q, w, g]
    rw [h1]
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [div_eq_mul_inv, mul_inv]
    ring
  set L := q r₀ + ∫ s in Ioi r₀, (1 - δ s) * g s with hL_def
  have hlimq : Tendsto q atTop (𝓝 L) := by
    have hdiff : Tendsto (fun r => q r - q r₀) atTop (𝓝 (∫ s in Ioi r₀, (1 - δ s) * g s)) :=
      (intervalIntegral_tendsto_integral_Ioi r₀ hweighted tendsto_id).congr'
        (by filter_upwards [hqinc] with r hr; exact hr.symm)
    simpa using hdiff.const_add (q r₀)
  have hq0 : 0 < q r₀ := mul_pos (hfpos r₀ hr₀) (inv_pos.mpr (hwpos r₀ hr₀))
  have htail : 0 ≤ ∫ s in Ioi r₀, (1 - δ s) * g s := by
    apply setIntegral_nonneg measurableSet_Ioi
    intro s hs
    have hd := (abs_le.1 (hδ1 s (le_of_lt hs))).2
    exact mul_nonneg (sub_nonneg.mpr hd) (hgpos s (lt_trans hr₀ hs)).le
  have hLpos : 0 < L := add_pos_of_pos_of_nonneg hq0 htail
  -- `q` has a positive limit, so it is slowly varying
  have hqrv : RegularlyVarying 0 q := by
    refine RegularlyVarying.of_tendsto_div
      ((slowlyVarying_iff_regularlyVarying_zero).1 (slowlyVarying_const hLpos)) ?_
      ⟨0, measurable_restrict_Ici_of_measurable (hfm.mul hwm.inv) 0⟩
    simpa [div_self hLpos.ne'] using hlimq.div_const L
  have hfrv : RegularlyVarying a f := by
    refine (by simpa using hwrv.mul hqrv : RegularlyVarying a (fun r => w r * q r)).congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    have := hwpos r hr
    simp only [q]
    field_simp
  have hf0 : Tendsto (fun r => h r / f r) atTop (𝓝 0) := by
    have hratio : RegularlyVarying (b - a) (fun r => h r / f r) := by
      have h1 := hh.mul hfrv.inv
      rw [← sub_eq_add_neg] at h1
      simpa [div_eq_mul_inv] using h1
    exact (isLogErrorFunction_of_regularlyVarying (by linarith) (hhm.div hfm) hratio).2
  refine ⟨hfrv, hf0, ?_⟩
  have hterm : Tendsto (fun r => (1 - δ r) * (1 + a⁻¹ * (h r / f r))) atTop (𝓝 1) := by
    simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub hδ0).mul
      ((hf0.const_mul a⁻¹).const_add 1)
  apply hterm.congr'
  filter_upwards [eventually_ge_atTop r₀] with r hr
  have hrpos : 0 < r := lt_of_lt_of_le hr₀ hr
  have hfr := hfpos r hrpos
  rw [hode r hr]
  field_simp

/-- **Lemma I.5.5 for `b < a`**: as
`regularlyVarying_and_tendsto_of_tendsto_deriv_ratio_of_lt_of_measurable`, without the
measurability hypothesis on `f`. -/
theorem regularlyVarying_and_tendsto_of_tendsto_deriv_ratio_of_lt {f f' h : ℝ → ℝ} {a b : ℝ}
    (hhm : Measurable h) (hh : RegularlyVarying b h) (hb : 0 < b) (ha : 0 < a) (hab : b < a)
    (hpos : ∀ x, 0 < x → 0 < h x) (hfpos : ∀ x, 0 < x → 0 < f x)
    (hderiv : ∀ x, 0 < x → HasDerivAt f (f' x) x)
    (hasym : Tendsto (fun r => f' r / ((a * f r + h r) / r)) atTop (𝓝 1)) :
    RegularlyVarying a f ∧ Tendsto (fun r => h r / f r) atTop (𝓝 0) ∧
      Tendsto (fun r => f' r / (a * f r / r)) atTop (𝓝 1) := by
  obtain ⟨f₀, hf0m, hf0eq, hf0d⟩ := exists_measurable_eq_and_hasDerivAt_of_hasDerivAt_Ioi hderiv
  have hev : f₀ =ᶠ[atTop] f := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact hf0eq x hx
  have hasym0 : Tendsto (fun r => f' r / ((a * f₀ r + h r) / r)) atTop (𝓝 1) := by
    apply hasym.congr'
    filter_upwards [hev] with x hx
    rw [hx]
  obtain ⟨hfrv, hf0, hder⟩ :=
    regularlyVarying_and_tendsto_of_tendsto_deriv_ratio_of_lt_of_measurable hhm hh hb ha hab hpos
      (fun x hx => (hf0eq x hx).symm ▸ hfpos x hx) hf0m hf0d hasym0
  refine ⟨hfrv.congr' hev, hf0.congr' ?_, hder.congr' ?_⟩ <;>
    filter_upwards [hev] with x hx <;> rw [hx]

end PercLib.Analysis
