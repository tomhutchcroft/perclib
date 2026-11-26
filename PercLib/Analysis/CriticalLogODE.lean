/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
The driven ODE with a critical forcing term and a logarithmically integrable error: Lemma I.5.6
of T. Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, §I.5.1.

Adapted from the repository `yujinhkim/lrp`, branch `critical-lrp-1`, commit
`d382e4c28d92dd4e698ebf4f2aaf0bc932ae73fc`, file
`PercLib/CriticalLRP/Analysis/Lemma_I_5_6.lean`; licence Apache-2.0 as declared in that commit's
file headers and `third_party/critical-lrp/NOTICE.md`; upstream
`yujinhkim/Critical-Long-range-percolation` at `3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf`.
Modified: `RegularlyVaryingAtTop h a` becomes `RegularlyVarying a h` of
`PercLib/Analysis/RegularVariation/Defs.lean`, which contains the eventual positivity of `h`; the
structure `RVPosData` is unbundled, and a threshold for the forcing term is obtained from
`RegularlyVarying.exists_threshold`; the definitions `errorTail` and `powerExpWeight` are written
out; the error functions are measurable only on a tail, as in the library's `IsLogErrorFunction`,
and are replaced by measurable modifications; positivity and differentiability of `f` and the
differential equation are assumed only eventually; the measurability hypothesis on the second
error is removed, a measurable forcing term being built from the equation; the hypothesis
`RegularlyVaryingAtTop h a` is removed from the logarithmic corollaries, where it follows from
`h ∼ A r ^ a`; declarations are renamed; `autoImplicit`, disabled linters and `#print` lines are
removed. The source file `PercLib/CriticalLRP/Analysis/LogPrimitive.lean` is not ported: its
only theorem is `tendsto_karamataPrimitive_tail` of
`PercLib/Analysis/RegularVariation/KaramataPrimitive.lean`.
-/
module

public import PercLib.Analysis.CriticalDrivenODE

/-! # The critical driven ODE with a logarithmically integrable error

Let `h` be measurable and regularly varying of index `a > 0`, and let `f` be eventually positive
and differentiable with `f' = (1 - δ) a f / r + h / r` on a tail, where `δ` is a logarithmically
integrable error function. With the integrating weight
`w r = r ^ a * exp (-(a * ∫ s in r₀..r, (Ioi r₀).indicator δ s / s))`, which satisfies
`w r / r ^ a → A > 0`, the normalized function `f / w` has the primitive `h / (r w)`. Hence:

* if `h / r ^ a` is not logarithmically integrable, `f r ∼ r ^ a ∫_{r₀}^r h s / s ^ (a + 1) ds`;
* if it is, `f r / r ^ a` has a positive limit.

## Main results

* `exists_tendsto_of_critical_log_error_ode`: Lemma I.5.6 for `f' = (1 - δ) a f / r + h / r`.
* `tendsto_div_mul_rpow_mul_log_of_critical_log_error_ode`: if moreover `h ∼ A r ^ a`, then
  `f ∼ A r ^ a log r`.
* `exists_tendsto_of_critical_two_error_ode`: Lemma I.5.6 for
  `f' = ((1 - δ₁) a f + (1 - δ₂) h) / r`, with `δ₁` a logarithmically integrable error function
  and `δ₂ → 0`.
* `tendsto_div_mul_rpow_mul_log_of_critical_two_error_ode`: its logarithmic corollary.
-/

@[expose] public section

open Filter Set MeasureTheory
open scoped Topology

namespace PercLib.Analysis

/-- **Lemma I.5.6, one-error form.** Let `h` be measurable and regularly varying of index `a > 0`,
let `δ` be a logarithmically integrable error function, and let `f` be eventually positive and
differentiable with `f' = (1 - δ) a f / r + h / r` eventually. Then for every `R` there is
`r₀ ≥ R`, `r₀ > 0`, such that `h s / s ^ (a + 1)` is interval integrable on `[r₀, ∞)`, and

* if `h / r ^ a` is not logarithmically integrable, then
  `f r / (r ^ a ∫_{r₀}^r h s / s ^ (a + 1) ds) → 1`;
* if `h / r ^ a` is logarithmically integrable, then `f r / r ^ a → A` for some `A > 0`. -/
theorem exists_tendsto_of_critical_log_error_ode {f f' h δ : ℝ → ℝ} {a R : ℝ} (ha : 0 < a)
    (hhm : Measurable h) (hh : RegularlyVarying a h)
    (hfpos : ∀ᶠ x in atTop, 0 < f x)
    (hderiv : ∀ᶠ x in atTop, HasDerivAt f (f' x) x)
    (hδ : IsLogErrorFunction δ)
    (hode : ∀ᶠ x in atTop, f' x = (1 - δ x) * a * f x / x + h x / x) :
    ∃ r₀ : ℝ, R ≤ r₀ ∧ 0 < r₀ ∧
      (∀ x y : ℝ, r₀ ≤ x → x ≤ y →
        IntervalIntegrable (fun s => h s / s ^ (a + 1)) volume x y) ∧
      (¬ LogarithmicallyIntegrable (fun r => h r / r ^ a) →
        Tendsto (fun r => f r / (r ^ a * ∫ s in r₀..r, h s / s ^ (a + 1))) atTop (𝓝 1)) ∧
      (LogarithmicallyIntegrable (fun r => h r / r ^ a) →
        ∃ A : ℝ, 0 < A ∧ Tendsto (fun r => f r / r ^ a) atTop (𝓝 A)) := by
  obtain ⟨x₀, -, hpos, hbdd⟩ := hh.exists_threshold ha hhm
  obtain ⟨c, hc⟩ := hδ.1.1
  obtain ⟨D, hDm, hDeq⟩ := exists_measurable_eqOn_Ici hc
  have hDδ : D =ᶠ[atTop] δ := by
    filter_upwards [eventually_ge_atTop c] with x hx using hDeq x hx
  have hDlog : LogarithmicallyIntegrable D :=
    hδ.1.mono ⟨0, measurable_restrict_Ici_of_measurable hDm 0⟩
      (hDδ.mono fun x hx => by rw [hx])
  have hD0 : Tendsto D atTop (𝓝 0) := hδ.2.congr' hDδ.symm
  obtain ⟨B, hB⟩ := eventually_atTop.1 (hfpos.and (hderiv.and (hode.and
    (hD0.eventually (Metric.closedBall_mem_nhds (0 : ℝ) one_pos)))))
  set r₀ : ℝ := max (max R (max 1 x₀)) (max c B) with hr₀_def
  have hrR : R ≤ r₀ := (le_max_left _ _).trans (le_max_left _ _)
  have hr₀1 : 1 ≤ r₀ := ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_left _ _)
  have hrx₀ : x₀ ≤ r₀ := ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_left _ _)
  have hrc : c ≤ r₀ := (le_max_left _ _).trans (le_max_right _ _)
  have hrB : B ≤ r₀ := (le_max_right _ _).trans (le_max_right _ _)
  have hr₀ : 0 < r₀ := zero_lt_one.trans_le hr₀1
  have hfr : ∀ x, r₀ ≤ x → 0 < f x := fun x hx => (hB x (hrB.trans hx)).1
  have hder : ∀ x, r₀ ≤ x → HasDerivAt f (f' x) x := fun x hx => (hB x (hrB.trans hx)).2.1
  have hodeD : ∀ x, r₀ ≤ x → f' x = (1 - D x) * a * f x / x + h x / x := by
    intro x hx
    rw [hDeq x (hrc.trans hx)]
    exact (hB x (hrB.trans hx)).2.2.1
  have hD1 : ∀ x, r₀ ≤ x → |D x| ≤ 1 := by
    intro x hx
    have h1 := (hB x (hrB.trans hx)).2.2.2
    rwa [Real.dist_eq, sub_zero] at h1
  set w : ℝ → ℝ := fun r => r ^ a * Real.exp (-(a * ∫ s in r₀..r, (Ioi r₀).indicator D s / s))
    with hw_def
  have hwm : Measurable w := measurable_rpow_mul_exp_neg_integral a hr₀ hDm hD1
  have hwpos : ∀ s, 0 < s → 0 < w s := fun s hs => rpow_mul_exp_neg_integral_pos hs
  obtain ⟨A, hA, hElim⟩ := exists_pos_tendsto_rpow_mul_exp_neg_integral_div_rpow (a := a) hr₀
    hDm hD1 hDlog
  set E : ℝ → ℝ := fun r => w r / r ^ a with hE_def
  set v : ℝ → ℝ := fun s => h s / w s with hv_def
  set u : ℝ → ℝ := fun r => h r / r ^ a with hu_def
  set U : ℝ → ℝ := fun s => h s / s ^ (a + 1) with hU_def
  set g : ℝ → ℝ := fun s => v s / s with hg_def
  set q : ℝ → ℝ := fun r => f r * (w r)⁻¹ with hq_def
  have hum : Measurable u := hhm.div (measurable_id.pow_const a)
  have hvm : Measurable v := hhm.div hwm
  have hEm : Measurable E := hwm.div (measurable_id.pow_const a)
  have hEpos : ∀ x, 0 < x → 0 < E x := fun x hx =>
    div_pos (hwpos x hx) (Real.rpow_pos_of_pos hx a)
  have hvpos : ∀ x, r₀ ≤ x → 0 < v x := fun x hx =>
    div_pos (hpos x (hrx₀.trans hx)) (hwpos x (hr₀.trans_le hx))
  have hgpos : ∀ x, r₀ ≤ x → 0 < g x := fun x hx => div_pos (hvpos x hx) (hr₀.trans_le hx)
  have hupos : ∀ x, r₀ ≤ x → 0 < u x := fun x hx =>
    div_pos (hpos x (hrx₀.trans hx)) (Real.rpow_pos_of_pos (hr₀.trans_le hx) a)
  have hUpos : ∀ x, r₀ ≤ x → 0 < U x := fun x hx =>
    div_pos (hpos x (hrx₀.trans hx)) (Real.rpow_pos_of_pos (hr₀.trans_le hx) (a + 1))
  have hU_u : ∀ x, 0 < x → U x = u x / x := by
    intro x hx
    simp only [U, u]
    rw [Real.rpow_add hx, Real.rpow_one, div_div]
  have hwcont : ContinuousOn w (Ici r₀) := by
    intro s hs
    have hs0 : 0 < s := lt_of_lt_of_le hr₀ hs
    exact ((Real.continuousAt_rpow_const s a (Or.inl hs0.ne')).mul
      (Real.continuous_exp.continuousAt.comp
        (((continuous_intervalIntegral_indicator_Ioi_div hr₀ hDm hD1).continuousAt.const_mul
          a).neg))).continuousWithinAt
  have hIc : ∀ x y, r₀ ≤ x → IntegrableOn h (Icc x y) volume := by
    intro x y hx
    obtain ⟨C, hC⟩ := hbdd y
    refine IntegrableOn.of_bound measure_Icc_lt_top hhm.aestronglyMeasurable C ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    rw [Real.norm_eq_abs, abs_of_pos (hpos s ((hrx₀.trans hx).trans hs.1))]
    exact hC s ((hrx₀.trans hx).trans hs.1) hs.2
  have hgint : ∀ x y : ℝ, r₀ ≤ x → x ≤ y → IntervalIntegrable g volume x y := by
    intro x y hx hxy
    have hcont : ContinuousOn (fun s => (s * w s)⁻¹) (Icc x y) := by
      apply (continuousOn_id.mul (hwcont.mono (fun s hs => le_trans hx hs.1))).inv₀
      intro s hs
      have hs0 : 0 < s := (lt_of_lt_of_le hr₀ hx).trans_le hs.1
      exact (mul_pos hs0 (hwpos s hs0)).ne'
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hxy]
    refine ((hIc x y hx).mul_continuousOn hcont isCompact_Icc).congr_fun (fun s _ => ?_)
      measurableSet_Icc
    simp only [g, v, div_eq_mul_inv, mul_inv]
    ring
  have hUint : ∀ x y : ℝ, r₀ ≤ x → x ≤ y → IntervalIntegrable U volume x y := by
    intro x y hx hxy
    have hcont : ContinuousOn (fun s : ℝ => (s ^ (a + 1))⁻¹) (Icc x y) := by
      apply ContinuousOn.inv₀
      · intro s hs
        exact (Real.continuousAt_rpow_const s (a + 1)
          (Or.inl ((hr₀.trans_le (hx.trans hs.1)).ne'))).continuousWithinAt
      · intro s hs
        exact (Real.rpow_pos_of_pos ((hr₀.trans_le hx).trans_le hs.1) (a + 1)).ne'
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hxy]
    exact (hIc x y hx).mul_continuousOn hcont isCompact_Icc
  have hqinc : ∀ R, r₀ ≤ R → q R - q r₀ = ∫ s in r₀..R, g s := by
    intro R hR
    have h1 := normalized_increment_of_unweighted_driving_ode hr₀ hR hpos hbdd hrx₀ hder hDm hD1
      hodeD
    simp only [q, w, g, v]
    rw [h1]
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [div_eq_mul_inv, mul_inv]
    ring
  have hq₀ : 0 < q r₀ := mul_pos (hfr r₀ le_rfl) (inv_pos.2 (hwpos r₀ hr₀))
  have hfwq : ∀ r, 0 < r → f r = w r * q r := by
    intro r hr0
    have := hwpos r hr0
    simp only [q]
    field_simp
  have huv : (fun r => u r / E r) =ᶠ[atTop] v := by
    filter_upwards [eventually_ge_atTop r₀] with r hr
    have hr0 : 0 < r := hr₀.trans_le hr
    have := (Real.rpow_pos_of_pos hr0 a).ne'
    have := (hwpos r hr0).ne'
    simp only [u, E, v]
    field_simp
  have hlogv : LogarithmicallyIntegrable u → LogarithmicallyIntegrable v := fun hu =>
    (logarithmicallyIntegrable_div_of_tendsto_pos hA hElim hu hEm).mono
      ⟨0, measurable_restrict_Ici_of_measurable hvm 0⟩ (huv.mono fun r hr => by rw [← hr])
  have hloginv : LogarithmicallyIntegrable v → LogarithmicallyIntegrable u := by
    intro hv
    have huvi : (fun r => v r / (E r)⁻¹) =ᶠ[atTop] u := by
      filter_upwards [eventually_ge_atTop r₀, huv] with r hr heq
      have := (hEpos r (hr₀.trans_le hr)).ne'
      rw [← heq]
      field_simp
    exact (logarithmicallyIntegrable_div_of_tendsto_pos (inv_pos.mpr hA) (hElim.inv₀ hA.ne') hv
      hEm.inv).mono ⟨0, measurable_restrict_Ici_of_measurable hum 0⟩
        (huvi.mono fun r hr => by rw [← hr])
  refine ⟨r₀, hrR, hr₀, hUint, fun hnot => ?_, fun hulog => ?_⟩
  · change ¬ LogarithmicallyIntegrable u at hnot
    change Tendsto (fun r => f r / (r ^ a * ∫ s in r₀..r, U s)) atTop (𝓝 1)
    have hnotg : ¬ IntegrableOn g (Ioi r₀) volume := by
      intro hgi
      refine hnot (hloginv ⟨⟨0, measurable_restrict_Ici_of_measurable hvm 0⟩, r₀, hr₀, ?_⟩)
      refine hgi.congr_fun (fun s hs => ?_) measurableSet_Ioi
      simp only [g]
      rw [abs_of_pos (hvpos s (le_of_lt hs))]
    have hGinf : Tendsto (fun r => ∫ s in r₀..r, g s) atTop atTop :=
      tendsto_intervalIntegral_atTop_of_not_integrableOn hgint (fun x hx => (hgpos x hx).le)
        hnotg
    have hqdiff : Tendsto (fun r => (q r - q r₀) / ∫ s in r₀..r, g s) atTop (𝓝 1) := by
      have hIFG := tendsto_intervalIntegral_div_of_tendsto_ratio hgpos
        (tendsto_const_nhds.congr' (by
          filter_upwards [eventually_ge_atTop r₀] with r hr
          exact (div_self (hgpos r hr).ne').symm)) hgint hgint hGinf
      refine hIFG.congr' ?_
      filter_upwards [eventually_ge_atTop r₀] with r hr
      rw [hqinc r hr]
    have hzero : Tendsto (fun r => q r₀ / ∫ s in r₀..r, g s) atTop (𝓝 0) := by
      simpa [div_eq_mul_inv] using hGinf.inv_tendsto_atTop.const_mul (q r₀)
    have hqG : Tendsto (fun r => q r / ∫ s in r₀..r, g s) atTop (𝓝 1) := by
      have hsum := hqdiff.add hzero
      rw [add_zero] at hsum
      refine hsum.congr' ?_
      filter_upwards [hGinf.eventually (eventually_gt_atTop 0)] with r hrG
      rw [← add_div, sub_add_cancel]
    have hnotU : ¬ IntegrableOn U (Ioi r₀) volume := by
      intro hUi
      refine hnot ⟨⟨0, measurable_restrict_Ici_of_measurable hum 0⟩, r₀, hr₀, ?_⟩
      refine hUi.congr_fun (fun s hs => ?_) measurableSet_Ioi
      rw [hU_u s (hr₀.trans hs), abs_of_pos (hupos s (le_of_lt hs))]
    have hUinf : Tendsto (fun r => ∫ s in r₀..r, U s) atTop atTop :=
      tendsto_intervalIntegral_atTop_of_not_integrableOn hUint (fun x hx => (hUpos x hx).le)
        hnotU
    have hgU : Tendsto (fun r => g r / U r) atTop (𝓝 A⁻¹) := by
      refine (hElim.inv₀ hA.ne').congr' ?_
      filter_upwards [eventually_ge_atTop r₀, huv] with r hr heq
      have hr0 : 0 < r := hr₀.trans_le hr
      have := (hEpos r hr0).ne'
      have := (hupos r hr).ne'
      rw [hU_u r hr0]
      simp only [g]
      rw [← heq]
      field_simp
    have hGU := tendsto_intervalIntegral_div_of_tendsto_ratio hUpos hgU hgint hUint hUinf
    have hqU : Tendsto (fun r => q r / ∫ s in r₀..r, U s) atTop (𝓝 A⁻¹) := by
      have hqUprod := hqG.mul hGU
      rw [one_mul] at hqUprod
      refine hqUprod.congr' ?_
      filter_upwards [hGinf.eventually (eventually_gt_atTop 0)] with r hrG
      field_simp
    have hmul := hElim.mul hqU
    rw [mul_inv_cancel₀ hA.ne'] at hmul
    refine hmul.congr' ?_
    filter_upwards [eventually_ge_atTop r₀] with r hr
    have hr0 : 0 < r := hr₀.trans_le hr
    have := (Real.rpow_pos_of_pos hr0 a).ne'
    rw [hfwq r hr0]
    simp only [E]
    field_simp
  · change LogarithmicallyIntegrable u at hulog
    have hIg : IntegrableOn g (Ioi r₀) volume :=
      integrableOn_div_of_logarithmicallyIntegrable hr₀ hgint (hlogv hulog)
    have hlimq : Tendsto q atTop (𝓝 (q r₀ + ∫ s in Ioi r₀, g s)) := by
      have hdiff : Tendsto (fun r => q r - q r₀) atTop (𝓝 (∫ s in Ioi r₀, g s)) :=
        (intervalIntegral_tendsto_integral_Ioi r₀ hIg tendsto_id).congr' (by
          filter_upwards [eventually_ge_atTop r₀] with r hr
          exact (hqinc r hr).symm)
      simpa using hdiff.const_add (q r₀)
    have htail : 0 ≤ ∫ s in Ioi r₀, g s := by
      refine integral_nonneg_of_ae ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact (hgpos s (le_of_lt hs)).le
    refine ⟨A * (q r₀ + ∫ s in Ioi r₀, g s), mul_pos hA (add_pos_of_pos_of_nonneg hq₀ htail),
      (hElim.mul hlimq).congr' ?_⟩
    filter_upwards [eventually_ge_atTop r₀] with r hr
    have hr0 : 0 < r := hr₀.trans_le hr
    have := (Real.rpow_pos_of_pos hr0 a).ne'
    rw [hfwq r hr0]
    simp only [E]
    field_simp

/-- `h ∼ A r ^ a` with `A > 0` and `h` measurable makes `h` regularly varying of index `a`. -/
private theorem regularlyVarying_of_tendsto_div_const_mul_rpow {h : ℝ → ℝ} {a A : ℝ}
    (hA : 0 < A) (hhm : Measurable h)
    (hhA : Tendsto (fun r => h r / (A * r ^ a)) atTop (𝓝 1)) : RegularlyVarying a h :=
  ((regularlyVarying_rpow a).const_mul hA).of_tendsto_div hhA
    ⟨0, measurable_restrict_Ici_of_measurable hhm 0⟩

/-- From `h ∼ A r ^ a`: `h / r ^ a` is not logarithmically integrable, and
`h s / s ^ (a + 1) ∼ A / s`. -/
private theorem not_logarithmicallyIntegrable_and_tendsto_of_tendsto_div_const_mul_rpow
    {h : ℝ → ℝ} {a A : ℝ} (hA : 0 < A)
    (hhA : Tendsto (fun r => h r / (A * r ^ a)) atTop (𝓝 1)) :
    ¬ LogarithmicallyIntegrable (fun r => h r / r ^ a) ∧
      Tendsto (fun s => h s / s ^ (a + 1) / (A / s)) atTop (𝓝 1) := by
  refine ⟨not_logarithmicallyIntegrable_of_tendsto_pos hA ?_, hhA.congr' ?_⟩
  · have hm := hhA.const_mul A
    rw [mul_one] at hm
    refine hm.congr' (Eventually.of_forall fun r => ?_)
    simp only
    rw [mul_div_assoc', mul_div_mul_left _ _ hA.ne']
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
    have := (Real.rpow_pos_of_pos hs a).ne'
    rw [Real.rpow_add hs, Real.rpow_one]
    field_simp

/-- The last step of the logarithmic corollaries: from
`f r / (r ^ a ∫_{r₀}^r U) → 1` and `U s ∼ A / s`, `f r / (A r ^ a log r) → 1`. -/
private theorem tendsto_div_mul_rpow_mul_log_of_tendsto_div_intervalIntegral
    {f U : ℝ → ℝ} {a A r₀ : ℝ} (hr₀ : 0 < r₀) (hA : 0 < A)
    (hUA : Tendsto (fun s => U s / (A / s)) atTop (𝓝 1))
    (hUint : ∀ x y : ℝ, r₀ ≤ x → x ≤ y → IntervalIntegrable U volume x y)
    (hmain : Tendsto (fun r => f r / (r ^ a * ∫ s in r₀..r, U s)) atTop (𝓝 1)) :
    Tendsto (fun r => f r / (A * r ^ a * Real.log r)) atTop (𝓝 1) := by
  have hUlog := tendsto_intervalIntegral_div_mul_log hr₀ hA hUA hUint
  have hmul := hmain.mul hUlog
  rw [mul_one] at hmul
  refine hmul.congr' ?_
  filter_upwards [eventually_gt_atTop (max r₀ 1),
    hUlog.eventually (eventually_gt_nhds zero_lt_one)] with r hr hratio
  have hr1 : 1 < r := (le_max_right _ _).trans_lt hr
  have hr0 : 0 < r := zero_lt_one.trans hr1
  have hlog := Real.log_pos hr1
  have hIU : 0 < ∫ s in r₀..r, U s := (div_pos_iff_of_pos_right (mul_pos hA hlog)).mp hratio
  have := (Real.rpow_pos_of_pos hr0 a).ne'
  have := hA.ne'
  have := hlog.ne'
  have := hIU.ne'
  field_simp

/-- **Logarithmic corollary of Lemma I.5.6, one-error form.** If moreover `h ∼ A r ^ a` with
`A > 0`, then `f ∼ A r ^ a log r`. -/
theorem tendsto_div_mul_rpow_mul_log_of_critical_log_error_ode {f f' h δ : ℝ → ℝ} {a A : ℝ}
    (ha : 0 < a) (hA : 0 < A) (hhm : Measurable h)
    (hfpos : ∀ᶠ x in atTop, 0 < f x)
    (hderiv : ∀ᶠ x in atTop, HasDerivAt f (f' x) x)
    (hδ : IsLogErrorFunction δ)
    (hode : ∀ᶠ x in atTop, f' x = (1 - δ x) * a * f x / x + h x / x)
    (hhA : Tendsto (fun r => h r / (A * r ^ a)) atTop (𝓝 1)) :
    Tendsto (fun r => f r / (A * r ^ a * Real.log r)) atTop (𝓝 1) := by
  obtain ⟨hnot, hUA⟩ :=
    not_logarithmicallyIntegrable_and_tendsto_of_tendsto_div_const_mul_rpow hA hhA
  obtain ⟨r₀, -, hr₀, hUint, hnon, -⟩ := exists_tendsto_of_critical_log_error_ode (R := 0) ha hhm
    (regularlyVarying_of_tendsto_div_const_mul_rpow hA hhm hhA) hfpos hderiv hδ hode
  exact tendsto_div_mul_rpow_mul_log_of_tendsto_div_intervalIntegral hr₀ hA hUA hUint (hnon hnot)

/-- **Lemma I.5.6, two-error form.** Let `h` be measurable and regularly varying of index
`a > 0`, let `δ₁` be a logarithmically integrable error function and `δ₂ → 0`, and let `f` be
eventually positive and differentiable with `f' = ((1 - δ₁) a f + (1 - δ₂) h) / r` eventually.
Then there is `r₀ > 0` such that `h s / s ^ (a + 1)` is interval integrable on `[r₀, ∞)`, and

* if `h / r ^ a` is not logarithmically integrable, then
  `f r / (r ^ a ∫_{r₀}^r h s / s ^ (a + 1) ds) → 1`;
* if `h / r ^ a` is logarithmically integrable, then `f r / r ^ a → A` for some `A > 0`.

No measurability of `δ₂` is assumed. -/
theorem exists_tendsto_of_critical_two_error_ode {f f' h δ₁ δ₂ : ℝ → ℝ} {a : ℝ} (ha : 0 < a)
    (hhm : Measurable h) (hh : RegularlyVarying a h)
    (hfpos : ∀ᶠ x in atTop, 0 < f x)
    (hderiv : ∀ᶠ x in atTop, HasDerivAt f (f' x) x)
    (hδ₁ : IsLogErrorFunction δ₁) (hδ₂ : Tendsto δ₂ atTop (𝓝 0))
    (hode : ∀ᶠ x in atTop, f' x = ((1 - δ₁ x) * a * f x + (1 - δ₂ x) * h x) / x) :
    ∃ r₀ : ℝ, 0 < r₀ ∧
      (∀ x y : ℝ, r₀ ≤ x → x ≤ y →
        IntervalIntegrable (fun s => h s / s ^ (a + 1)) volume x y) ∧
      (¬ LogarithmicallyIntegrable (fun r => h r / r ^ a) →
        Tendsto (fun r => f r / (r ^ a * ∫ s in r₀..r, h s / s ^ (a + 1))) atTop (𝓝 1)) ∧
      (LogarithmicallyIntegrable (fun r => h r / r ^ a) →
        ∃ A : ℝ, 0 < A ∧ Tendsto (fun r => f r / r ^ a) atTop (𝓝 A)) := by
  obtain ⟨x₀, -, hpos, hbdd⟩ := hh.exists_threshold ha hhm
  -- a measurable forcing term `h₂`, equal to `(1 - δ₂) h` on a tail
  obtain ⟨B₁, hB₁⟩ := eventually_atTop.1 hderiv
  obtain ⟨f₀, hf₀m, hf₀eq, hf₀d⟩ := exists_measurable_eq_and_hasDerivAt_of_hasDerivAt_Ioi
    (c := max B₁ 0) fun x hx => hB₁ x ((le_max_left _ _).trans hx.le)
  obtain ⟨c₁, hc₁⟩ := hδ₁.1.1
  obtain ⟨D₁, hD₁m, hD₁eq⟩ := exists_measurable_eqOn_Ici hc₁
  set h₂ : ℝ → ℝ := fun x => x * deriv f₀ x - (1 - D₁ x) * a * f₀ x with hh₂_def
  have hh₂m : Measurable h₂ :=
    (measurable_id.mul (measurable_deriv f₀)).sub
      (((measurable_const.sub hD₁m).mul measurable_const).mul hf₀m)
  have hh₂eq : ∀ᶠ x in atTop, h₂ x = (1 - δ₂ x) * h x := by
    filter_upwards [eventually_gt_atTop (max B₁ 0), eventually_ge_atTop c₁, hode] with x hx hxc
      hox
    have hx0 : 0 < x := (le_max_right _ _).trans_lt hx
    simp only [h₂]
    rw [(hf₀d x hx).deriv, hf₀eq x hx, hD₁eq x hxc, hox]
    field_simp
    ring
  have hfac : Tendsto (fun r => 1 - δ₂ r) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hδ₂
  have hhalf : ∀ᶠ r in atTop, 1 / 2 ≤ 1 - δ₂ r ∧ 1 - δ₂ r ≤ 2 :=
    hfac.eventually (Icc_mem_nhds (by norm_num) (by norm_num))
  have hh₂rv : RegularlyVarying a h₂ := by
    refine hh.of_tendsto_div (hfac.congr' ?_) ⟨0, measurable_restrict_Ici_of_measurable hh₂m 0⟩
    filter_upwards [hh₂eq, hh.eventually_pos] with r hr hhr
    rw [hr, mul_div_cancel_right₀ _ hhr.ne']
  have hode₂ : ∀ᶠ x in atTop, f' x = (1 - δ₁ x) * a * f x / x + h₂ x / x := by
    filter_upwards [hode, hh₂eq] with x hox hx
    rw [hox, hx, add_div]
  obtain ⟨r₀, hrx₀, hr₀, hU₂int, hmain, hfinite⟩ :=
    exists_tendsto_of_critical_log_error_ode (R := x₀) ha hh₂m hh₂rv hfpos hderiv hδ₁ hode₂
  set U : ℝ → ℝ := fun s => h s / s ^ (a + 1) with hU_def
  set U₂ : ℝ → ℝ := fun s => h₂ s / s ^ (a + 1) with hU₂_def
  have hUpos : ∀ x, r₀ ≤ x → 0 < U x := fun x hx =>
    div_pos (hpos x (hrx₀.trans hx)) (Real.rpow_pos_of_pos (hr₀.trans_le hx) (a + 1))
  have hUint : ∀ x y : ℝ, r₀ ≤ x → x ≤ y → IntervalIntegrable U volume x y := by
    intro x y hx hxy
    obtain ⟨C, hC⟩ := hbdd y
    have hIc : IntegrableOn h (Icc x y) volume := by
      refine IntegrableOn.of_bound measure_Icc_lt_top hhm.aestronglyMeasurable C ?_
      filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
      rw [Real.norm_eq_abs, abs_of_pos (hpos s ((hrx₀.trans hx).trans hs.1))]
      exact hC s ((hrx₀.trans hx).trans hs.1) hs.2
    have hcont : ContinuousOn (fun s : ℝ => (s ^ (a + 1))⁻¹) (Icc x y) := by
      apply ContinuousOn.inv₀
      · intro s hs
        exact (Real.continuousAt_rpow_const s (a + 1)
          (Or.inl ((hr₀.trans_le (hx.trans hs.1)).ne'))).continuousWithinAt
      · intro s hs
        exact (Real.rpow_pos_of_pos ((hr₀.trans_le hx).trans_le hs.1) (a + 1)).ne'
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hxy]
    exact hIc.mul_continuousOn hcont isCompact_Icc
  have hum : ∃ b, Measurable ((Ici b).domRestrict fun r => h r / r ^ a) :=
    ⟨0, measurable_restrict_Ici_of_measurable (hhm.div (measurable_id.pow_const a)) 0⟩
  have hum₂ : ∃ b, Measurable ((Ici b).domRestrict fun r => h₂ r / r ^ a) :=
    ⟨0, measurable_restrict_Ici_of_measurable (hh₂m.div (measurable_id.pow_const a)) 0⟩
  have hforward : LogarithmicallyIntegrable (fun r => h r / r ^ a) →
      LogarithmicallyIntegrable (fun r => h₂ r / r ^ a) := fun hu =>
    (hu.const_mul 2).mono hum₂ (by
      filter_upwards [hh₂eq, hhalf] with r hr hr2
      rw [hr, mul_div_assoc, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
        abs_of_pos (by linarith [hr2.1] : (0 : ℝ) < 1 - δ₂ r)]
      exact mul_le_mul_of_nonneg_right hr2.2 (abs_nonneg _))
  have hback : LogarithmicallyIntegrable (fun r => h₂ r / r ^ a) →
      LogarithmicallyIntegrable (fun r => h r / r ^ a) := fun hu₂ =>
    (hu₂.const_mul 2).mono hum (by
      filter_upwards [hh₂eq, hhalf] with r hr hr2
      rw [hr, mul_div_assoc, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
        abs_of_pos (by linarith [hr2.1] : (0 : ℝ) < 1 - δ₂ r), ← mul_assoc]
      have h1 : 1 ≤ 2 * (1 - δ₂ r) := by linarith [hr2.1]
      calc |h r / r ^ a| = 1 * |h r / r ^ a| := (one_mul _).symm
        _ ≤ 2 * (1 - δ₂ r) * |h r / r ^ a| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _))
  refine ⟨r₀, hr₀, hUint, fun hnot => ?_, fun hu => hfinite (hforward hu)⟩
  change Tendsto (fun r => f r / (r ^ a * ∫ s in r₀..r, U s)) atTop (𝓝 1)
  have hm := hmain fun hu₂ => hnot (hback hu₂)
  change Tendsto (fun r => f r / (r ^ a * ∫ s in r₀..r, U₂ s)) atTop (𝓝 1) at hm
  have hnotU : ¬ IntegrableOn U (Ioi r₀) volume := by
    intro hUi
    refine hnot ⟨(hum), r₀, hr₀, ?_⟩
    refine hUi.congr_fun (fun s hs => ?_) measurableSet_Ioi
    have hs0 : 0 < s := hr₀.trans hs
    have hupos : 0 < h s / s ^ a :=
      div_pos (hpos s (hrx₀.trans hs.le)) (Real.rpow_pos_of_pos hs0 a)
    simp only [U]
    rw [abs_of_pos hupos, Real.rpow_add hs0, Real.rpow_one, div_div]
  have hUinf : Tendsto (fun r => ∫ s in r₀..r, U s) atTop atTop :=
    tendsto_intervalIntegral_atTop_of_not_integrableOn hUint (fun x hx => (hUpos x hx).le) hnotU
  have hUratio : Tendsto (fun s => U₂ s / U s) atTop (𝓝 1) := by
    refine hfac.congr' ?_
    filter_upwards [eventually_ge_atTop r₀, hh₂eq] with s hs hs₂
    have := (hUpos s hs).ne'
    simp only [U₂, U] at this ⊢
    rw [hs₂, mul_div_assoc, mul_div_cancel_right₀ _ this]
  have hIntRatio := tendsto_intervalIntegral_div_of_tendsto_ratio hUpos hUratio hU₂int hUint
    hUinf
  have hmul := hm.mul hIntRatio
  rw [mul_one] at hmul
  refine hmul.congr' ?_
  filter_upwards [hUinf.eventually (eventually_gt_atTop 0),
    hIntRatio.eventually (eventually_gt_nhds zero_lt_one)] with r hrI hrRatio
  have hrI₂ : 0 < ∫ s in r₀..r, U₂ s := (div_pos_iff_of_pos_right hrI).mp hrRatio
  have := hrI.ne'
  have := hrI₂.ne'
  field_simp

/-- **Logarithmic corollary of Lemma I.5.6, two-error form.** If moreover `h ∼ A r ^ a` with
`A > 0`, then `f ∼ A r ^ a log r`. -/
theorem tendsto_div_mul_rpow_mul_log_of_critical_two_error_ode {f f' h δ₁ δ₂ : ℝ → ℝ} {a A : ℝ}
    (ha : 0 < a) (hA : 0 < A) (hhm : Measurable h)
    (hfpos : ∀ᶠ x in atTop, 0 < f x)
    (hderiv : ∀ᶠ x in atTop, HasDerivAt f (f' x) x)
    (hδ₁ : IsLogErrorFunction δ₁) (hδ₂ : Tendsto δ₂ atTop (𝓝 0))
    (hode : ∀ᶠ x in atTop, f' x = ((1 - δ₁ x) * a * f x + (1 - δ₂ x) * h x) / x)
    (hhA : Tendsto (fun r => h r / (A * r ^ a)) atTop (𝓝 1)) :
    Tendsto (fun r => f r / (A * r ^ a * Real.log r)) atTop (𝓝 1) := by
  obtain ⟨hnot, hUA⟩ :=
    not_logarithmicallyIntegrable_and_tendsto_of_tendsto_div_const_mul_rpow hA hhA
  obtain ⟨r₀, hr₀, hUint, hnon, -⟩ := exists_tendsto_of_critical_two_error_ode ha hhm
    (regularlyVarying_of_tendsto_div_const_mul_rpow hA hhm hhA) hfpos hderiv hδ₁ hδ₂ hode
  exact tendsto_div_mul_rpow_mul_log_of_tendsto_div_intervalIntegral hr₀ hA hUA hUint (hnon hnot)

end PercLib.Analysis
