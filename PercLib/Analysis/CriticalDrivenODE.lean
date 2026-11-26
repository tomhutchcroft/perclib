/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
The critical case `a = b` and the assembled statement of Lemma I.5.5, the logarithmic integration
lemmas used with it, and the almost-everywhere normalized increment of the driven ODE, from
T. Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, §I.5.1.

Adapted from the repository `yujinhkim/lrp`, branch `critical-lrp-1`, commit
`d382e4c28d92dd4e698ebf4f2aaf0bc932ae73fc`, files
`PercLib/CriticalLRP/Analysis/Lemma_I_5_5.lean`, `PercLib/CriticalLRP/Analysis/CriticalLog.lean`
and `PercLib/CriticalLRP/Analysis/AENormalizedIncrement.lean`; licence Apache-2.0 as declared in
that commit's file headers and `third_party/critical-lrp/NOTICE.md`; upstream
`yujinhkim/Critical-Long-range-percolation` at `3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf`.
Modified: `RegularlyVaryingAtTop f ρ` becomes `RegularlyVarying ρ f` of
`PercLib/Analysis/RegularVariation/Defs.lean`; the structure `RVPosData` is unbundled, and a
threshold for the forcing term is obtained from `RegularlyVarying.exists_threshold`; the
definitions `errorTail` and `powerExpWeight` are written out; the critical case assumes only
eventual positivity of `f` and no positivity of `h`; the slowly varying window bounds are taken
from `RegularlyVarying.uniform_ratio`; the comparison of divergent integrals and the logarithmic
average are derived from `tendsto_div_of_ae_deriv_near` and `tendsto_div_log_of_mul_deriv`;
`LogarithmicallyIntegrable.congr_of_eventuallyEq` is replaced by
`LogarithmicallyIntegrable.mono`; the almost-everywhere increment is stated for a general
forcing term and a general bound on the error; declarations are renamed; `autoImplicit`,
disabled linters and `#print` lines are removed.
-/
module

public import PercLib.Analysis.DrivenODE
public import PercLib.Analysis.HardyMajorant
public import PercLib.Analysis.LinearODEAsymptotics

/-! # The critical driven ODE

Let `h` be measurable and regularly varying of index `a > 0`, and let `f` be differentiable on
`(0, ∞)` with `f' / ((a f + h) / r) → 1`. With the integrating weight
`w r = r ^ a * exp (-(a * ∫ s in r₀..r, (Ioi r₀).indicator δ s / s))` of
`PercLib/Analysis/DrivenODE.lean`, the function `v = h / w` is slowly varying and `q = f / w`
has the primitive `(1 - δ) v / r`. Uniform ratio bounds on fixed multiplicative windows show
`q / v → ∞` and that `q` is slowly varying, whether or not `∫ v / r` converges.

## Main results

* `ae_hasDerivAt_intervalIntegral_of_intervalIntegrable`: Lebesgue differentiation on a
  half-line.
* `tendsto_intervalIntegral_atTop_of_not_integrableOn`,
  `tendsto_intervalIntegral_div_of_tendsto_ratio`, `tendsto_intervalIntegral_div_mul_log`:
  divergent integrals and their comparison.
* `not_logarithmicallyIntegrable_of_tendsto_pos`, `logarithmicallyIntegrable_div_of_tendsto_pos`,
  `integrableOn_div_of_logarithmicallyIntegrable`: logarithmic integrability.
* `exists_pos_tendsto_rpow_mul_exp_neg_integral_div_rpow`: `w r / r ^ a` has a positive limit
  when the error is logarithmically integrable.
* `normalized_increment_of_ae_driving_ode`: the exact normalized increment for an absolutely
  continuous solution of `f' = (1 - δ) a f / r + k / r` almost everywhere;
  `normalized_increment_of_unweighted_driving_ode` is its everywhere-differentiable form.
* `regularlyVarying_zero_and_tendsto_of_primitive`: a critical primitive dominates its slowly
  varying driver and is slowly varying.
* `regularlyVarying_and_tendsto_of_tendsto_deriv_ratio_of_eq`: Lemma I.5.5 for `a = b`.
* `regularlyVarying_max_and_tendsto_of_tendsto_deriv_ratio`: Lemma I.5.5, all cases.
-/

@[expose] public section

open Filter Set MeasureTheory
open scoped Topology

namespace PercLib.Analysis

/-! ## Primitives on a half-line -/

/-- **Lebesgue differentiation on a half-line**: if `F` is interval integrable on every
interval of `[a, ∞)`, then for almost every `x ≥ a` the primitive `∫ t in a..u, F t` has
derivative `F x` at `x`. -/
theorem ae_hasDerivAt_intervalIntegral_of_intervalIntegrable {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {F : ℝ → E} {a : ℝ}
    (hF : ∀ x y : ℝ, a ≤ x → x ≤ y → IntervalIntegrable F volume x y) :
    ∀ᵐ x, a ≤ x → HasDerivAt (fun u => ∫ t in a..u, F t) (F x) x := by
  have h := ae_all_iff.2 fun n : ℕ =>
    (hF a (a + n) le_rfl (by linarith [n.cast_nonneg (α := ℝ)])).ae_hasDerivAt_integral
  filter_upwards [h] with x hx hax
  obtain ⟨n, hn⟩ := exists_nat_ge (x - a)
  have hmem : x ∈ uIcc a (a + n) := by
    rw [uIcc_of_le (by linarith [n.cast_nonneg (α := ℝ)])]
    exact ⟨hax, by linarith⟩
  exact hx n hmem a left_mem_uIcc

/-- A nonnegative function, interval integrable on `[a, ∞)` but not integrable on `(a, ∞)`,
has a primitive tending to `+∞`. -/
theorem tendsto_intervalIntegral_atTop_of_not_integrableOn {u : ℝ → ℝ} {a : ℝ}
    (huint : ∀ x y : ℝ, a ≤ x → x ≤ y → IntervalIntegrable u volume x y)
    (hunonneg : ∀ x, a ≤ x → 0 ≤ u x) (hnot : ¬ IntegrableOn u (Ioi a) volume) :
    Tendsto (fun r => ∫ s in a..r, u s) atTop atTop := by
  by_cases hunbounded : ∀ M : ℝ, ∃ b, a ≤ b ∧ M ≤ ∫ s in a..b, u s
  · refine tendsto_atTop.2 fun M => ?_
    obtain ⟨b, hab, hMb⟩ := hunbounded M
    filter_upwards [eventually_ge_atTop b] with r hbr
    have hInt : 0 ≤ ∫ s in b..r, u s :=
      intervalIntegral.integral_nonneg hbr fun s hs => hunonneg s (hab.trans hs.1)
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (huint a b le_rfl hab) (huint b r hab hbr)
    linarith
  · push Not at hunbounded
    obtain ⟨M, hM⟩ := hunbounded
    refine absurd (integrableOn_Ioi_of_intervalIntegral_norm_bounded M a (b := fun r : ℝ => r)
      (f := u) (fun b => ?_) tendsto_id ?_) hnot
    · by_cases hab : a ≤ b
      · exact (huint a b le_rfl hab).1
      · rw [Set.Ioc_eq_empty (not_lt_of_ge (lt_of_not_ge hab).le)]
        exact integrableOn_empty
    · filter_upwards [eventually_ge_atTop a] with b hab
      have hnorm : (∫ s in a..b, ‖u s‖) = ∫ s in a..b, u s := by
        refine intervalIntegral.integral_congr fun s hs => ?_
        rw [uIcc_of_le hab] at hs
        exact Real.norm_of_nonneg (hunonneg s hs.1)
      rw [hnorm]
      exact (hM b hab).le

/-- **Comparison of divergent integrals**: if `G > 0` on `[a, ∞)`, `∫ G → ∞` and `F / G → C`,
then `(∫ s in a..r, F s) / (∫ s in a..r, G s) → C`. -/
theorem tendsto_intervalIntegral_div_of_tendsto_ratio {F G : ℝ → ℝ} {a C : ℝ}
    (hGpos : ∀ x, a ≤ x → 0 < G x)
    (hFG : Tendsto (fun x => F x / G x) atTop (𝓝 C))
    (hFint : ∀ x y : ℝ, a ≤ x → x ≤ y → IntervalIntegrable F volume x y)
    (hGint : ∀ x y : ℝ, a ≤ x → x ≤ y → IntervalIntegrable G volume x y)
    (hGinf : Tendsto (fun r => ∫ s in a..r, G s) atTop atTop) :
    Tendsto (fun r => (∫ s in a..r, F s) / (∫ s in a..r, G s)) atTop (𝓝 C) := by
  refine tendsto_div_of_ae_deriv_near (r₀ := a)
    (fun R hR => (hFint a R le_rfl hR).absolutelyContinuousOnInterval_intervalIntegral
      left_mem_uIcc) hGint
    (fun x y hx hxy => (intervalIntegral.integral_interval_sub_left
      (hGint a y le_rfl (hx.trans hxy)) (hGint a x le_rfl hx)).symm) hGinf fun δ hδ => ?_
  obtain ⟨R₀, hR₀⟩ := Metric.tendsto_atTop.1 hFG δ hδ
  refine ⟨max a R₀, ?_⟩
  filter_upwards [ae_hasDerivAt_intervalIntegral_of_intervalIntegrable hFint] with s hs hsR
  have has : a ≤ s := (le_max_left _ _).trans hsR
  have hG := hGpos s has
  have hd := hR₀ s ((le_max_right _ _).trans hsR)
  rw [Real.dist_eq, abs_lt, lt_sub_iff_add_lt, sub_lt_iff_lt_add, lt_div_iff₀ hG,
    div_lt_iff₀ hG] at hd
  rw [(hs has).deriv]
  constructor <;> nlinarith

/-- **The logarithmic average**: if `U s / (A / s) → 1` with `A > 0`, then
`(∫ s in r₀..r, U s) / (A log r) → 1`. -/
theorem tendsto_intervalIntegral_div_mul_log {U : ℝ → ℝ} {A r₀ : ℝ}
    (hr₀ : 0 < r₀) (hA : 0 < A)
    (hUA : Tendsto (fun s => U s / (A / s)) atTop (𝓝 1))
    (hUint : ∀ x y : ℝ, r₀ ≤ x → x ≤ y → IntervalIntegrable U volume x y) :
    Tendsto (fun r => (∫ s in r₀..r, U s) / (A * Real.log r)) atTop (𝓝 1) := by
  have hrU : Tendsto (fun s => s * U s) atTop (𝓝 A) := by
    have h := hUA.const_mul A
    rw [mul_one] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
    field_simp
  have hlog := tendsto_div_log_of_mul_deriv hr₀
    (fun R hR => (hUint r₀ R le_rfl hR).absolutelyContinuousOnInterval_intervalIntegral
      left_mem_uIcc) fun δ hδ => by
    obtain ⟨R₀, hR₀⟩ := Metric.tendsto_atTop.1 hrU δ hδ
    refine ⟨max r₀ R₀, ?_⟩
    filter_upwards [ae_hasDerivAt_intervalIntegral_of_intervalIntegrable hUint] with s hs hsR
    rw [(hs ((le_max_left _ _).trans hsR)).deriv]
    exact (hR₀ s ((le_max_right _ _).trans hsR)).le
  have h := hlog.div_const A
  rw [div_self hA.ne'] at h
  refine h.congr' (Eventually.of_forall fun r => ?_)
  rw [div_div, mul_comm]

/-! ## Logarithmic integrability -/

/-- A function with a positive finite limit at infinity is not logarithmically integrable. -/
theorem not_logarithmicallyIntegrable_of_tendsto_pos {u : ℝ → ℝ} {A : ℝ}
    (hA : 0 < A) (hulim : Tendsto u atTop (𝓝 A)) :
    ¬ LogarithmicallyIntegrable u := by
  intro hulog
  obtain ⟨B, hB⟩ := Metric.tendsto_atTop.1 hulim (A / 2) (by positivity)
  obtain ⟨r₀, hr₀, hint⟩ := hulog.2
  set R : ℝ := max r₀ B with hR_def
  have hRr₀ : r₀ ≤ R := le_max_left _ _
  have hRB : B ≤ R := le_max_right _ _
  have hR0 : 0 < R := hr₀.trans_le hRr₀
  have hscaled : IntegrableOn (fun x : ℝ => (A / 2) * x⁻¹) (Ioi R) volume := by
    refine (hint.mono_set (Ioi_subset_Ioi hRr₀)).mono' (by fun_prop) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 < x := hR0.trans hx
    have hd := hB x (hRB.trans hx.le)
    rw [Real.dist_eq, abs_lt] at hd
    have habs : A / 2 < |u x| := (by linarith [hd.1] : A / 2 < u x).trans_le (le_abs_self _)
    rw [Real.norm_of_nonneg (by positivity), ← div_eq_mul_inv]
    exact div_le_div_of_nonneg_right habs.le hx0.le
  have hinv : IntegrableOn (fun x : ℝ => x⁻¹) (Ioi R) volume := by
    refine IntegrableOn.congr_fun (hscaled.const_mul (A / 2)⁻¹) (fun x _ => ?_) measurableSet_Ioi
    field_simp
  exact not_integrableOn_Ioi_inv hinv

/-- Division by a measurable function with a positive finite limit preserves logarithmic
integrability. -/
theorem logarithmicallyIntegrable_div_of_tendsto_pos {u E : ℝ → ℝ} {A : ℝ}
    (hA : 0 < A) (hlim : Tendsto E atTop (𝓝 A))
    (hu : LogarithmicallyIntegrable u) (hEm : Measurable E) :
    LogarithmicallyIntegrable (fun s => u s / E s) := by
  obtain ⟨a, ha⟩ := hu.1
  refine (hu.const_mul (2 / A)).mono ⟨a, ha.div (hEm.comp measurable_subtype_coe)⟩ ?_
  filter_upwards [hlim.eventually (lt_mem_nhds (by linarith : A / 2 < A))] with s hs
  have hEpos : 0 < E s := by linarith
  rw [abs_div, abs_of_pos hEpos, abs_mul, abs_of_pos (by positivity : 0 < 2 / A),
    div_le_iff₀ hEpos]
  have h1 : |u s| * (A / 2) ≤ |u s| * E s := mul_le_mul_of_nonneg_left hs.le (abs_nonneg _)
  calc |u s| = 2 / A * (|u s| * (A / 2)) := by field_simp
    _ ≤ 2 / A * (|u s| * E s) := mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = 2 / A * |u s| * E s := by ring

/-- On a tail where `v / s` is locally integrable, logarithmic integrability of `v` gives
integrability of `v / s` on `(r₀, ∞)`. -/
theorem integrableOn_div_of_logarithmicallyIntegrable {v : ℝ → ℝ} {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hvint : ∀ x y : ℝ, r₀ ≤ x → x ≤ y → IntervalIntegrable (fun s => v s / s) volume x y)
    (hvlog : LogarithmicallyIntegrable v) :
    IntegrableOn (fun s => v s / s) (Ioi r₀) volume := by
  obtain ⟨⟨c, hc⟩, r₂, -, hint⟩ := hvlog
  obtain ⟨V, hVm, hVeq⟩ := exists_measurable_eqOn_Ici hc
  set R : ℝ := max (max r₀ r₂) c with hR_def
  have hRr₀ : r₀ ≤ R := (le_max_left _ _).trans (le_max_left _ _)
  have hRr₂ : r₂ ≤ R := (le_max_right _ _).trans (le_max_left _ _)
  have hRc : c ≤ R := le_max_right _ _
  have hR0 : 0 < R := hr₀.trans_le hRr₀
  have htail : IntegrableOn (fun s => v s / s) (Ioi R) volume := by
    have hmeas : AEStronglyMeasurable (fun s => v s / s) (volume.restrict (Ioi R)) :=
      ((hVm.div measurable_id).aestronglyMeasurable).congr
        (ae_restrict_of_forall_mem measurableSet_Ioi fun s hs => by
          change V s / s = v s / s
          rw [hVeq s (hRc.trans hs.le)])
    refine (hint.mono_set (Ioi_subset_Ioi hRr₂)).mono' hmeas
      (ae_restrict_of_forall_mem measurableSet_Ioi fun s hs => ?_)
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (hR0.trans hs)]
  rw [← Ioc_union_Ioi_eq_Ioi hRr₀]
  exact (hvint r₀ R le_rfl hRr₀).1.union htail

/-- **The power-normalized integrating weight converges**: if the error `δ` is logarithmically
integrable, then `w r / r ^ a` has a positive limit. -/
theorem exists_pos_tendsto_rpow_mul_exp_neg_integral_div_rpow {δ : ℝ → ℝ} {r₀ a C : ℝ}
    (hr₀ : 0 < r₀) (hδm : Measurable δ) (hδ1 : ∀ x, r₀ ≤ x → |δ x| ≤ C)
    (hδlog : LogarithmicallyIntegrable δ) :
    ∃ A : ℝ, 0 < A ∧ Tendsto (fun r =>
      r ^ a * Real.exp (-(a * ∫ s in r₀..r, (Ioi r₀).indicator δ s / s)) / r ^ a) atTop (𝓝 A) := by
  obtain ⟨r₂, -, hint⟩ := hδlog.2
  set d : ℝ → ℝ := fun s => (Ioi r₀).indicator δ s / s with hd_def
  set R : ℝ := max r₀ r₂ with hR_def
  have hRr₀ : r₀ ≤ R := le_max_left _ _
  have hRr₂ : r₂ ≤ R := le_max_right _ _
  have hR0 : 0 < R := hr₀.trans_le hRr₀
  have hdm : Measurable d := (hδm.indicator measurableSet_Ioi).div measurable_id
  have htail : IntegrableOn d (Ioi R) volume := by
    refine (hint.mono_set (Ioi_subset_Ioi hRr₂)).mono' hdm.aestronglyMeasurable
      (ae_restrict_of_forall_mem measurableSet_Ioi fun s hs => ?_)
    have hs0 : 0 < s := hR0.trans hs
    simp only [d]
    rw [indicator_of_mem (mem_Ioi.2 (hRr₀.trans_lt hs)), Real.norm_eq_abs, abs_div,
      abs_of_pos hs0]
  have hintd : IntegrableOn d (Ioi r₀) volume := by
    rw [← Ioc_union_Ioi_eq_Ioi hRr₀]
    exact (intervalIntegrable_indicator_Ioi_div hr₀ hδm hδ1 r₀ R).1.union htail
  have hlim : Tendsto (fun r => Real.exp (-(a * ∫ s in r₀..r, d s))) atTop
      (𝓝 (Real.exp (-(a * ∫ s in Ioi r₀, d s)))) :=
    (Real.continuous_exp.tendsto _).comp
      (((intervalIntegral_tendsto_integral_Ioi r₀ hintd tendsto_id).const_mul a).neg)
  refine ⟨_, Real.exp_pos _, hlim.congr' ?_⟩
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  exact (mul_div_cancel_left₀ _ (Real.rpow_pos_of_pos hr a).ne').symm

/-! ## The normalized increment -/

/-- **The exact normalized increment, almost-everywhere form.** Let `w` be the integrating weight.
If `f` is absolutely continuous on `[r₀, R]` and almost everywhere on `(r₀, R]` it has a
derivative `f' = (1 - δ) a f / r + k / r`, with `δ` measurable and bounded on `[r₀, ∞)`, then
`f R / w R - f r₀ / w r₀ = ∫ s in r₀..R, k s / (s w s)`. -/
theorem normalized_increment_of_ae_driving_ode {f f' k δ : ℝ → ℝ} {a r₀ R C : ℝ}
    (hr₀ : 0 < r₀) (hR : r₀ ≤ R)
    (hfAC : AbsolutelyContinuousOnInterval f r₀ R)
    (hderiv : ∀ᵐ x, x ∈ Ioc r₀ R → HasDerivAt f (f' x) x)
    (hδm : Measurable δ) (hδ1 : ∀ x, r₀ ≤ x → |δ x| ≤ C)
    (hode : ∀ᵐ x, x ∈ Ioc r₀ R → f' x = (1 - δ x) * a * f x / x + k x / x) :
    f R * (R ^ a * Real.exp (-(a * ∫ s in r₀..R, (Ioi r₀).indicator δ s / s)))⁻¹ -
        f r₀ * (r₀ ^ a * Real.exp (-(a * ∫ s in r₀..r₀, (Ioi r₀).indicator δ s / s)))⁻¹ =
      ∫ s in r₀..R,
        k s / (s * (s ^ a * Real.exp (-(a * ∫ t in r₀..s, (Ioi r₀).indicator δ t / t)))) := by
  set w : ℝ → ℝ := fun r => r ^ a * Real.exp (-(a * ∫ s in r₀..r, (Ioi r₀).indicator δ s / s))
    with hw_def
  set q : ℝ → ℝ := fun r => f r * (w r)⁻¹ with hq_def
  have hwpos : ∀ x, 0 < x → 0 < w x := fun x hx => rpow_mul_exp_neg_integral_pos hx
  have hHac : AbsolutelyContinuousOnInterval
      (fun r => ∫ s in r₀..r, (Ioi r₀).indicator δ s / s) r₀ R :=
    (intervalIntegrable_indicator_Ioi_div hr₀ hδm hδ1 r₀
        R).absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc
  have h0 : ∀ x ∈ uIcc r₀ R, x ≠ 0 := by
    intro x hx
    rw [uIcc_of_le hR] at hx
    exact (lt_of_lt_of_le hr₀ hx.1).ne'
  have hwAC : AbsolutelyContinuousOnInterval w r₀ R :=
    (absolutelyContinuousOnInterval_rpow a h0).mul
      (AbsolutelyContinuousOnInterval.exp (hHac.const_mul a).neg)
  have hwiAC : AbsolutelyContinuousOnInterval (fun x => (w x)⁻¹) r₀ R :=
    absolutelyContinuousOnInterval_inv hR hwAC fun x hx => hwpos x (lt_of_lt_of_le hr₀ hx.1)
  have hqAC : AbsolutelyContinuousOnInterval q r₀ R := hfAC.mul hwiAC
  have hqderiv : ∀ᵐ x, x ∈ Ioc r₀ R → deriv q x = k x / (x * w x) := by
    filter_upwards [ae_hasDerivAt_rpow_mul_exp_neg_integral (a := a) hr₀ hR hδm hδ1, hderiv,
      hode] with x hx hfx hox hxmem
    have hxpos : 0 < x := lt_of_lt_of_le hr₀ hxmem.1.le
    have hwx := hwpos x hxpos
    have hq : HasDerivAt q (f' x * (w x)⁻¹ +
        f x * (-(a * (1 - δ x) * w x / x) / (w x) ^ 2)) x :=
      (hfx hxmem).mul ((hx hxmem).inv hwx.ne')
    rw [hq.deriv, hox hxmem]
    field_simp
    ring
  calc _ = q R - q r₀ := rfl
    _ = ∫ s in r₀..R, deriv q s := hqAC.integral_deriv_eq_sub.symm
    _ = _ := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [hqderiv] with x hx hxmem
        exact hx (by rwa [uIoc_of_le hR] at hxmem)

/-- **The exact normalized increment with unweighted forcing.** If
`f' = (1 - δ) a f / r + h / r` at every point of `[r₀, R]`, with `δ` measurable and bounded on
`[r₀, ∞)` and `x₀ ≤ r₀` a threshold above which `h` is positive and locally bounded, then
`f R / w R - f r₀ / w r₀ = ∫ s in r₀..R, h s / (s w s)`. -/
theorem normalized_increment_of_unweighted_driving_ode {f f' h δ : ℝ → ℝ} {a x₀ r₀ R C : ℝ}
    (hr₀ : 0 < r₀) (hR : r₀ ≤ R)
    (hpos : ∀ x, x₀ ≤ x → 0 < h x) (hbdd : ∀ M, ∃ C, ∀ x, x₀ ≤ x → x ≤ M → h x ≤ C)
    (hrD : x₀ ≤ r₀)
    (hderiv : ∀ x, r₀ ≤ x → HasDerivAt f (f' x) x)
    (hδm : Measurable δ) (hδ1 : ∀ x, r₀ ≤ x → |δ x| ≤ C)
    (hode : ∀ x, r₀ ≤ x → f' x = (1 - δ x) * a * f x / x + h x / x) :
    f R * (R ^ a * Real.exp (-(a * ∫ s in r₀..R, (Ioi r₀).indicator δ s / s)))⁻¹ -
        f r₀ * (r₀ ^ a * Real.exp (-(a * ∫ s in r₀..r₀, (Ioi r₀).indicator δ s / s)))⁻¹ =
      ∫ s in r₀..R,
        h s / (s * (s ^ a * Real.exp (-(a * ∫ t in r₀..s, (Ioi r₀).indicator δ t / t)))) := by
  have hfc : ContinuousOn f (Icc r₀ R) := fun x hx =>
    (hderiv x hx.1).continuousAt.continuousWithinAt
  obtain ⟨Cf, hCf⟩ := isCompact_Icc.exists_bound_of_continuousOn hfc
  obtain ⟨Ch, hCh⟩ := hbdd R
  have hM : 0 ≤ (1 + C) * (|a| * Cf) + Ch := by
    have hC : 0 ≤ C := (abs_nonneg _).trans (hδ1 r₀ le_rfl)
    have hCf0 : 0 ≤ Cf := (norm_nonneg _).trans (hCf r₀ ⟨le_rfl, hR⟩)
    have hCh0 : 0 ≤ Ch := (hpos r₀ hrD).le.trans (hCh r₀ hrD hR)
    positivity
  have hf'bound : ∀ x ∈ uIcc r₀ R, ‖f' x‖ ≤ ((1 + C) * (|a| * Cf) + Ch) / r₀ := by
    intro x hx
    rw [uIcc_of_le hR] at hx
    have hx0 : 0 < x := lt_of_lt_of_le hr₀ hx.1
    have hfx : |f x| ≤ Cf := hCf x hx
    have hhx : |h x| ≤ Ch := by
      rw [abs_of_pos (hpos x (le_trans hrD hx.1))]
      exact hCh x (le_trans hrD hx.1) hx.2
    have hfac : |1 - δ x| ≤ 1 + C := by
      calc |1 - δ x| ≤ |1| + |δ x| := abs_sub _ _
        _ ≤ 1 + C := by rw [abs_one]; linarith [hδ1 x hx.1]
    have hsum : |(1 - δ x) * a * f x + h x| ≤ (1 + C) * (|a| * Cf) + Ch := by
      calc |(1 - δ x) * a * f x + h x| ≤ |1 - δ x| * (|a| * |f x|) + |h x| := by
            rw [mul_assoc, ← abs_mul, ← abs_mul]
            exact abs_add_le _ _
        _ ≤ (1 + C) * (|a| * Cf) + Ch := by
            gcongr
            exact (abs_nonneg _).trans hfac
    rw [hode x hx.1, ← add_div, Real.norm_eq_abs, abs_div, abs_of_pos hx0]
    calc |(1 - δ x) * a * f x + h x| / x ≤ ((1 + C) * (|a| * Cf) + Ch) / x :=
          div_le_div_of_nonneg_right hsum hx0.le
      _ ≤ ((1 + C) * (|a| * Cf) + Ch) / r₀ := div_le_div_of_nonneg_left hM hr₀ hx.1
  have hfAC : AbsolutelyContinuousOnInterval f r₀ R :=
    absolutelyContinuousOnInterval_of_hasDerivAt_of_norm_le
      (fun x hx => hderiv x (by rw [uIcc_of_le hR] at hx; exact hx.1)) hf'bound
  exact normalized_increment_of_ae_driving_ode hr₀ hR hfAC
    (ae_of_all _ fun x hx => hderiv x hx.1.le) hδm hδ1
    (ae_of_all _ fun x hx => hode x hx.1.le)

/-! ## The critical primitive -/

/-- **The fixed-window lower bound for a critical primitive.** Let `v > 0` on `[r₀, ∞)` be
measurable and slowly varying, `δ → 0` with `|δ| ≤ 1` on `[r₀, ∞)`, and let `q` have the
primitive `F = (1 - δ) v / r` on `[r₀, ∞)` with `q r₀ > 0`. Then for every `K > 1`,
`(log K / 4) v r ≤ q r` eventually. -/
theorem eventually_log_div_four_mul_le_of_primitive {v q F δ : ℝ → ℝ} {r₀ K : ℝ}
    (hr₀ : 0 < r₀) (hK : 1 < K) (hvm : Measurable v)
    (hvrv : RegularlyVarying 0 v) (hvpos : ∀ x, r₀ ≤ x → 0 < v x)
    (hδ0 : Tendsto δ atTop (𝓝 0))
    (hδ1 : ∀ x, r₀ ≤ x → |δ x| ≤ 1)
    (hF : ∀ x, r₀ ≤ x → F x = (1 - δ x) * (v x / x))
    (hFint : ∀ x y : ℝ, r₀ ≤ x → r₀ ≤ y → IntervalIntegrable F volume x y)
    (hq₀ : 0 < q r₀)
    (hqinc : ∀ R, r₀ ≤ R → q R - q r₀ = ∫ s in r₀..R, F s) :
    ∀ᶠ r in atTop, (Real.log K / 4) * v r ≤ q r := by
  have hK0 : 0 < K := zero_lt_one.trans hK
  obtain ⟨B, hB⟩ := Metric.tendsto_atTop.1 hδ0 (1 / 2) (by norm_num)
  obtain ⟨Y, hYr₀, hY⟩ := hvrv.uniform_ratio hvm hvpos (inv_pos.2 hK0)
    ((inv_le_one_of_one_le₀ hK.le).trans hK.le) (by norm_num : (0 : ℝ) < 1 / 2)
  filter_upwards [eventually_ge_atTop (K * max Y B)] with r hrB
  have hMr : max Y B ≤ r / K := (le_div_iff₀ hK0).2 (by simpa [mul_comm] using hrB)
  have har₀ : r₀ ≤ r / K := hYr₀.trans ((le_max_left _ _).trans hMr)
  have haB : B ≤ r / K := (le_max_right _ _).trans hMr
  have ha0 : 0 < r / K := hr₀.trans_le har₀
  have hr0 : 0 < r := by
    have := mul_pos ha0 hK0
    rwa [div_mul_cancel₀ r hK0.ne'] at this
  have hKr : r / K ≤ r := div_le_self hr0.le hK.le
  have hrY : Y ≤ r := ((le_max_left _ _).trans hMr).trans hKr
  have hrr₀ : r₀ ≤ r := har₀.trans hKr
  have hvr := hvpos r hrr₀
  have hra : r / (r / K) = K := by field_simp
  have hFnn : ∀ s, r₀ ≤ s → 0 ≤ F s := by
    intro s hs
    rw [hF s hs]
    have hd : 0 ≤ 1 - δ s := by linarith [(abs_le.1 (hδ1 s hs)).2]
    exact mul_nonneg hd (div_nonneg (hvpos s hs).le (hr₀.trans_le hs).le)
  have hnonneg : 0 ≤ ∫ s in r₀..(r / K), F s :=
    intervalIntegral.integral_nonneg har₀ fun s hs => hFnn s hs.1
  have hpoint : ∀ s ∈ Icc (r / K) r, (v r / 4) / s ≤ F s := by
    intro s hs
    have hsr₀ : r₀ ≤ s := har₀.trans hs.1
    have hs0 : 0 < s := hr₀.trans_le hsr₀
    have hd : (1 : ℝ) / 2 ≤ 1 - δ s := by
      have hdist := hB s (haB.trans hs.1)
      rw [Real.dist_eq, sub_zero, abs_lt] at hdist
      linarith [hdist.2]
    have hl : s / r ∈ Icc K⁻¹ K := by
      constructor
      · rw [le_div_iff₀ hr0, ← div_eq_inv_mul]
        exact hs.1
      · rw [div_le_iff₀ hr0]
        nlinarith [hs.2]
    have hvs := (hY r hrY (s / r) hl).2
    rw [div_mul_cancel₀ s hr0.ne', Real.rpow_zero, abs_of_pos hvr,
      abs_of_pos (hvpos s hsr₀)] at hvs
    rw [hF s hsr₀, mul_div_assoc', div_le_div_iff_of_pos_right hs0]
    nlinarith [hvpos s hsr₀]
  have hconstint : IntervalIntegrable (fun s => (v r / 4) / s) volume (r / K) r := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hKr]
    intro s hs
    exact (continuousAt_const.div continuousAt_id
      (ha0.trans_le hs.1).ne').continuousWithinAt
  have hmono := intervalIntegral.integral_mono_on hKr hconstint
    (hFint (r / K) r har₀ hrr₀) hpoint
  have hconstval : (∫ s in (r / K)..r, (v r / 4) / s) = (v r / 4) * Real.log K := by
    rw [show (fun s => (v r / 4) / s) = (fun s => (v r / 4) * (1 / s)) by
      funext s; rw [mul_one_div], intervalIntegral.integral_const_mul,
      integral_one_div_of_pos ha0 hr0, hra]
  rw [hconstval] at hmono
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (hFint r₀ (r / K) le_rfl har₀) (hFint (r / K) r har₀ hrr₀)
  have hq := hqinc r hrr₀
  nlinarith

/-- **A critical primitive grows faster than its slowly varying driver**: under the hypotheses
of `eventually_log_div_four_mul_le_of_primitive`, `q / v → ∞`. -/
theorem tendsto_div_atTop_of_primitive {v q F δ : ℝ → ℝ} {r₀ : ℝ}
    (hr₀ : 0 < r₀) (hvm : Measurable v)
    (hvrv : RegularlyVarying 0 v) (hvpos : ∀ x, r₀ ≤ x → 0 < v x)
    (hδ0 : Tendsto δ atTop (𝓝 0))
    (hδ1 : ∀ x, r₀ ≤ x → |δ x| ≤ 1)
    (hF : ∀ x, r₀ ≤ x → F x = (1 - δ x) * (v x / x))
    (hFint : ∀ x y : ℝ, r₀ ≤ x → r₀ ≤ y → IntervalIntegrable F volume x y)
    (hq₀ : 0 < q r₀)
    (hqinc : ∀ R, r₀ ≤ R → q R - q r₀ = ∫ s in r₀..R, F s) :
    Tendsto (fun r => q r / v r) atTop atTop := by
  refine tendsto_atTop.2 fun M => ?_
  set K : ℝ := Real.exp (4 * (|M| + 1)) with hK_def
  have hK : 1 < K := Real.one_lt_exp_iff.2 (by positivity)
  have hlog : Real.log K / 4 = |M| + 1 := by
    rw [hK_def, Real.log_exp]
    ring
  filter_upwards [eventually_log_div_four_mul_le_of_primitive hr₀ hK hvm hvrv hvpos hδ0 hδ1
    hF hFint hq₀ hqinc, eventually_ge_atTop r₀] with r hr hrr₀
  rw [hlog] at hr
  have hratio : |M| + 1 ≤ q r / v r := (le_div_iff₀ (hvpos r hrr₀)).2 hr
  linarith [le_abs_self M]

/-- **Critical primitives are slowly varying and dominate their drivers**: under the hypotheses
of `eventually_log_div_four_mul_le_of_primitive`, `q / v → ∞`, `v / q → 0` and `q` is slowly
varying. -/
theorem regularlyVarying_zero_and_tendsto_of_primitive {v q F δ : ℝ → ℝ} {r₀ : ℝ}
    (hr₀ : 0 < r₀) (hvm : Measurable v)
    (hvrv : RegularlyVarying 0 v) (hvpos : ∀ x, r₀ ≤ x → 0 < v x)
    (hδ0 : Tendsto δ atTop (𝓝 0))
    (hδ1 : ∀ x, r₀ ≤ x → |δ x| ≤ 1)
    (hF : ∀ x, r₀ ≤ x → F x = (1 - δ x) * (v x / x))
    (hFint : ∀ x y : ℝ, r₀ ≤ x → r₀ ≤ y → IntervalIntegrable F volume x y)
    (hq₀ : 0 < q r₀)
    (hqinc : ∀ R, r₀ ≤ R → q R - q r₀ = ∫ s in r₀..R, F s) :
    Tendsto (fun r => q r / v r) atTop atTop ∧
      Tendsto (fun r => v r / q r) atTop (𝓝 0) ∧ RegularlyVarying 0 q := by
  have hqv : Tendsto (fun r => q r / v r) atTop atTop :=
    tendsto_div_atTop_of_primitive hr₀ hvm hvrv hvpos hδ0 hδ1 hF hFint hq₀ hqinc
  have hqinc' : ∀ x y : ℝ, r₀ ≤ x → r₀ ≤ y → q y - q x = ∫ s in x..y, F s := by
    intro x y hx hy
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (hFint r₀ x le_rfl hx) (hFint x y hx hy)
    linarith [hqinc x hx, hqinc y hy]
  have hFnn : ∀ s, r₀ ≤ s → 0 ≤ F s := by
    intro s hs
    rw [hF s hs]
    have hd : 0 ≤ 1 - δ s := by linarith [(abs_le.1 (hδ1 s hs)).2]
    exact mul_nonneg hd (div_nonneg (hvpos s hs).le (hr₀.trans_le hs).le)
  have hqpos : ∀ x, r₀ ≤ x → 0 < q x := by
    intro x hx
    have hInt : 0 ≤ ∫ s in r₀..x, F s :=
      intervalIntegral.integral_nonneg hx fun s hs => hFnn s hs.1
    linarith [hqinc x hx]
  have hvq : Tendsto (fun r => v r / q r) atTop (𝓝 0) := by
    refine hqv.inv_tendsto_atTop.congr' ?_
    filter_upwards with r
    exact inv_div _ _
  -- `q` is continuous on `[r₀, ∞)`, hence measurable there
  have hqcont : ContinuousOn q (Ici r₀) := by
    have hG : Continuous fun x => ∫ t in r₀..x, (Ioi r₀).indicator F t :=
      intervalIntegral.continuous_primitive (intervalIntegrable_indicator_Ioi_of_intervalIntegrable
        fun x y hx hxy => (hFint x y hx (hx.trans hxy)).1) r₀
    refine ((continuousOn_const (c := q r₀)).add hG.continuousOn).congr fun x hx => ?_
    change q x = q r₀ + ∫ t in r₀..x, (Ioi r₀).indicator F t
    have hx' : r₀ ≤ x := hx
    rw [intervalIntegral.integral_congr_ae (g := F) (ae_of_all _ fun t ht => by
      rw [uIoc_of_le hx'] at ht
      exact indicator_of_mem (mem_Ioi.2 ht.1) F), ← hqinc x hx']
    ring
  refine ⟨hqv, hvq, ⟨r₀, hqcont.domRestrict.measurable⟩,
    (eventually_ge_atTop r₀).mono fun r hr => hqpos r hr, ?_⟩
  have hbase : ∀ l : ℝ, 1 < l → Tendsto (fun r => q (l * r) / q r) atTop (𝓝 1) := by
    intro l hll
    have hl0 : 0 < l := zero_lt_one.trans hll
    obtain ⟨Y, hYr₀, hY⟩ := hvrv.uniform_ratio hvm hvpos (inv_pos.2 hl0)
      ((inv_le_one_of_one_le₀ hll.le).trans hll.le) (by norm_num : (0 : ℝ) < 1 / 2)
    have hnonneg : ∀ᶠ r in atTop, 0 ≤ (q (l * r) - q r) / q r := by
      filter_upwards [eventually_ge_atTop r₀] with r hr
      have hr0 : 0 < r := hr₀.trans_le hr
      have hlr : r ≤ l * r := by nlinarith
      rw [hqinc' r (l * r) hr (hr.trans hlr)]
      exact div_nonneg (intervalIntegral.integral_nonneg hlr fun s hs => hFnn s (hr.trans hs.1))
        (hqpos r hr).le
    have hupper : ∀ᶠ r in atTop,
        (q (l * r) - q r) / q r ≤ (4 * Real.log l) * (v r / q r) := by
      filter_upwards [eventually_ge_atTop Y] with r hrY
      have hr : r₀ ≤ r := hYr₀.trans hrY
      have hr0 : 0 < r := hr₀.trans_le hr
      have hlr0 : 0 < l * r := mul_pos hl0 hr0
      have hlr : r ≤ l * r := by nlinarith
      have hvr := hvpos r hr
      have hpoint : ∀ s ∈ Icc r (l * r), F s ≤ (4 * v r) / s := by
        intro s hs
        have hsr₀ : r₀ ≤ s := hr.trans hs.1
        have hs0 : 0 < s := hr₀.trans_le hsr₀
        have hd : 1 - δ s ≤ 2 := by linarith [(abs_le.1 (hδ1 s hsr₀)).1]
        have hd0 : 0 ≤ 1 - δ s := by linarith [(abs_le.1 (hδ1 s hsr₀)).2]
        have hl : s / r ∈ Icc l⁻¹ l := by
          constructor
          · rw [le_div_iff₀ hr0]
            nlinarith [inv_le_one_of_one_le₀ hll.le, hs.1]
          · rw [div_le_iff₀ hr0]
            exact hs.2
        have hvs := (hY r hrY (s / r) hl).1
        rw [div_mul_cancel₀ s hr0.ne', Real.rpow_zero, abs_of_pos hvr,
          abs_of_pos (hvpos s hsr₀)] at hvs
        rw [hF s hsr₀, mul_div_assoc', div_le_div_iff_of_pos_right hs0]
        nlinarith [hvpos s hsr₀]
      have hconstint : IntervalIntegrable (fun s => (4 * v r) / s) volume r (l * r) := by
        apply ContinuousOn.intervalIntegrable
        rw [uIcc_of_le hlr]
        intro s hs
        exact (continuousAt_const.div continuousAt_id
          (hr0.trans_le hs.1).ne').continuousWithinAt
      have hmono := intervalIntegral.integral_mono_on hlr (hFint r (l * r) hr (hr.trans hlr))
        hconstint hpoint
      have hconstval : (∫ s in r..(l * r), (4 * v r) / s) = (4 * v r) * Real.log l := by
        rw [show (fun s => (4 * v r) / s) = (fun s => (4 * v r) * (1 / s)) by
          funext s; rw [mul_one_div], intervalIntegral.integral_const_mul,
          integral_one_div_of_pos hr0 hlr0, mul_div_cancel_right₀ l hr0.ne']
      rw [hconstval, ← hqinc' r (l * r) hr (hr.trans hlr)] at hmono
      have hqr := hqpos r hr
      rw [div_le_iff₀ hqr]
      calc q (l * r) - q r ≤ (4 * v r) * Real.log l := hmono
        _ = (4 * Real.log l) * (v r / q r) * q r := by field_simp
    have hzero : Tendsto (fun r => (4 * Real.log l) * (v r / q r)) atTop (𝓝 0) := by
      simpa using hvq.const_mul (4 * Real.log l)
    have hdiff := squeeze_zero' hnonneg hupper hzero
    have hone : Tendsto (fun r => 1 + (q (l * r) - q r) / q r) atTop (𝓝 1) := by
      simpa using hdiff.const_add 1
    refine hone.congr' ?_
    filter_upwards [eventually_ge_atTop r₀] with r hr
    have hqr := (hqpos r hr).ne'
    field_simp
    ring
  intro l hl
  rw [Real.rpow_zero]
  rcases lt_trichotomy l 1 with hl1 | rfl | hl1
  · have h := hbase l⁻¹ (one_lt_inv₀ hl |>.2 hl1)
    have hcomp : Tendsto (fun x : ℝ => q (l⁻¹ * (l * x)) / q (l * x)) atTop (𝓝 1) :=
      h.comp ((tendsto_const_mul_atTop_of_pos hl).2 tendsto_id)
    have hinv := hcomp.inv₀ one_ne_zero
    rw [inv_one] at hinv
    refine hinv.congr' (Eventually.of_forall fun x => ?_)
    simp only [inv_mul_cancel_left₀ hl.ne', inv_div]
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop r₀] with r hr
    rw [one_mul, div_self (hqpos r hr).ne']
  · exact hbase l hl1

/-! ## Lemma I.5.5 -/

/-- **Lemma I.5.5 in the critical case `a = b`.** Let `h` be measurable and regularly varying of
index `a > 0`, and let `f` be eventually positive and differentiable on `(0, ∞)` with
`f' / ((a f + h) / r) → 1`. Then `f` is regularly varying of index `a`, `h / f → 0` and
`f' / (a f / r) → 1`. -/
theorem regularlyVarying_and_tendsto_of_tendsto_deriv_ratio_of_eq {f f' h : ℝ → ℝ} {a : ℝ}
    (hhm : Measurable h) (hh : RegularlyVarying a h) (ha : 0 < a)
    (hfpos : ∀ᶠ x in atTop, 0 < f x)
    (hderiv : ∀ x, 0 < x → HasDerivAt f (f' x) x)
    (hasym : Tendsto (fun r => f' r / ((a * f r + h r) / r)) atTop (𝓝 1)) :
    RegularlyVarying a f ∧ Tendsto (fun r => h r / f r) atTop (𝓝 0) ∧
      Tendsto (fun r => f' r / (a * f r / r)) atTop (𝓝 1) := by
  obtain ⟨x₀, -, hpos, hbdd⟩ := hh.exists_threshold ha hhm
  obtain ⟨X, hX⟩ := eventually_atTop.1 hfpos
  obtain ⟨r₀, δ, hr₀, -, hrD, hδm, hδ0, hδ1, hode⟩ :=
    exists_shared_error_of_tendsto (max x₀ X) hhm hderiv hasym
  have hrx₀ : x₀ ≤ r₀ := (le_max_left _ _).trans hrD
  have hrX : X ≤ r₀ := (le_max_right _ _).trans hrD
  set w : ℝ → ℝ := fun r => r ^ a * Real.exp (-(a * ∫ s in r₀..r, (Ioi r₀).indicator δ s / s))
    with hw_def
  set v : ℝ → ℝ := fun s => h s / w s with hv_def
  set F : ℝ → ℝ := fun s => (1 - δ s) * (v s / s) with hF_def
  set q : ℝ → ℝ := fun r => f r * (w r)⁻¹ with hq_def
  have hwrv : RegularlyVarying a w := regularlyVarying_rpow_mul_exp_neg_integral ha hr₀ hδm hδ0 hδ1
  have hwm : Measurable w := measurable_rpow_mul_exp_neg_integral a hr₀ hδm hδ1
  have hwpos : ∀ s, 0 < s → 0 < w s := fun s hs => rpow_mul_exp_neg_integral_pos hs
  have hvrv : RegularlyVarying 0 v := by
    have h1 := hh.mul hwrv.inv
    rw [add_neg_cancel] at h1
    simpa [v, div_eq_mul_inv] using h1
  have hvm : Measurable v := hhm.div hwm
  have hvpos : ∀ x, r₀ ≤ x → 0 < v x := fun x hx =>
    div_pos (hpos x (hrx₀.trans hx)) (hwpos x (hr₀.trans_le hx))
  have hwcont : ContinuousOn w (Ici r₀) := by
    intro s hs
    have hs0 : 0 < s := lt_of_lt_of_le hr₀ hs
    exact ((Real.continuousAt_rpow_const s a (Or.inl hs0.ne')).mul
      (Real.continuous_exp.continuousAt.comp
        (((continuous_intervalIntegral_indicator_Ioi_div hr₀ hδm hδ1).continuousAt.const_mul
          a).neg))).continuousWithinAt
  have hFint_of_le : ∀ x y : ℝ, r₀ ≤ x → x ≤ y → IntervalIntegrable F volume x y := by
    intro x y hx hxy
    obtain ⟨C, hC⟩ := hbdd y
    have hIc : IntegrableOn h (Icc x y) volume := by
      refine IntegrableOn.of_bound measure_Icc_lt_top hhm.aestronglyMeasurable C ?_
      filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
      rw [Real.norm_eq_abs, abs_of_pos (hpos s ((le_trans hrx₀ hx).trans hs.1))]
      exact hC s ((le_trans hrx₀ hx).trans hs.1) hs.2
    have hcont : ContinuousOn (fun s => (s * w s)⁻¹) (Icc x y) := by
      apply (continuousOn_id.mul (hwcont.mono (fun s hs => le_trans hx hs.1))).inv₀
      intro s hs
      have hs0 : 0 < s := (lt_of_lt_of_le hr₀ hx).trans_le hs.1
      exact (mul_pos hs0 (hwpos s hs0)).ne'
    have hg : IntegrableOn (fun s => v s / s) (Icc x y) volume := by
      refine (hIc.mul_continuousOn hcont isCompact_Icc).congr_fun (fun s _ => ?_)
        measurableSet_Icc
      simp only [v, div_eq_mul_inv, mul_inv]
      ring
    have hbd : ∀ᵐ s ∂(volume.restrict (Icc x y)), ‖1 - δ s‖ ≤ 2 := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
      have hd := hδ1 s (hx.trans hs.1)
      calc ‖1 - δ s‖ = |1 - δ s| := Real.norm_eq_abs _
        _ ≤ |1| + |δ s| := abs_sub _ _
        _ ≤ 2 := by rw [abs_one]; linarith
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hxy]
    exact hg.bdd_mul (measurable_const.sub hδm).aestronglyMeasurable hbd
  have hFint : ∀ x y : ℝ, r₀ ≤ x → r₀ ≤ y → IntervalIntegrable F volume x y := by
    intro x y hx hy
    rcases le_total x y with hxy | hyx
    · exact hFint_of_le x y hx hxy
    · exact (hFint_of_le y x hy hyx).symm
  have hqinc : ∀ R, r₀ ≤ R → q R - q r₀ = ∫ s in r₀..R, F s := by
    intro R hR
    have h1 := normalized_increment_of_driving_ode ha hr₀ hR hpos hbdd hrx₀
      (fun x hx => hderiv x (lt_of_lt_of_le hr₀ hx)) hδm hδ1 hode
    simp only [q, w, F, v]
    rw [h1]
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [div_eq_mul_inv, mul_inv]
    ring
  have hq₀ : 0 < q r₀ := mul_pos (hX r₀ hrX) (inv_pos.2 (hwpos r₀ hr₀))
  obtain ⟨-, hvq, hqrv⟩ := regularlyVarying_zero_and_tendsto_of_primitive hr₀ hvm hvrv hvpos
    hδ0 hδ1 (fun x _ => rfl) hFint hq₀ hqinc
  have hfrv : RegularlyVarying a f := by
    refine (by simpa using hwrv.mul hqrv : RegularlyVarying a (fun r => w r * q r)).congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    have := hwpos r hr
    simp only [q]
    field_simp
  have hf0 : Tendsto (fun r => h r / f r) atTop (𝓝 0) := by
    refine hvq.congr' ?_
    filter_upwards [eventually_ge_atTop r₀] with r hr
    have := hwpos r (hr₀.trans_le hr)
    have := hX r (hrX.trans hr)
    simp only [v, q]
    field_simp
  refine ⟨hfrv, hf0, ?_⟩
  have hterm : Tendsto (fun r => (1 - δ r) * (1 + a⁻¹ * (h r / f r))) atTop (𝓝 1) := by
    simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub hδ0).mul
      ((hf0.const_mul a⁻¹).const_add 1)
  apply hterm.congr'
  filter_upwards [eventually_ge_atTop r₀] with r hr
  have hrpos : 0 < r := lt_of_lt_of_le hr₀ hr
  have hfr := hX r (hrX.trans hr)
  rw [hode r hr]
  field_simp

/-- **Lemma I.5.5.** Let `h > 0` be measurable and regularly varying of index `b > 0`, let
`a > 0`, and let `f > 0` be differentiable on `(0, ∞)` with `f' / ((a f + h) / r) → 1`. Then `f`
is regularly varying of index `max a b`, and if `b ≤ a` then `h / f → 0` and
`f' / (a f / r) → 1`. -/
theorem regularlyVarying_max_and_tendsto_of_tendsto_deriv_ratio {f f' h : ℝ → ℝ} {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hhm : Measurable h) (hh : RegularlyVarying b h)
    (hpos : ∀ x, 0 < x → 0 < h x) (hfpos : ∀ x, 0 < x → 0 < f x)
    (hderiv : ∀ x, 0 < x → HasDerivAt f (f' x) x)
    (hasym : Tendsto (fun r => f' r / ((a * f r + h r) / r)) atTop (𝓝 1)) :
    RegularlyVarying (max a b) f ∧ (b ≤ a →
      Tendsto (fun r => h r / f r) atTop (𝓝 0) ∧
        Tendsto (fun r => f' r / (a * f r / r)) atTop (𝓝 1)) := by
  rcases lt_trichotomy b a with hba | rfl | hab
  · obtain ⟨hfrv, hf0, hder⟩ := regularlyVarying_and_tendsto_of_tendsto_deriv_ratio_of_lt hhm hh
      hb ha hba hpos hfpos hderiv hasym
    exact ⟨by rwa [max_eq_left hba.le], fun _ => ⟨hf0, hder⟩⟩
  · obtain ⟨hfrv, hf0, hder⟩ := regularlyVarying_and_tendsto_of_tendsto_deriv_ratio_of_eq hhm hh
      ha ((eventually_gt_atTop 0).mono hfpos) hderiv hasym
    exact ⟨by rwa [max_self], fun _ => ⟨hf0, hder⟩⟩
  · refine ⟨?_, fun hle => absurd hle (not_le.2 hab)⟩
    rw [max_eq_right hab.le]
    exact regularlyVarying_of_tendsto_deriv_ratio hhm hh ha hab hderiv hasym

end PercLib.Analysis
