/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Adapted from contributor yujinhkim, repository `yujinhkim/lrp`, branch `critical-lrp-1`,
commit `d382e4c28d92dd4e698ebf4f2aaf0bc932ae73fc`, file
`PercLib/CriticalLRP/VolumeMoments/FirstMoment/LogIntegrability.lean`. Licence: Apache-2.0
as declared in that revision's file headers and `third_party/critical-lrp/NOTICE.md`.
Upstream origin: `yujinhkim/Critical-Long-range-percolation`, revision
`3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf` (not independently verified).
Changes: `LogarithmicallyIntegrable` is the notion of
`PercLib/Analysis/RegularVariation/Defs.lean` (measurability on a tail); the source's
`logIntegrable_mono`, `lintegral_Ioo_ofReal_rpow`, `ofReal_hardyMajorant` and
`lintegral_hardyMajorant_le` are replaced by the existing
`LogarithmicallyIntegrable.mono`, `lintegral_Ioo_rpow`, `ofReal_mul_tailIntegral` and
`lintegral_transform_first`; the triangle identity and the measurability of the parametric
tail integral are stated for an arbitrary s-finite measure and integrand; no disabled linters,
`autoImplicit` or `maxHeartbeats`.

Mathematical reference: T. Hutchcroft, *Critical long-range percolation I: High effective
dimension*, arXiv:2508.18807v1, Lemma I.4.13 (p. 39).
-/
module

public import PercLib.Analysis.RegularVariation.LogErrorTransforms

/-! # The Hardy majorant of Lemma I.4.13

For `a > 0` and `h` with `∫_{r₀}^∞ |h s| ds / s < ∞`, the majorant
`r ↦ r^{a-1} ∫_r^∞ s^{-a-1} |h s| ds` is integrable on `(r₀, ∞)`; this is the integrability
content of the first clause of Lemma I.4.13, by Tonelli on the triangle `{r₀ < r < s}`.

## Main results

* `LogarithmicallyIntegrable.const_mul`, `LogarithmicallyIntegrable.neg`,
  `LogarithmicallyIntegrable.add`: closure properties of logarithmic integrability;
* `lintegral_Ioi_mul_lintegral_Ioi`: Tonelli on the triangle `{c < r < s}`;
* `stronglyMeasurable_setIntegral_Ioi`: the parametric tail integral `r ↦ ∫_{(r,∞)} g` is
  strongly measurable;
* `integrableOn_rpow_mul_integral_Ioi_rpow_mul_abs`: integrability of the Hardy majorant.
-/

@[expose] public section

open Filter Set MeasureTheory
open scoped Topology ENNReal

namespace PercLib.Analysis

/-! ### Closure properties of `LogarithmicallyIntegrable` -/

namespace LogarithmicallyIntegrable

variable {g h : ℝ → ℝ}

/-- A constant multiple of a logarithmically integrable function is logarithmically
integrable. -/
theorem const_mul (hh : LogarithmicallyIntegrable h) (c : ℝ) :
    LogarithmicallyIntegrable (fun r => c * h r) := by
  obtain ⟨⟨a, ha⟩, r₀, hr₀, hint⟩ := hh
  refine ⟨⟨a, measurable_const.mul ha⟩, r₀, hr₀, ?_⟩
  have : (fun r => |c * h r| / r) = fun r => |c| * (|h r| / r) := by
    ext r
    rw [abs_mul, mul_div_assoc]
  rw [this]
  exact hint.const_mul |c|

/-- The negative of a logarithmically integrable function is logarithmically integrable. -/
theorem neg (hh : LogarithmicallyIntegrable h) :
    LogarithmicallyIntegrable (fun r => -h r) := by
  simpa using hh.const_mul (-1)

/-- The sum of two logarithmically integrable functions is logarithmically integrable. -/
theorem add (hg : LogarithmicallyIntegrable g) (hh : LogarithmicallyIntegrable h) :
    LogarithmicallyIntegrable (fun r => g r + h r) := by
  obtain ⟨⟨a, ha⟩, r₀, hr₀, hgint⟩ := hg
  obtain ⟨⟨b, hb⟩, r₁, hr₁, hhint⟩ := hh
  set c := max a b with hc
  have hmc : Measurable ((Ici c).domRestrict (fun r => g r + h r)) :=
    (measurable_restrict_Ici_mono ha (le_max_left a b)).add
      (measurable_restrict_Ici_mono hb (le_max_right a b))
  obtain ⟨F, hF, hFeq⟩ := exists_measurable_eqOn_Ici hmc
  set d := max (max r₀ r₁) c with hd
  have hd₀ : r₀ ≤ d := (le_max_left _ _).trans (le_max_left _ _)
  have hd₁ : r₁ ≤ d := (le_max_right _ _).trans (le_max_left _ _)
  have hdc : c ≤ d := le_max_right _ _
  refine ⟨⟨c, hmc⟩, d, hr₀.trans_le hd₀, ?_⟩
  have hsum : IntegrableOn (fun r => |g r| / r + |h r| / r) (Ioi d) :=
    (hgint.mono_set (Ioi_subset_Ioi hd₀)).add (hhint.mono_set (Ioi_subset_Ioi hd₁))
  have hmeas : AEStronglyMeasurable (fun r => |g r + h r| / r) (volume.restrict (Ioi d)) :=
    (((continuous_abs.measurable.comp hF).div measurable_id).aestronglyMeasurable).congr
      (ae_restrict_of_forall_mem measurableSet_Ioi fun r hr => by
        change |F r| / r = |g r + h r| / r
        rw [hFeq r (hdc.trans hr.le)])
  refine hsum.mono' hmeas (ae_restrict_of_forall_mem measurableSet_Ioi fun r hr => ?_)
  have hr0 : 0 < r := hr₀.trans_le (hd₀.trans hr.le)
  rw [Real.norm_of_nonneg (div_nonneg (abs_nonneg _) hr0.le), ← add_div]
  exact div_le_div_of_nonneg_right (abs_add_le _ _) hr0.le

end LogarithmicallyIntegrable

/-! ### Tonelli on the triangle `{c < r < s}` -/

/-- **Tonelli on the triangle** `{c < r < s}`:
`∫_{(c,∞)} p(r) ∫_{(r,∞)} q(s) ds dr = ∫_{(c,∞)} q(s) ∫_{(c,s)} p(r) dr ds`. -/
theorem lintegral_Ioi_mul_lintegral_Ioi {μ : Measure ℝ} [SFinite μ] {p q : ℝ → ℝ≥0∞}
    (hp : Measurable p) (hq : Measurable q) (c : ℝ) :
    ∫⁻ r in Ioi c, p r * ∫⁻ s in Ioi r, q s ∂μ ∂μ
      = ∫⁻ s in Ioi c, q s * ∫⁻ r in Ioo c s, p r ∂μ ∂μ := by
  set T : Set (ℝ × ℝ) := {x | c < x.1 ∧ x.1 < x.2} with hT
  have hTm : MeasurableSet T :=
    (measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_lt measurable_fst measurable_snd)
  set F : ℝ × ℝ → ℝ≥0∞ := T.indicator (fun x => p x.1 * q x.2) with hF
  have hFm : Measurable F :=
    ((hp.comp measurable_fst).mul (hq.comp measurable_snd)).indicator hTm
  have h1 : ∀ r, ∫⁻ s, F (r, s) ∂μ
      = (Ioi c).indicator (fun r => p r * ∫⁻ s in Ioi r, q s ∂μ) r := by
    intro r
    by_cases hr : c < r
    · rw [indicator_of_mem (show r ∈ Ioi c from hr),
        ← lintegral_const_mul _ hq, ← lintegral_indicator measurableSet_Ioi]
      refine lintegral_congr fun s => ?_
      by_cases hs : r < s <;> simp [hF, hT, indicator, hr, hs]
    · rw [indicator_of_notMem (show r ∉ Ioi c from hr)]
      simp [hF, hT, hr]
  have h2 : ∀ s, ∫⁻ r, F (r, s) ∂μ
      = (Ioi c).indicator (fun s => q s * ∫⁻ r in Ioo c s, p r ∂μ) s := by
    intro s
    by_cases hs : c < s
    · rw [indicator_of_mem (show s ∈ Ioi c from hs), mul_comm,
        ← lintegral_mul_const _ hp, ← lintegral_indicator measurableSet_Ioo]
      refine lintegral_congr fun r => ?_
      by_cases h1 : c < r <;> by_cases h2 : r < s <;> simp [hF, hT, indicator, h1, h2]
    · rw [indicator_of_notMem (show s ∉ Ioi c from hs)]
      refine (lintegral_congr fun r => ?_).trans lintegral_zero
      by_cases h1 : c < r
      · have h2 : ¬ r < s := fun h => hs (h1.trans h)
        simp [hF, hT, h1, h2]
      · simp [hF, hT, h1]
  calc ∫⁻ r in Ioi c, p r * ∫⁻ s in Ioi r, q s ∂μ ∂μ
      = ∫⁻ r, ∫⁻ s, F (r, s) ∂μ ∂μ := by
        rw [← lintegral_indicator measurableSet_Ioi]
        exact lintegral_congr fun r => (h1 r).symm
    _ = ∫⁻ s, ∫⁻ r, F (r, s) ∂μ ∂μ := lintegral_lintegral_swap hFm.aemeasurable
    _ = ∫⁻ s in Ioi c, q s * ∫⁻ r in Ioo c s, p r ∂μ ∂μ := by
        rw [← lintegral_indicator measurableSet_Ioi]
        exact lintegral_congr h2

/-! ### Measurability of the parametric tail integral -/

/-- The parametric tail integral `r ↦ ∫_{(r,∞)} g` of a strongly measurable function is
strongly measurable (no integrability is needed: off the integrable set the Bochner integral
takes the value `0`). -/
theorem stronglyMeasurable_setIntegral_Ioi {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {μ : Measure ℝ} [SFinite μ] {g : ℝ → E} (hg : StronglyMeasurable g) :
    StronglyMeasurable (fun r => ∫ s in Ioi r, g s ∂μ) := by
  have hjoint : StronglyMeasurable (fun x : ℝ × ℝ => (Ioi x.1).indicator g x.2) :=
    (hg.comp_measurable measurable_snd).indicator
      (measurableSet_lt measurable_fst measurable_snd)
  have hsm := hjoint.integral_prod_right' (ν := μ)
  convert hsm using 1
  funext r
  exact (integral_indicator measurableSet_Ioi).symm

/-! ### The majorant of Lemma I.4.13 -/

/-- **Lemma I.4.13, first clause, integrability content.** For `a > 0` and
`∫_{r₀}^∞ |h s| ds / s < ∞`, the Hardy majorant `r ↦ r^{a-1} ∫_r^∞ s^{-a-1} |h s| ds` is
integrable on `(r₀, ∞)`. -/
theorem integrableOn_rpow_mul_integral_Ioi_rpow_mul_abs {h : ℝ → ℝ} {a r₀ : ℝ} (ha : 0 < a)
    (hr₀ : 0 < r₀) (hm : Measurable h) (hint : IntegrableOn (fun r => |h r| / r) (Ioi r₀)) :
    IntegrableOn (fun r => r ^ (a - 1) * ∫ s in Ioi r, s ^ (-a - 1) * |h s|) (Ioi r₀) := by
  have hmeas : Measurable (fun r => r ^ (a - 1) * ∫ s in Ioi r, s ^ (-a - 1) * |h s|) := by
    have hg : StronglyMeasurable (fun s : ℝ => s ^ (-a - 1) * |h s|) :=
      (by fun_prop : Measurable fun s : ℝ => s ^ (-a - 1) * |h s|).stronglyMeasurable
    exact (measurable_id.pow_const _).mul
      (stronglyMeasurable_setIntegral_Ioi (μ := volume) hg).measurable
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_restrict_of_forall_mem measurableSet_Ioi fun r hr => by
    have hr0 : 0 < r := hr₀.trans hr
    exact mul_nonneg (Real.rpow_nonneg hr0.le _)
      (setIntegral_nonneg measurableSet_Ioi fun s hs =>
        mul_nonneg (Real.rpow_nonneg (hr0.trans hs).le _) (abs_nonneg _)))]
  refine (lintegral_transform_first ha hr₀ hm hint).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_)
  exact hint.setLIntegral_lt_top

end PercLib.Analysis
