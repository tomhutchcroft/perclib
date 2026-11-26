/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Lemma I.4.13 of T. Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1
(logarithmic error transforms): for `a > 0` the transforms
`r ↦ r^a ∫_r^∞ s^{-a-1} h(s) ds` and `r ↦ r^{-a} ∫_{r₀}^r s^{a-1} h(s) ds` of a
logarithmically integrable error function `h` are again logarithmically integrable error
functions.

Ported from the repository `yujinhkim/lrp`, branch
`critical-lrp-1`, commit `d382e4c28d92dd4e698ebf4f2aaf0bc932ae73fc`, file
`PercLib/CriticalLRP/Analysis/Lemma_I_4_13.lean`; licence Apache-2.0 as declared in that
commit's file headers and `third_party/critical-lrp/NOTICE.md`; upstream
`yujinhkim/Critical-Long-range-percolation` at `3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf`.
Modified: the source definitions `potKer`, `potKer2`, `logTransformFirst` and
`logTransformSecond` are written out inline in every statement and proof (no new
definition); `IsLogErrorFunction` and `LogarithmicallyIntegrable` are those of
`PercLib/Analysis/RegularVariation/Defs.lean`, which ask measurability only on a tail, so
`lemma_I_4_13_first`, `isLogErrorFunction_add` and `isLogErrorFunction_congr` are proved
under that weaker hypothesis (the transform is first computed for a globally measurable
function agreeing with `h` on a tail, `logTransformFirst_eqOn_Ici`), and
`isLogErrorFunction_congr` asks tail measurability of `g` instead of global measurability;
`import Mathlib`-style imports, `autoImplicit`, disabled linters and `#print` lines are
removed.
-/
module

public import PercLib.Analysis.RegularVariation.Defs
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Order.Group.Lattice

/-! # Logarithmic error transforms (Lemma I.4.13)

* `lintegral_transform_first`, `lintegral_transform_second`: the two Tonelli estimates of
  the proof of Lemma I.4.13, `∫_{r₀}^∞ (…) dr ≤ a⁻¹ ∫_{r₀}^∞ |h s| ds/s`;
* `lemma_I_4_13_first`: the transform `r ↦ r^a ∫_r^∞ s^{-a-1} h(s) ds` of a log-error
  function is a log-error function;
* `lemma_I_4_13_second`, `lemma_I_4_13_second_from_one`: the same for
  `r ↦ r^{-a} ∫_{r₀}^r s^{a-1} h(s) ds` (lower limit `r₀`, respectively the paper's `1`);
* closure properties: `isLogErrorFunction_congr`, `isLogErrorFunction_add`,
  `isLogErrorFunction_const_rpow_neg`.
-/

@[expose] public section

open Filter Set MeasureTheory
open scoped Topology

namespace PercLib.Analysis

/-! ### A one-dimensional power computation -/

/-- `∫⁻_{Ioo r₀ s} ofReal (r^{a-1}) = ofReal ((s^a - r₀^a)/a)`. -/
theorem lintegral_Ioo_rpow {a r₀ s : ℝ} (ha : 0 < a) (hr₀ : 0 < r₀) (hs : r₀ ≤ s) :
    ∫⁻ r in Set.Ioo r₀ s, ENNReal.ofReal (r ^ (a - 1))
      = ENNReal.ofReal ((s ^ a - r₀ ^ a) / a) := by
  have hcont : ContinuousOn (fun r : ℝ => r ^ (a - 1)) (Icc r₀ s) := by
    intro x hx
    exact (Real.continuousAt_rpow_const x (a - 1)
      (Or.inl (ne_of_gt (lt_of_lt_of_le hr₀ hx.1)))).continuousWithinAt
  have hint : IntegrableOn (fun r : ℝ => r ^ (a - 1)) (Icc r₀ s) volume :=
    hcont.integrableOn_Icc
  have hint' : IntegrableOn (fun r : ℝ => r ^ (a - 1)) (Set.Ioo r₀ s) volume :=
    hint.mono_set Ioo_subset_Icc_self
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioo r₀ s)] (fun r : ℝ => r ^ (a - 1)) :=
    (ae_restrict_mem measurableSet_Ioo).mono
      (fun r hr => Real.rpow_nonneg (le_of_lt (lt_trans hr₀ hr.1)) _)
  rw [← ofReal_integral_eq_lintegral_ofReal hint' hnn]
  congr 1
  rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hs,
    integral_rpow (Or.inr ⟨?_, ?_⟩)]
  · norm_num
  · intro h; linarith
  · intro h
    rw [uIcc_of_le hs] at h
    exact absurd h.1 (not_le.2 hr₀)

/-! ### Integrability of the tail integrand -/

/-- If `∫_{r₀}^∞ |h s| ds/s < ∞` then `s ↦ s^{-a-1}|h s|` is integrable on every
tail `(r,∞)` with `r > r₀`, for `a > 0`. -/
theorem integrableOn_rpow_mul_abs {h : ℝ → ℝ} {a r r₀ : ℝ} (ha : 0 < a) (hmeas : Measurable h)
    (hr : r₀ < r) (hr₀ : 0 < r₀)
    (hint : IntegrableOn (fun s => |h s| / s) (Ioi r₀) volume) :
    IntegrableOn (fun s => s ^ (-a - 1) * |h s|) (Ioi r) volume := by
  have hrpos : 0 < r := lt_trans hr₀ hr
  have hbase : IntegrableOn (fun s => r ^ (-a) * (|h s| / s)) (Ioi r) volume :=
    (hint.mono_set (Ioi_subset_Ioi hr.le)).const_mul _
  refine hbase.mono' ?_ ?_
  · have hcont : ContinuousOn (fun s : ℝ => s ^ (-a - 1)) (Ioi r) :=
      fun s hs => (Real.continuousAt_rpow_const s (-a - 1)
        (Or.inl (ne_of_gt (lt_trans hrpos hs)))).continuousWithinAt
    exact (hcont.aestronglyMeasurable measurableSet_Ioi).mul
      hmeas.abs.aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs0 : 0 < s := lt_trans hrpos hs
    have hle : r ≤ s := hs.le
    have h1 : s ^ (-a) ≤ r ^ (-a) := by
      rw [Real.rpow_neg hs0.le, Real.rpow_neg hrpos.le]
      exact inv_anti₀ (Real.rpow_pos_of_pos hrpos a) (Real.rpow_le_rpow hrpos.le hle ha.le)
    have h2 : s ^ (-a - 1) = s ^ (-a) * s⁻¹ := by
      rw [show -a - 1 = -a + (-1) by ring, Real.rpow_add hs0, Real.rpow_neg_one]
    have hnn : 0 ≤ s ^ (-a - 1) := Real.rpow_nonneg hs0.le _
    have hgoal : ‖s ^ (-a - 1) * |h s|‖ = s ^ (-a - 1) * |h s| := by
      rw [Real.norm_eq_abs, abs_mul, abs_abs, abs_of_nonneg hnn]
    rw [hgoal]
    calc s ^ (-a - 1) * |h s| = s ^ (-a) * s⁻¹ * |h s| := by rw [h2]
      _ ≤ r ^ (-a) * s⁻¹ * |h s| :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 (by positivity))
            (abs_nonneg _)
      _ = r ^ (-a) * (|h s| / s) := by field_simp

/-! ### The Tonelli computation behind Lemma I.4.13 -/

/-- Pointwise form of the first step of the Tonelli computation (the source's kernel
`potKer a h r s` is written out). -/
theorem ofReal_mul_tailIntegral {h : ℝ → ℝ} {a r r₀ : ℝ} (ha : 0 < a) (hmeas : Measurable h)
    (hr : r₀ < r) (hr₀ : 0 < r₀)
    (hint : IntegrableOn (fun s => |h s| / s) (Ioi r₀) volume) :
    ENNReal.ofReal (r ^ (a - 1) * ∫ s in Ioi r, s ^ (-a - 1) * |h s|)
      = ∫⁻ s in Ioi r, ENNReal.ofReal (r ^ (a - 1) * (s ^ (-a - 1) * |h s|)) := by
  have hrpos : 0 < r := lt_trans hr₀ hr
  have hInt : IntegrableOn (fun s => s ^ (-a - 1) * |h s|) (Ioi r) volume :=
    integrableOn_rpow_mul_abs ha hmeas hr hr₀ hint
  have hnn : ∀ᵐ s ∂(volume.restrict (Ioi r)), 0 ≤ s ^ (-a - 1) * |h s| :=
    (ae_restrict_mem measurableSet_Ioi).mono
      (fun s hs => mul_nonneg (Real.rpow_nonneg (le_of_lt (lt_trans hrpos hs)) _) (abs_nonneg _))
  rw [ENNReal.ofReal_mul (Real.rpow_nonneg hrpos.le _),
    ofReal_integral_eq_lintegral_ofReal hInt hnn]
  have hm : Measurable (fun s => ENNReal.ofReal (s ^ (-a - 1) * |h s|)) := by
    fun_prop
  rw [← lintegral_const_mul'' (ENNReal.ofReal (r ^ (a - 1))) hm.aemeasurable]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  exact (ENNReal.ofReal_mul (Real.rpow_nonneg hrpos.le _)).symm

/-- **Tonelli estimate for the first transform** (the computation in the proof of
Lemma I.4.13 of the paper):
`∫_{r₀}^∞ r^{a-1} (∫_r^∞ s^{-a-1}|h s| ds) dr ≤ a⁻¹ ∫_{r₀}^∞ |h s| ds/s`,
in `lintegral` form. -/
theorem lintegral_transform_first {h : ℝ → ℝ} {a r₀ : ℝ} (ha : 0 < a) (hr₀ : 0 < r₀)
    (hmeas : Measurable h) (hint : IntegrableOn (fun s => |h s| / s) (Ioi r₀) volume) :
    ∫⁻ r in Ioi r₀, ENNReal.ofReal (r ^ (a - 1) * ∫ s in Ioi r, s ^ (-a - 1) * |h s|)
      ≤ ENNReal.ofReal a⁻¹ * ∫⁻ s in Ioi r₀, ENNReal.ofReal (|h s| / s) := by
  obtain ⟨K, hK⟩ : ∃ K : ℝ → ℝ → ENNReal,
      K = fun r s => ENNReal.ofReal (r ^ (a - 1) * (s ^ (-a - 1) * |h s|)) := ⟨_, rfl⟩
  have hG : Measurable (Function.uncurry K) := by
    subst hK
    unfold Function.uncurry
    fun_prop
  -- step 1: pointwise rewriting of the integrand
  have step1 : ∫⁻ r in Ioi r₀, ENNReal.ofReal (r ^ (a - 1) * ∫ s in Ioi r, s ^ (-a - 1) * |h s|)
      = ∫⁻ r in Ioi r₀, ∫⁻ s in Ioi r, K r s := by
    refine lintegral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    rw [hK]
    exact ofReal_mul_tailIntegral ha hmeas hr hr₀ hint
  -- step 2: Tonelli
  have step2 : ∫⁻ r in Ioi r₀, ∫⁻ s in Ioi r, K r s
      = ∫⁻ s in Ioi r₀, ∫⁻ r in Set.Ioo r₀ s, K r s := by
    have hmk : MeasurableSet {p : ℝ × ℝ | r₀ < p.1 ∧ p.1 < p.2} :=
      (measurableSet_lt measurable_const measurable_fst).inter
        (measurableSet_lt measurable_fst measurable_snd)
    have hswap : ∫⁻ r, ∫⁻ s, (if r₀ < r ∧ r < s then K r s else 0)
        = ∫⁻ s, ∫⁻ r, (if r₀ < r ∧ r < s then K r s else 0) :=
      lintegral_lintegral_swap ((Measurable.ite hmk hG measurable_const).aemeasurable)
    have hL : ∫⁻ r, ∫⁻ s, (if r₀ < r ∧ r < s then K r s else 0)
        = ∫⁻ r in Ioi r₀, ∫⁻ s in Ioi r, K r s := by
      rw [← lintegral_indicator measurableSet_Ioi]
      refine lintegral_congr fun r => ?_
      by_cases hr : r₀ < r
      · rw [Set.indicator_of_mem (mem_Ioi.2 hr), ← lintegral_indicator measurableSet_Ioi]
        exact lintegral_congr fun s => by simp only [Set.indicator_apply, Set.mem_Ioi]; simp [hr]
      · rw [Set.indicator_of_notMem (by simpa [mem_Ioi] using hr)]
        simp [hr]
    have hinner : ∀ s, ∫⁻ r, (if r₀ < r ∧ r < s then K r s else 0)
        = ∫⁻ r in Set.Ioo r₀ s, K r s := by
      intro s
      rw [← lintegral_indicator measurableSet_Ioo]
      exact lintegral_congr fun r => by
        simp only [Set.indicator_apply, Set.mem_Ioo]
    have hR : ∫⁻ s, ∫⁻ r, (if r₀ < r ∧ r < s then K r s else 0)
        = ∫⁻ s in Ioi r₀, ∫⁻ r in Set.Ioo r₀ s, K r s := by
      simp only [hinner]
      rw [← lintegral_indicator measurableSet_Ioi]
      refine lintegral_congr fun s => ?_
      by_cases hs : r₀ < s
      · rw [Set.indicator_of_mem (mem_Ioi.2 hs)]
      · rw [Set.indicator_of_notMem (by simpa [mem_Ioi] using hs)]
        rw [Set.Ioo_eq_empty hs]
        simp
    exact hL.symm.trans (hswap.trans hR)
  -- step 3: evaluate the inner integral
  have step3 : ∫⁻ s in Ioi r₀, ∫⁻ r in Set.Ioo r₀ s, K r s
      = ∫⁻ s in Ioi r₀, ENNReal.ofReal (s ^ (-a - 1) * |h s| * ((s ^ a - r₀ ^ a) / a)) := by
    refine lintegral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hfac : ∀ᵐ r ∂(volume.restrict (Set.Ioo r₀ s)),
        K r s = ENNReal.ofReal (r ^ (a - 1)) * ENNReal.ofReal (s ^ (-a - 1) * |h s|) :=
      (ae_restrict_mem measurableSet_Ioo).mono (fun r hr => by
        rw [hK]
        exact ENNReal.ofReal_mul (Real.rpow_nonneg (le_of_lt (lt_trans hr₀ hr.1)) _))
    rw [lintegral_congr_ae hfac,
      lintegral_mul_const _ (by fun_prop : Measurable fun r : ℝ => ENNReal.ofReal (r ^ (a - 1))),
      lintegral_Ioo_rpow ha hr₀ hs.le, ← ENNReal.ofReal_mul (by
        have := Real.rpow_nonneg (lt_trans hr₀ hs).le (-a - 1)
        have : 0 ≤ (s ^ a - r₀ ^ a) / a := by
          have h2 : r₀ ^ a ≤ s ^ a := Real.rpow_le_rpow hr₀.le hs.le ha.le
          have h3 : 0 < a := ha
          exact div_nonneg (by linarith) h3.le
        positivity)]
    ring_nf
  -- step 4: pointwise domination and the final constant
  rw [step1, step2, step3]
  have hpt : ∀ᵐ s ∂(volume.restrict (Ioi r₀)),
      ENNReal.ofReal (s ^ (-a - 1) * |h s| * ((s ^ a - r₀ ^ a) / a))
        ≤ ENNReal.ofReal (a⁻¹ * (|h s| / s)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    apply ENNReal.ofReal_le_ofReal
    have hs0 : 0 < s := lt_trans hr₀ hs
    have h1 : s ^ (-a - 1) * s ^ a = s⁻¹ := by
      rw [← Real.rpow_add hs0, show -a - 1 + a = -1 by ring, Real.rpow_neg_one]
    have hnn : 0 ≤ s ^ (-a - 1) := Real.rpow_nonneg hs0.le _
    have hle1 : s ^ (-a - 1) * (s ^ a - r₀ ^ a) ≤ s⁻¹ := by
      have hsq : s ^ a - r₀ ^ a ≤ s ^ a := by
        have h2 := Real.rpow_nonneg hr₀.le a
        linarith
      calc s ^ (-a - 1) * (s ^ a - r₀ ^ a) ≤ s ^ (-a - 1) * s ^ a :=
            mul_le_mul_of_nonneg_left hsq hnn
        _ = s⁻¹ := h1
    have hstep : s ^ (-a - 1) * |h s| * ((s ^ a - r₀ ^ a) / a)
        = (|h s| * a⁻¹) * (s ^ (-a - 1) * (s ^ a - r₀ ^ a)) := by
      rw [div_eq_mul_inv]
      ring
    rw [hstep]
    calc (|h s| * a⁻¹) * (s ^ (-a - 1) * (s ^ a - r₀ ^ a))
        ≤ (|h s| * a⁻¹) * s⁻¹ :=
          mul_le_mul_of_nonneg_left hle1 (by positivity)
      _ = a⁻¹ * (|h s| / s) := by
          rw [div_eq_mul_inv]
          ring
  have hconst : ∫⁻ s in Ioi r₀, ENNReal.ofReal (a⁻¹ * (|h s| / s))
      = ENNReal.ofReal a⁻¹ * ∫⁻ s in Ioi r₀, ENNReal.ofReal (|h s| / s) := by
    have hfun : (fun s => ENNReal.ofReal (a⁻¹ * (|h s| / s)))
        = fun s => ENNReal.ofReal a⁻¹ * ENNReal.ofReal (|h s| / s) := by
      funext s
      exact ENNReal.ofReal_mul (le_of_lt (inv_pos.2 ha))
    rw [hfun, lintegral_const_mul'' _ (by fun_prop)]
  exact le_trans (lintegral_mono_ae hpt) (le_of_eq hconst)

/-! ### The first transform of Lemma I.4.13

The source's `logTransformFirst h a` is written out as
`fun r => r ^ a * ∫ s in Ioi r, s ^ (-a - 1) * h s`. -/

theorem measurable_logTransformFirst {h : ℝ → ℝ} {a : ℝ} (hmeas : Measurable h) :
    Measurable (fun r : ℝ => r ^ a * ∫ s in Ioi r, s ^ (-a - 1) * h s) := by
  have hF : StronglyMeasurable (fun s : ℝ => s ^ (-a - 1) * h s) := by
    have h1 : StronglyMeasurable (fun s : ℝ => s ^ (-a - 1)) := by
      fun_prop
    exact h1.mul hmeas.stronglyMeasurable
  have hjoint : StronglyMeasurable
      (fun p : ℝ × ℝ => (Ioi p.1).indicator (fun s => s ^ (-a - 1) * h s) p.2) :=
    hF.comp_measurable measurable_snd |>.indicator
      (measurableSet_lt measurable_fst measurable_snd)
  have hsm : StronglyMeasurable
      (fun r : ℝ => ∫ s, (Ioi r).indicator (fun s => s ^ (-a - 1) * h s) s) :=
    hjoint.integral_prod_right'
  have hEq : (fun r : ℝ => ∫ s, (Ioi r).indicator (fun s => s ^ (-a - 1) * h s) s)
      = fun r => ∫ s in Ioi r, s ^ (-a - 1) * h s := by
    funext r
    exact integral_indicator measurableSet_Ioi
  rw [hEq] at hsm
  exact (measurable_id.pow_const a).mul hsm.measurable

/-- **Logarithmic integrability of the first transform.** -/
theorem integrableOn_logTransformFirst {h : ℝ → ℝ} {a r₀ : ℝ} (ha : 0 < a) (hr₀ : 0 < r₀)
    (hmeas : Measurable h) (hint : IntegrableOn (fun s => |h s| / s) (Ioi r₀) volume) :
    IntegrableOn (fun r => |r ^ a * ∫ s in Ioi r, s ^ (-a - 1) * h s| / r) (Ioi r₀) volume := by
  have hmeasg : AEStronglyMeasurable (fun r => |r ^ a * ∫ s in Ioi r, s ^ (-a - 1) * h s| / r)
      (volume.restrict (Ioi r₀)) :=
    ((measurable_logTransformFirst hmeas).abs.div measurable_id).aestronglyMeasurable
  have hbdd : ∀ᵐ r ∂(volume.restrict (Ioi r₀)),
      |r ^ a * ∫ s in Ioi r, s ^ (-a - 1) * h s| / r
        ≤ r ^ (a - 1) * ∫ s in Ioi r, s ^ (-a - 1) * |h s| := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hrpos : 0 < r := lt_trans hr₀ hr
    have h1 : |∫ s in Ioi r, s ^ (-a - 1) * h s| ≤ ∫ s in Ioi r, s ^ (-a - 1) * |h s| := by
      refine le_trans abs_integral_le_integral_abs (le_of_eq ?_)
      refine setIntegral_congr_fun measurableSet_Ioi (fun s hs => ?_)
      rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (lt_trans hrpos hs).le _)]
    have hnonneg : (0:ℝ) ≤ r ^ (a - 1) := Real.rpow_nonneg hrpos.le _
    have hrw2 : r ^ a * r⁻¹ = r ^ (a - 1) := by
      rw [Real.rpow_sub hrpos a 1, Real.rpow_one, div_eq_mul_inv]
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hrpos.le _)]
    calc r ^ a * |∫ s in Ioi r, s ^ (-a - 1) * h s| / r
        = (r ^ a * r⁻¹) * |∫ s in Ioi r, s ^ (-a - 1) * h s| := by
          field_simp
      _ = r ^ (a - 1) * |∫ s in Ioi r, s ^ (-a - 1) * h s| := by rw [hrw2]
      _ ≤ r ^ (a - 1) * ∫ s in Ioi r, s ^ (-a - 1) * |h s| :=
          mul_le_mul_of_nonneg_left h1 hnonneg
  refine ⟨hmeasg, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (μ := volume.restrict (Ioi r₀))
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      exact div_nonneg (abs_nonneg _) (le_of_lt (lt_trans hr₀ hr)))]
  have hmono : ∫⁻ r in Ioi r₀, ENNReal.ofReal (|r ^ a * ∫ s in Ioi r, s ^ (-a - 1) * h s| / r)
      ≤ ∫⁻ r in Ioi r₀, ENNReal.ofReal (r ^ (a - 1) * ∫ s in Ioi r, s ^ (-a - 1) * |h s|) :=
    lintegral_mono_ae (hbdd.mono (fun r hr => ENNReal.ofReal_le_ofReal hr))
  refine lt_of_le_of_lt (le_trans hmono (lintegral_transform_first ha hr₀ hmeas hint)) ?_
  refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    ((ae_restrict_mem measurableSet_Ioi).mono
      (fun s hs => div_nonneg (abs_nonneg _) (le_of_lt (lt_trans hr₀ hs))))]
  exact ENNReal.ofReal_lt_top

/-- **The first transform is an error function**: it tends to `0` at `∞`. -/
theorem tendsto_logTransformFirst {h : ℝ → ℝ} {a r₀ : ℝ} (ha : 0 < a) (hmeas : Measurable h)
    (h0 : Tendsto h atTop (𝓝 0)) (hr₀ : 0 < r₀)
    (hint : IntegrableOn (fun s => |h s| / s) (Ioi r₀) volume) :
    Tendsto (fun r : ℝ => r ^ a * ∫ s in Ioi r, s ^ (-a - 1) * h s) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨R, hR⟩ : ∃ R : ℝ, ∀ s : ℝ, R ≤ s → |h s| ≤ a * (ε / 2) := by
    obtain ⟨R, hR⟩ := Metric.tendsto_atTop.1 h0 (a * (ε / 2)) (by positivity)
    exact ⟨R, fun s hs => by
      have h := hR s hs
      rw [Real.dist_eq, sub_zero, abs_lt] at h
      exact abs_le.2 ⟨le_of_lt h.1, le_of_lt h.2⟩⟩
  refine ⟨max R (r₀ + 1), fun r hr => ?_⟩
  have hrpos : r₀ < r := lt_of_lt_of_le (by linarith) (le_trans (le_max_right R (r₀ + 1)) hr)
  have hr0 : 0 < r := lt_trans hr₀ hrpos
  have hrR : R ≤ r := le_trans (le_max_left R (r₀ + 1)) hr
  have htail : IntegrableOn (fun s : ℝ => s ^ (-a - 1)) (Ioi r) volume :=
    integrableOn_Ioi_rpow_of_lt (by linarith) hr0
  have habs : IntegrableOn (fun s : ℝ => s ^ (-a - 1) * |h s|) (Ioi r) volume :=
    integrableOn_rpow_mul_abs ha hmeas hrpos hr₀ hint
  have hle : ∫ s in Ioi r, s ^ (-a - 1) * |h s| ≤ (a * (ε / 2)) * (r ^ (-a) / a) := by
    have hmono : ∫ s in Ioi r, s ^ (-a - 1) * |h s| ≤ ∫ s in Ioi r, (a * (ε / 2)) * s ^ (-a - 1) :=
      setIntegral_mono_on habs (htail.const_mul _) measurableSet_Ioi (fun s hs => by
        have hsa : |h s| ≤ a * (ε / 2) := hR s (le_trans hrR hs.le)
        have hnn : 0 ≤ s ^ (-a - 1) := Real.rpow_nonneg (lt_trans hr0 hs).le _
        nlinarith)
    rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith : -a - 1 < -1) hr0] at hmono
    have hval : -(r ^ (-a - 1 + 1)) / (-a - 1 + 1) = r ^ (-a) / a := by
      rw [show -a - 1 + 1 = -a by ring]
      field_simp
    rw [hval] at hmono
    exact hmono
  have hle2 : |∫ s in Ioi r, s ^ (-a - 1) * h s| ≤ ∫ s in Ioi r, s ^ (-a - 1) * |h s| := by
    refine le_trans abs_integral_le_integral_abs (le_of_eq ?_)
    refine setIntegral_congr_fun measurableSet_Ioi (fun s hs => ?_)
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (lt_trans hr0 hs).le _)]
  have hmain : |r ^ a * ∫ s in Ioi r, s ^ (-a - 1) * h s| ≤ ε / 2 := by
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hr0.le _)]
    calc r ^ a * |∫ s in Ioi r, s ^ (-a - 1) * h s|
        ≤ r ^ a * ∫ s in Ioi r, s ^ (-a - 1) * |h s| :=
          mul_le_mul_of_nonneg_left hle2 (Real.rpow_nonneg hr0.le _)
      _ ≤ r ^ a * ((a * (ε / 2)) * (r ^ (-a) / a)) :=
          mul_le_mul_of_nonneg_left hle (Real.rpow_nonneg hr0.le _)
      _ = ε / 2 := by
          rw [Real.rpow_neg hr0.le]
          field_simp
  rw [Real.dist_eq, sub_zero]
  linarith

/-- The first transform at `r` only sees `h` on `(r, ∞)`: if `F = h` on `[b, ∞)`, the two
transforms agree on `[b, ∞)`. (New; used to pass from tail measurability to global
measurability in `lemma_I_4_13_first`.) -/
theorem logTransformFirst_eqOn_Ici {h F : ℝ → ℝ} {a b : ℝ} (hF : ∀ x, b ≤ x → F x = h x)
    {r : ℝ} (hr : b ≤ r) :
    r ^ a * ∫ s in Ioi r, s ^ (-a - 1) * F s = r ^ a * ∫ s in Ioi r, s ^ (-a - 1) * h s := by
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi (fun s hs => ?_)
  rw [hF s (hr.trans (le_of_lt hs))]

/-! ### The second transform of Lemma I.4.13

The source's `logTransformSecond h a r₀` is written out as
`fun r => r ^ (-a) * ∫ s in Ioc r₀ r, s ^ (a - 1) * h s`, with the lower limit of
integration at `r₀` (the paper writes `∫_1^r`; the difference is the constant `∫_1^{r₀}`
times `r^{-a}`, see `lemma_I_4_13_second_from_one`). -/

theorem measurable_logTransformSecond {h : ℝ → ℝ} {a r₀ : ℝ} (hmeas : Measurable h) :
    Measurable (fun r : ℝ => r ^ (-a) * ∫ s in Set.Ioc r₀ r, s ^ (a - 1) * h s) := by
  have hF : StronglyMeasurable (fun s : ℝ => s ^ (a - 1) * h s) := by
    have h1 : StronglyMeasurable (fun s : ℝ => s ^ (a - 1)) := by fun_prop
    exact h1.mul hmeas.stronglyMeasurable
  have hjoint : StronglyMeasurable
      (fun p : ℝ × ℝ => (Ioc r₀ p.1).indicator (fun s => s ^ (a - 1) * h s) p.2) :=
    hF.comp_measurable measurable_snd |>.indicator
      (measurableSet_lt measurable_const measurable_snd |>.inter
        (measurableSet_le measurable_snd measurable_fst))
  have hsm : StronglyMeasurable
      (fun r : ℝ => ∫ s, (Ioc r₀ r).indicator (fun s => s ^ (a - 1) * h s) s) :=
    hjoint.integral_prod_right'
  have hEq : (fun r : ℝ => ∫ s, (Ioc r₀ r).indicator (fun s => s ^ (a - 1) * h s) s)
      = fun r => ∫ s in Set.Ioc r₀ r, s ^ (a - 1) * h s := by
    funext r
    exact integral_indicator measurableSet_Ioc
  rw [hEq] at hsm
  exact (measurable_id.pow_const (-a)).mul hsm.measurable

/-- `∫⁻_{r ≥ s} r^{-a-1} = s^{-a}/a`. -/
theorem lintegral_Ici_rpow_neg {a s : ℝ} (ha : 0 < a) (hs : 0 < s) :
    ∫⁻ r in Set.Ici s, ENNReal.ofReal (r ^ (-a - 1)) = ENNReal.ofReal (s ^ (-a) / a) := by
  have hint : IntegrableOn (fun r : ℝ => r ^ (-a - 1)) (Ioi s) volume :=
    integrableOn_Ioi_rpow_of_lt (by linarith) hs
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi s)] (fun r : ℝ => r ^ (-a - 1)) :=
    (ae_restrict_mem measurableSet_Ioi).mono
      (fun r hr => Real.rpow_nonneg (le_trans hs.le hr.le) _)
  rw [Measure.restrict_congr_set Ioi_ae_eq_Ici.symm]
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn]
  congr 1
  rw [integral_Ioi_rpow_of_lt (by linarith) hs, show -a - 1 + 1 = -a by ring]
  field_simp

/-- Pointwise form of the first step for the second transform. -/
theorem ofReal_mul_intervalIntegral {h : ℝ → ℝ} {a r r₀ : ℝ} (ha : 0 < a) (hmeas : Measurable h)
    (hr : r₀ < r) (hr₀ : 0 < r₀)
    (hint : IntegrableOn (fun s => |h s| / s) (Ioi r₀) volume) :
    ENNReal.ofReal (r ^ (-a - 1) * ∫ s in Set.Ioc r₀ r, s ^ (a - 1) * |h s|)
      = ∫⁻ s in Set.Ioc r₀ r, ENNReal.ofReal (r ^ (-a - 1) * (s ^ (a - 1) * |h s|)) := by
  have hrpos : 0 < r := lt_trans hr₀ hr
  have hInt : IntegrableOn (fun s => s ^ (a - 1) * |h s|) (Set.Ioc r₀ r) volume := by
    have hbase : IntegrableOn (fun s => r ^ a * (|h s| / s)) (Set.Ioc r₀ r) volume :=
      (hint.mono_set (fun x hx => hx.1)).const_mul _
    refine hbase.mono' ?_ ?_
    · have hcont : ContinuousOn (fun s : ℝ => s ^ (a - 1)) (Ioi r₀) :=
        fun s hs => (Real.continuousAt_rpow_const s (a - 1)
          (Or.inl (ne_of_gt (lt_trans hr₀ hs)))).continuousWithinAt
      exact ((hcont.aestronglyMeasurable measurableSet_Ioi).mono_set
        Ioc_subset_Ioi_self).mul hmeas.abs.aestronglyMeasurable.restrict
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      have hs0 : 0 < s := lt_trans hr₀ hs.1
      rw [Real.norm_eq_abs, abs_mul, abs_abs, abs_of_nonneg (Real.rpow_nonneg hs0.le _)]
      calc s ^ (a - 1) * |h s| = s ^ a * (|h s| / s) := by
            rw [show a - 1 = a + (-1) by ring, Real.rpow_add hs0, Real.rpow_neg_one]
            field_simp
        _ ≤ r ^ a * (|h s| / s) := by
            apply mul_le_mul_of_nonneg_right _ (div_nonneg (abs_nonneg _) hs0.le)
            exact Real.rpow_le_rpow hs0.le hs.2 ha.le
  have hnn : ∀ᵐ s ∂(volume.restrict (Set.Ioc r₀ r)), 0 ≤ s ^ (a - 1) * |h s| :=
    (ae_restrict_mem measurableSet_Ioc).mono
      (fun s hs => mul_nonneg (Real.rpow_nonneg (lt_trans hr₀ hs.1).le _) (abs_nonneg _))
  rw [ENNReal.ofReal_mul (Real.rpow_nonneg hrpos.le _),
    ofReal_integral_eq_lintegral_ofReal hInt hnn]
  have hm : AEMeasurable (fun s => ENNReal.ofReal (s ^ (a - 1) * |h s|))
      (volume.restrict (Set.Ioc r₀ r)) := by fun_prop
  rw [← lintegral_const_mul'' (ENNReal.ofReal (r ^ (-a - 1))) hm]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  exact (ENNReal.ofReal_mul (Real.rpow_nonneg hrpos.le _)).symm

/-- **Tonelli estimate for the second transform** (the second computation in the
proof of Lemma I.4.13):
`∫_{r₀}^∞ r^{-a-1} (∫_{r₀}^r s^{a-1}|h s| ds) dr ≤ a⁻¹ ∫_{r₀}^∞ |h s| ds/s`. -/
theorem lintegral_transform_second {h : ℝ → ℝ} {a r₀ : ℝ} (ha : 0 < a) (hr₀ : 0 < r₀)
    (hmeas : Measurable h) (hint : IntegrableOn (fun s => |h s| / s) (Ioi r₀) volume) :
    ∫⁻ r in Ioi r₀, ENNReal.ofReal (r ^ (-a - 1) * ∫ s in Set.Ioc r₀ r, s ^ (a - 1) * |h s|)
      ≤ ENNReal.ofReal a⁻¹ * ∫⁻ s in Ioi r₀, ENNReal.ofReal (|h s| / s) := by
  obtain ⟨K, hK⟩ : ∃ K : ℝ → ℝ → ENNReal,
      K = fun r s => ENNReal.ofReal (r ^ (-a - 1) * (s ^ (a - 1) * |h s|)) := ⟨_, rfl⟩
  have hG : Measurable (Function.uncurry K) := by
    subst hK
    unfold Function.uncurry
    fun_prop
  have step1 : ∫⁻ r in Ioi r₀,
        ENNReal.ofReal (r ^ (-a - 1) * ∫ s in Set.Ioc r₀ r, s ^ (a - 1) * |h s|)
      = ∫⁻ r in Ioi r₀, ∫⁻ s in Set.Ioc r₀ r, K r s := by
    refine lintegral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    rw [hK]
    exact ofReal_mul_intervalIntegral ha hmeas hr hr₀ hint
  have step2 : ∫⁻ r in Ioi r₀, ∫⁻ s in Set.Ioc r₀ r, K r s
      = ∫⁻ s in Ioi r₀, ∫⁻ r in Set.Ici s, K r s := by
    have hmk : MeasurableSet {p : ℝ × ℝ | r₀ < p.2 ∧ p.2 ≤ p.1} :=
      (measurableSet_lt measurable_const measurable_snd).inter
        (measurableSet_le measurable_snd measurable_fst)
    have hswap : ∫⁻ r, ∫⁻ s, (if r₀ < s ∧ s ≤ r then K r s else 0)
        = ∫⁻ s, ∫⁻ r, (if r₀ < s ∧ s ≤ r then K r s else 0) :=
      lintegral_lintegral_swap ((Measurable.ite hmk hG measurable_const).aemeasurable)
    have hL : ∫⁻ r, ∫⁻ s, (if r₀ < s ∧ s ≤ r then K r s else 0)
        = ∫⁻ r in Ioi r₀, ∫⁻ s in Set.Ioc r₀ r, K r s := by
      rw [← lintegral_indicator measurableSet_Ioi]
      refine lintegral_congr fun r => ?_
      by_cases hr : r₀ < r
      · rw [Set.indicator_of_mem (mem_Ioi.2 hr), ← lintegral_indicator measurableSet_Ioc]
        exact lintegral_congr fun s => by
          simp only [Set.indicator_apply, Set.mem_Ioc]
      · rw [Set.indicator_of_notMem (by simpa [mem_Ioi] using hr)]
        have hno : ∀ s : ℝ, ¬ (r₀ < s ∧ s ≤ r) := fun s => by
          rintro ⟨h1, h2⟩
          linarith [not_lt.1 hr]
        simp [hno]
    have hR : ∫⁻ s, ∫⁻ r, (if r₀ < s ∧ s ≤ r then K r s else 0)
        = ∫⁻ s in Ioi r₀, ∫⁻ r in Set.Ici s, K r s := by
      have hinner : ∀ s, ∫⁻ r, (if r₀ < s ∧ s ≤ r then K r s else 0)
          = (Ioi r₀).indicator (fun s => ∫⁻ r in Set.Ici s, K r s) s := by
        intro s
        by_cases hs : r₀ < s
        · rw [Set.indicator_of_mem (mem_Ioi.2 hs), ← lintegral_indicator measurableSet_Ici]
          exact lintegral_congr fun r => by
            simp only [Set.indicator_apply, Set.mem_Ici]
            by_cases hsr : s ≤ r
            · simp [hs, hsr]
            · simp [hsr]
        · rw [Set.indicator_of_notMem (by simpa [mem_Ioi] using hs)]
          have hno : ∀ r : ℝ, ¬ (r₀ < s ∧ s ≤ r) := fun r => by
            rintro ⟨h1, _⟩
            exact absurd h1 hs
          simp [hno]
      simp only [hinner]
      rw [lintegral_indicator measurableSet_Ioi]
    exact hL.symm.trans (hswap.trans hR)
  have step3 : ∫⁻ s in Ioi r₀, ∫⁻ r in Set.Ici s, K r s
      = ∫⁻ s in Ioi r₀, ENNReal.ofReal (s ^ (a - 1) * |h s| * (s ^ (-a) / a)) := by
    refine lintegral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hfac : ∀ᵐ r ∂(volume.restrict (Set.Ici s)),
        K r s = ENNReal.ofReal (r ^ (-a - 1)) * ENNReal.ofReal (s ^ (a - 1) * |h s|) :=
      (ae_restrict_mem measurableSet_Ici).mono (fun r hr => by
        rw [hK]
        exact ENNReal.ofReal_mul (Real.rpow_nonneg (le_trans (lt_trans hr₀ hs).le hr) _))
    rw [lintegral_congr_ae hfac,
      lintegral_mul_const _ (by fun_prop : Measurable fun r : ℝ => ENNReal.ofReal (r ^ (-a - 1))),
      lintegral_Ici_rpow_neg ha (lt_trans hr₀ hs)]
    rw [mul_comm,
      ← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg (lt_trans hr₀ hs).le _) (abs_nonneg _))]
  rw [step1, step2, step3]
  have hpt : ∀ᵐ s ∂(volume.restrict (Ioi r₀)),
      ENNReal.ofReal (s ^ (a - 1) * |h s| * (s ^ (-a) / a))
        ≤ ENNReal.ofReal (a⁻¹ * (|h s| / s)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    apply ENNReal.ofReal_le_ofReal
    have hs0 : 0 < s := lt_trans hr₀ hs
    have h1 : s ^ (a - 1) * s ^ (-a) = s⁻¹ := by
      rw [← Real.rpow_add hs0, show a - 1 + -a = -1 by ring, Real.rpow_neg_one]
    have hstep : s ^ (a - 1) * |h s| * (s ^ (-a) / a)
        = (s ^ (a - 1) * s ^ (-a)) * (|h s| * a⁻¹) := by
      rw [div_eq_mul_inv]; ring
    rw [hstep, h1, div_eq_mul_inv]
    exact le_of_eq (by ring)
  have hconst : ∫⁻ s in Ioi r₀, ENNReal.ofReal (a⁻¹ * (|h s| / s))
      = ENNReal.ofReal a⁻¹ * ∫⁻ s in Ioi r₀, ENNReal.ofReal (|h s| / s) := by
    have hfun : (fun s => ENNReal.ofReal (a⁻¹ * (|h s| / s)))
        = fun s => ENNReal.ofReal a⁻¹ * ENNReal.ofReal (|h s| / s) := by
      funext s
      exact ENNReal.ofReal_mul (le_of_lt (inv_pos.2 ha))
    rw [hfun, lintegral_const_mul'' _ (by fun_prop)]
  exact le_trans (lintegral_mono_ae hpt) (le_of_eq hconst)

/-- **Logarithmic integrability of the second transform.** -/
theorem integrableOn_logTransformSecond {h : ℝ → ℝ} {a r₀ : ℝ} (ha : 0 < a) (hr₀ : 0 < r₀)
    (hmeas : Measurable h) (hint : IntegrableOn (fun s => |h s| / s) (Ioi r₀) volume) :
    IntegrableOn (fun r => |r ^ (-a) * ∫ s in Set.Ioc r₀ r, s ^ (a - 1) * h s| / r)
      (Ioi r₀) volume := by
  have hmeasg : AEStronglyMeasurable
      (fun r => |r ^ (-a) * ∫ s in Set.Ioc r₀ r, s ^ (a - 1) * h s| / r)
      (volume.restrict (Ioi r₀)) :=
    ((measurable_logTransformSecond hmeas).abs.div measurable_id).aestronglyMeasurable
  have hbdd : ∀ᵐ r ∂(volume.restrict (Ioi r₀)),
      |r ^ (-a) * ∫ s in Set.Ioc r₀ r, s ^ (a - 1) * h s| / r
        ≤ r ^ (-a - 1) * ∫ s in Set.Ioc r₀ r, s ^ (a - 1) * |h s| := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hrpos : 0 < r := lt_trans hr₀ hr
    have h1 : |∫ s in Set.Ioc r₀ r, s ^ (a - 1) * h s|
        ≤ ∫ s in Set.Ioc r₀ r, s ^ (a - 1) * |h s| := by
      refine le_trans abs_integral_le_integral_abs (le_of_eq ?_)
      refine setIntegral_congr_fun measurableSet_Ioc (fun s hs => ?_)
      rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (lt_trans hr₀ hs.1).le _)]
    have hrw : r ^ (-a) * r⁻¹ = r ^ (-a - 1) := by
      rw [Real.rpow_sub hrpos (-a) 1, Real.rpow_one, div_eq_mul_inv]
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hrpos.le _)]
    calc r ^ (-a) * |∫ s in Set.Ioc r₀ r, s ^ (a - 1) * h s| / r
        = (r ^ (-a) * r⁻¹) * |∫ s in Set.Ioc r₀ r, s ^ (a - 1) * h s| := by
          field_simp
      _ = r ^ (-a - 1) * |∫ s in Set.Ioc r₀ r, s ^ (a - 1) * h s| := by rw [hrw]
      _ ≤ r ^ (-a - 1) * ∫ s in Set.Ioc r₀ r, s ^ (a - 1) * |h s| :=
          mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hrpos.le _)
  refine ⟨hmeasg, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (μ := volume.restrict (Ioi r₀))
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      exact div_nonneg (abs_nonneg _) (le_of_lt (lt_trans hr₀ hr)))]
  have hmono : ∫⁻ r in Ioi r₀,
        ENNReal.ofReal (|r ^ (-a) * ∫ s in Set.Ioc r₀ r, s ^ (a - 1) * h s| / r)
      ≤ ∫⁻ r in Ioi r₀,
        ENNReal.ofReal (r ^ (-a - 1) * ∫ s in Set.Ioc r₀ r, s ^ (a - 1) * |h s|) :=
    lintegral_mono_ae (hbdd.mono (fun r hr => ENNReal.ofReal_le_ofReal hr))
  refine lt_of_le_of_lt (le_trans hmono (lintegral_transform_second ha hr₀ hmeas hint)) ?_
  refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    ((ae_restrict_mem measurableSet_Ioi).mono
      (fun s hs => div_nonneg (abs_nonneg _) (le_of_lt (lt_trans hr₀ hs))))]
  exact ENNReal.ofReal_lt_top

/-- `s ↦ s^{a-1}|h s|` is integrable on `(L, U]` for `r₀ ≤ L ≤ U`, given
logarithmic integrability of `h` on `(r₀,∞)`. -/
theorem integrableOn_rpow_mul_abs_Ioc {h : ℝ → ℝ} {a r₀ L U : ℝ} (ha : 0 < a)
    (hmeas : Measurable h) (hr₀ : 0 < r₀) (_hLU : L ≤ U) (hL : r₀ ≤ L)
    (hint : IntegrableOn (fun s => |h s| / s) (Ioi r₀) volume) :
    IntegrableOn (fun s => s ^ (a - 1) * |h s|) (Set.Ioc L U) volume := by
  have hbase : IntegrableOn (fun s => U ^ a * (|h s| / s)) (Set.Ioc L U) volume :=
    (hint.mono_set (fun x hx => lt_of_le_of_lt hL hx.1)).const_mul _
  refine hbase.mono' ?_ ?_
  · have hcont : ContinuousOn (fun s : ℝ => s ^ (a - 1)) (Set.Ioc L U) :=
      fun s hs => (Real.continuousAt_rpow_const s (a - 1)
        (Or.inl (ne_of_gt (lt_trans hr₀ (lt_of_le_of_lt hL hs.1))))).continuousWithinAt
    exact hcont.aestronglyMeasurable measurableSet_Ioc |>.mul
      hmeas.abs.aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have hs0 : 0 < s := lt_trans hr₀ (lt_of_le_of_lt hL hs.1)
    rw [Real.norm_eq_abs, abs_mul, abs_abs, abs_of_nonneg (Real.rpow_nonneg hs0.le _)]
    calc s ^ (a - 1) * |h s| = s ^ a * (|h s| / s) := by
          rw [show a - 1 = a + (-1) by ring, Real.rpow_add hs0, Real.rpow_neg_one]
          field_simp
      _ ≤ U ^ a * (|h s| / s) := by
          apply mul_le_mul_of_nonneg_right _ (div_nonneg (abs_nonneg _) hs0.le)
          exact Real.rpow_le_rpow hs0.le hs.2 ha.le

/-- **The second transform is an error function**: it tends to `0` at `∞`. -/
theorem tendsto_logTransformSecond {h : ℝ → ℝ} {a r₀ : ℝ} (ha : 0 < a) (hmeas : Measurable h)
    (h0 : Tendsto h atTop (𝓝 0)) (hr₀ : 0 < r₀)
    (hint : IntegrableOn (fun s => |h s| / s) (Ioi r₀) volume) :
    Tendsto (fun r : ℝ => r ^ (-a) * ∫ s in Set.Ioc r₀ r, s ^ (a - 1) * h s) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨R, hRr₀, hR⟩ : ∃ R : ℝ, r₀ ≤ R ∧ ∀ s : ℝ, R ≤ s → |h s| ≤ a * (ε / 4) := by
    obtain ⟨R₀, hR₀⟩ := Metric.tendsto_atTop.1 h0 (a * (ε / 4)) (by positivity)
    refine ⟨max R₀ r₀, le_max_right _ _, fun s hs => ?_⟩
    have h := hR₀ s (le_trans (le_max_left _ _) hs)
    rw [Real.dist_eq, sub_zero, abs_lt] at h
    exact abs_le.2 ⟨le_of_lt h.1, le_of_lt h.2⟩
  have hintR : IntegrableOn (fun s => s ^ (a - 1) * |h s|) (Set.Ioc r₀ R) volume :=
    integrableOn_rpow_mul_abs_Ioc ha hmeas hr₀ hRr₀ le_rfl hint
  set C : ℝ := ∫ s in Set.Ioc r₀ R, s ^ (a - 1) * |h s| with hCdef
  have hC0 : 0 ≤ C :=
    integral_nonneg_of_ae ((ae_restrict_mem measurableSet_Ioc).mono
      (fun s hs => mul_nonneg (Real.rpow_nonneg (lt_trans hr₀ hs.1).le _) (abs_nonneg _)))
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 (tendsto_rpow_neg_atTop ha)
    (ε / (4 * (C + 1))) (by positivity)
  refine ⟨max (max R N) (r₀ + 1), fun r hr => ?_⟩
  have hrR : R ≤ r := le_trans (le_max_left R N) (le_trans (le_max_left (max R N) (r₀+1)) hr)
  have hrN : N ≤ r := le_trans (le_max_right R N) (le_trans (le_max_left (max R N) (r₀+1)) hr)
  have hrr₀ : r₀ < r :=
    lt_of_lt_of_le (by linarith) (le_trans (le_max_right (max R N) (r₀+1)) hr)
  have hr0 : 0 < r := lt_trans hr₀ hrr₀
  -- the finite piece
  have htailInt : IntegrableOn (fun s => s ^ (a - 1) * |h s|) (Set.Ioc R r) volume :=
    integrableOn_rpow_mul_abs_Ioc ha hmeas hr₀ hrR hRr₀ hint
  have hsplit : ∫ s in Set.Ioc r₀ r, s ^ (a - 1) * |h s|
      = (∫ s in Set.Ioc r₀ R, s ^ (a - 1) * |h s|) + ∫ s in Set.Ioc R r, s ^ (a - 1) * |h s| := by
    have hdisj : Disjoint (Set.Ioc r₀ R) (Set.Ioc R r) :=
      disjoint_left.mpr (fun x hx hx' => by linarith [hx.2, hx'.1])
    have hunion := setIntegral_union hdisj measurableSet_Ioc hintR htailInt
      (f := fun s => s ^ (a - 1) * |h s|)
    rw [Set.Ioc_union_Ioc_eq_Ioc hRr₀ hrR] at hunion
    exact hunion
  have hpowInt : IntegrableOn (fun s : ℝ => s ^ (a - 1)) (Set.Ioc R r) volume := by
    have hcont : ContinuousOn (fun s : ℝ => s ^ (a - 1)) (Set.Icc R r) :=
      fun s hs => (Real.continuousAt_rpow_const s (a - 1)
        (Or.inl (ne_of_gt (lt_of_lt_of_le (lt_of_lt_of_le hr₀ hRr₀) hs.1)))).continuousWithinAt
    exact hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have htail : ∫ s in Set.Ioc R r, s ^ (a - 1) * |h s| ≤ ε / 4 * r ^ a := by
    have hmono : ∫ s in Set.Ioc R r, s ^ (a - 1) * |h s|
        ≤ ∫ s in Set.Ioc R r, (a * (ε / 4)) * s ^ (a - 1) :=
      setIntegral_mono_on htailInt (hpowInt.const_mul _)
        measurableSet_Ioc (fun s hs => by
          have hsa : |h s| ≤ a * (ε / 4) := hR s hs.1.le
          have hnn : 0 ≤ s ^ (a - 1) :=
            Real.rpow_nonneg (lt_trans (lt_of_lt_of_le hr₀ hRr₀) hs.1).le _
          nlinarith)
    rw [integral_const_mul] at hmono
    have hval : ∫ s in Set.Ioc R r, s ^ (a - 1) ≤ r ^ a / a := by
      rw [← intervalIntegral.integral_of_le hrR,
        integral_rpow (Or.inr ⟨by linarith, by
          rw [uIcc_of_le hrR]
          intro h
          linarith [h.1, hRr₀, hr₀]⟩)]
      have h1 : R ^ a ≥ 0 := Real.rpow_nonneg (le_trans hr₀.le hRr₀) a
      rw [show a - 1 + 1 = a by ring]
      have : (r ^ a - R ^ a) / a ≤ r ^ a / a := by
        apply div_le_div_of_nonneg_right _ ha.le
        linarith
      exact this
    calc ∫ s in Set.Ioc R r, s ^ (a - 1) * |h s|
        ≤ (a * (ε / 4)) * ∫ s in Set.Ioc R r, s ^ (a - 1) := hmono
      _ ≤ (a * (ε / 4)) * (r ^ a / a) := by
          apply mul_le_mul_of_nonneg_left hval (by positivity)
      _ = ε / 4 * r ^ a := by field_simp
  have hle : |r ^ (-a) * ∫ s in Set.Ioc r₀ r, s ^ (a - 1) * h s| ≤ ε / 2 := by
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hr0.le _)]
    have h1 : |∫ s in Set.Ioc r₀ r, s ^ (a - 1) * h s|
        ≤ ∫ s in Set.Ioc r₀ r, s ^ (a - 1) * |h s| := by
      refine le_trans abs_integral_le_integral_abs (le_of_eq ?_)
      refine setIntegral_congr_fun measurableSet_Ioc (fun s hs => ?_)
      rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (lt_trans hr₀ hs.1).le _)]
    have hCr : r ^ (-a) * C ≤ ε / 4 := by
      have hlt : r ^ (-a) < ε / (4 * (C + 1)) := by
        have h := hN r hrN
        rw [Real.dist_eq, sub_zero, abs_of_nonneg (Real.rpow_nonneg hr0.le _)] at h
        exact h
      have h1 : r ^ (-a) * C ≤ r ^ (-a) * (C + 1) := by
        apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hr0.le _)
        linarith
      have h2 : r ^ (-a) * (C + 1) ≤ ε / (4 * (C + 1)) * (C + 1) :=
        mul_le_mul_of_nonneg_right hlt.le (by linarith : (0:ℝ) ≤ C + 1)
      have h3 : ε / (4 * (C + 1)) * (C + 1) = ε / 4 := by
        field_simp
      linarith
    calc r ^ (-a) * |∫ s in Set.Ioc r₀ r, s ^ (a - 1) * h s|
        ≤ r ^ (-a) * ∫ s in Set.Ioc r₀ r, s ^ (a - 1) * |h s| :=
          mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hr0.le _)
      _ = r ^ (-a) * C + r ^ (-a) * ∫ s in Set.Ioc R r, s ^ (a - 1) * |h s| := by
          rw [hsplit]; ring
      _ ≤ ε / 4 + r ^ (-a) * (ε / 4 * r ^ a) := by
          apply add_le_add hCr
          exact mul_le_mul_of_nonneg_left htail (Real.rpow_nonneg hr0.le _)
      _ = ε / 2 := by
          rw [Real.rpow_neg hr0.le]
          field_simp
          ring
  rw [Real.dist_eq, sub_zero]
  linarith

/-! ### Lemma I.4.13 -/

/-- **Lemma I.4.13, first half.**  The transform `r ↦ r^a ∫_r^∞ s^{-a-1} h(s) ds`
of a logarithmically integrable error function is again a logarithmically
integrable error function. -/
theorem lemma_I_4_13_first {h : ℝ → ℝ} (hlog : IsLogErrorFunction h) {a : ℝ} (ha : 0 < a) :
    IsLogErrorFunction (fun r : ℝ => r ^ a * ∫ s in Ioi r, s ^ (-a - 1) * h s) := by
  obtain ⟨⟨⟨b, hb⟩, r₀, hr₀, hint⟩, h0⟩ := hlog
  obtain ⟨F, hF, hFeq⟩ := exists_measurable_eqOn_Ici hb
  set c := max r₀ b with hc
  have hc0 : 0 < c := lt_max_of_lt_left hr₀
  have hintF : IntegrableOn (fun s => |F s| / s) (Ioi c) volume := by
    refine (hint.mono_set (Ioi_subset_Ioi (le_max_left _ _))).congr_fun (fun s hs => ?_)
      measurableSet_Ioi
    simp only
    rw [hFeq s ((le_max_right _ _).trans (le_of_lt hs))]
  have hF0 : Tendsto F atTop (𝓝 0) :=
    h0.congr' (eventually_atTop.2 ⟨b, fun x hx => (hFeq x hx).symm⟩)
  have hTF : IsLogErrorFunction (fun r : ℝ => r ^ a * ∫ s in Ioi r, s ^ (-a - 1) * F s) :=
    ⟨⟨⟨0, measurable_restrict_Ici_of_measurable (measurable_logTransformFirst hF) 0⟩, c, hc0,
      integrableOn_logTransformFirst ha hc0 hF hintF⟩,
      tendsto_logTransformFirst ha hF hF0 hc0 hintF⟩
  refine hTF.mono ⟨b, ?_⟩ (eventually_atTop.2 ⟨b, fun r hr => ?_⟩)
  · have hfun : (Ici b).domRestrict (fun r : ℝ => r ^ a * ∫ s in Ioi r, s ^ (-a - 1) * h s)
        = (Ici b).domRestrict (fun r : ℝ => r ^ a * ∫ s in Ioi r, s ^ (-a - 1) * F s) := by
      funext r
      exact (logTransformFirst_eqOn_Ici hFeq r.2).symm
    rw [hfun]
    exact measurable_restrict_Ici_of_measurable (measurable_logTransformFirst hF) b
  · rw [logTransformFirst_eqOn_Ici hFeq hr]

/-- **Lemma I.4.13, second half.**  The transform `r ↦ r^{-a} ∫_{r₀}^r s^{a-1} h(s) ds`
(equivalently, up to the lower limit of integration, the paper's `r^{-a} ∫_1^r`)
of a logarithmically integrable error function is again a logarithmically
integrable error function. -/
theorem lemma_I_4_13_second {h : ℝ → ℝ} {a r₀ : ℝ} (ha : 0 < a) (hr₀ : 0 < r₀)
    (hmeas : Measurable h) (hint : IntegrableOn (fun s => |h s| / s) (Ioi r₀) volume)
    (h0 : Tendsto h atTop (𝓝 0)) :
    IsLogErrorFunction (fun r : ℝ => r ^ (-a) * ∫ s in Set.Ioc r₀ r, s ^ (a - 1) * h s) :=
  ⟨⟨⟨0, measurable_restrict_Ici_of_measurable (measurable_logTransformSecond hmeas) 0⟩, r₀, hr₀,
      integrableOn_logTransformSecond ha hr₀ hmeas hint⟩,
    tendsto_logTransformSecond ha hmeas h0 hr₀ hint⟩

/-! ### Closure properties of log-integrable error functions

These are the manipulations used once Lemma I.4.13 is applied (e.g. in the proof
of Proposition I.4.2, where the error term `H_r` is a fixed linear combination of
terms each covered by I.4.13). -/

/-- Eventual equality of a log-integrable error function with a function measurable on a
tail again gives a log-integrable error function. -/
theorem isLogErrorFunction_congr {f g : ℝ → ℝ} (hf : IsLogErrorFunction f)
    (hfg : f =ᶠ[atTop] g) (hg : ∃ a, Measurable ((Ici a).domRestrict g)) :
    IsLogErrorFunction g :=
  hf.mono hg (hfg.mono fun _ hr => by rw [hr])

/-- The sum of two log-integrable error functions. -/
theorem isLogErrorFunction_add {f g : ℝ → ℝ} (hf : IsLogErrorFunction f)
    (hg : IsLogErrorFunction g) : IsLogErrorFunction (fun r => f r + g r) := by
  obtain ⟨⟨⟨b₁, hb₁⟩, r₁, hr₁, hf1⟩, hf0⟩ := hf
  obtain ⟨⟨⟨b₂, hb₂⟩, r₂, hr₂, hg2⟩, hg0⟩ := hg
  obtain ⟨F, hF, hFeq⟩ := exists_measurable_eqOn_Ici hb₁
  obtain ⟨G, hG, hGeq⟩ := exists_measurable_eqOn_Ici hb₂
  set c := max (max r₁ r₂) (max b₁ b₂) with hc
  have hcr₁ : r₁ ≤ c := (le_max_left _ _).trans (le_max_left _ _)
  have hcr₂ : r₂ ≤ c := (le_max_right _ _).trans (le_max_left _ _)
  have hcb₁ : b₁ ≤ c := (le_max_left _ _).trans (le_max_right _ _)
  have hcb₂ : b₂ ≤ c := (le_max_right _ _).trans (le_max_right _ _)
  have hc0 : 0 < c := lt_of_lt_of_le hr₁ hcr₁
  have hsum : ∀ x, c ≤ x → F x + G x = f x + g x := fun x hx => by
    rw [hFeq x (hcb₁.trans hx), hGeq x (hcb₂.trans hx)]
  have hmeasc : Measurable ((Ici c).domRestrict (fun r => f r + g r)) := by
    have hfun : (Ici c).domRestrict (fun r => f r + g r)
        = (Ici c).domRestrict (fun r => F r + G r) := by
      funext r
      exact (hsum r r.2).symm
    rw [hfun]
    exact measurable_restrict_Ici_of_measurable (hF.add hG) c
  refine ⟨⟨⟨c, hmeasc⟩, c, hc0, ?_⟩, ?_⟩
  swap
  · simpa using hf0.add hg0
  have h1 : IntegrableOn (fun r => |f r| / r) (Ioi c) volume :=
    hf1.mono_set (Ioi_subset_Ioi hcr₁)
  have h2 : IntegrableOn (fun r => |g r| / r) (Ioi c) volume :=
    hg2.mono_set (Ioi_subset_Ioi hcr₂)
  have h3 : IntegrableOn (fun r => |f r| / r + |g r| / r) (Ioi c) volume :=
    h1.add h2
  refine h3.mono' ?_ ?_
  · refine ((((hF.add hG).abs).div measurable_id).aestronglyMeasurable).congr
      (ae_restrict_of_forall_mem measurableSet_Ioi fun r hr => ?_)
    change |F r + G r| / r = |f r + g r| / r
    rw [hsum r (le_of_lt hr)]
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    rw [mem_Ioi] at hr
    have hr0 : 0 < r := hc0.trans hr
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hr0, abs_abs, ← add_div]
    exact div_le_div_of_nonneg_right (abs_add_le _ _) hr0.le

/-- The constant multiples of `r^{-a}` (`a > 0`) are log-integrable error functions. -/
theorem isLogErrorFunction_const_rpow_neg {a r₀ c : ℝ} (ha : 0 < a) (hr₀ : 0 < r₀) :
    IsLogErrorFunction (fun r => c * r ^ (-a)) := by
  have hmeas : Measurable (fun r : ℝ => c * r ^ (-a)) := by fun_prop
  refine ⟨⟨⟨0, measurable_restrict_Ici_of_measurable hmeas 0⟩, r₀, hr₀, ?_⟩, ?_⟩
  · have hint : IntegrableOn (fun r : ℝ => r ^ (-a - 1)) (Ioi r₀) volume :=
      integrableOn_Ioi_rpow_of_lt (by linarith) hr₀
    refine (hint.const_mul (|c|)).mono' ?_ ?_
    · exact (hmeas.abs.div measurable_id).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      rw [mem_Ioi] at hr
      have hr0 : 0 < r := lt_trans hr₀ hr
      have hrew : |c * r ^ (-a)| / r = |c| * r ^ (-a - 1) := by
        rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hr0.le _),
          show -a - 1 = -a + (-1) by ring, Real.rpow_add hr0, Real.rpow_neg_one]
        field_simp
      rw [Real.norm_eq_abs, hrew, abs_of_nonneg (by positivity)]
  · have h1 : Tendsto (fun r : ℝ => r ^ (-a)) atTop (𝓝 0) := tendsto_rpow_neg_atTop ha
    simpa using h1.const_mul c

/-- **Lemma I.4.13, second half, in the paper's form**: the lower limit of
integration is `1`, i.e. the paper's `r ↦ r^{-a} ∫_1^r s^{a-1} h(s) ds`,
realised as the set integral over `(1, r]` (which agrees with the interval
integral `∫_1^r` for every `r ≥ 1`).  The extra hypothesis is logarithmic
integrability on the finite piece `(1, r₀]`, which is what makes the integral
from `1` well defined. -/
theorem lemma_I_4_13_second_from_one {h : ℝ → ℝ} {a r₀ : ℝ} (ha : 0 < a) (hr₀ : 1 ≤ r₀)
    (hmeas : Measurable h) (hint : IntegrableOn (fun s => |h s| / s) (Ioi r₀) volume)
    (h0 : Tendsto h atTop (𝓝 0))
    (hint1 : IntegrableOn (fun s => |h s| / s) (Set.Ioc (1 : ℝ) r₀) volume) :
    IsLogErrorFunction (fun r : ℝ => r ^ (-a) * ∫ s in Set.Ioc 1 r, s ^ (a - 1) * h s) := by
  have hsplit : IntegrableOn (fun s => |h s| / s) (Ioi (1:ℝ)) volume := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi hr₀]
    exact hint1.union hint
  exact lemma_I_4_13_second (r₀ := 1) ha one_pos hmeas hsplit h0

end PercLib.Analysis
