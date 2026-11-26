/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Karamata's integral theorem under Potter bounds, Lemma I.2.10 of T. Hutchcroft, *Critical long-range
percolation I*, arXiv:2508.18807v1, p. 26 (citing Feller, Theorem VIII.9.1).

Ported from the work of contributor `yujinhkim`: repository `yujinhkim/lrp`, branch
`critical-lrp-1`, commit `d382e4c28d92dd4e698ebf4f2aaf0bc932ae73fc`, files
`PercLib/CriticalLRP/Analysis/Karamata.lean` and `PercLib/CriticalLRP/Analysis/KaramataMain.lean`;
licence Apache-2.0 as declared in that commit's file headers and
`third_party/critical-lrp/NOTICE.md`; upstream `yujinhkim/Critical-Long-range-percolation` at
`3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf`. Modified: the two files are merged; the source's
definition `HasPotterBounds f α` is written out as the explicit hypothesis it abbreviates (Potter's
bounds, Bingham–Goldie–Teugels Theorem 1.5.6, are proved in
`PercLib/Analysis/RegularVariation/UniformConvergence.lean`); `RegularlyVaryingAtTop f α` becomes
`RegularlyVarying α f` of `PercLib/Analysis/RegularVariation/Defs.lean`; `import Mathlib`,
`autoImplicit` and disabled linters are removed.
-/
module

public import PercLib.Analysis.RegularVariation.Defs
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.Topology.Order.IsLocallyClosed

/-! # Karamata's integral theorem under Potter bounds

If `f` is measurable, locally integrable on `(0, ∞)`, eventually positive, regularly varying of
index `α > -1`, and satisfies Potter's bounds
`∀ ε > 0, ∃ X ≥ 1, ∀ x ≥ y ≥ X, (1-ε)(x/y)^(α-ε)|f y| ≤ |f x| ≤ (1+ε)(x/y)^(α+ε)|f y|`,
then `(∫_1^r f) / (r f r) → 1/(α+1)` (`lemma_I_2_10`).
-/

@[expose] public section

open Filter Set MeasureTheory
open scoped Topology

namespace PercLib.Analysis

theorem potter_upper {f : ℝ → ℝ} {α ε X : ℝ}
    (h : ∀ x y : ℝ, X ≤ y → y ≤ x →
      (1 - ε) * (x / y) ^ (α - ε) * |f y| ≤ |f x| ∧
        |f x| ≤ (1 + ε) * (x / y) ^ (α + ε) * |f y|)
    {x y : ℝ} (hy : X ≤ y) (hxy : y ≤ x) :
    |f x| ≤ (1 + ε) * (x / y) ^ (α + ε) * |f y| :=
  (h x y hy hxy).2

theorem potter_lower {f : ℝ → ℝ} {α ε X : ℝ}
    (h : ∀ x y : ℝ, X ≤ y → y ≤ x →
      (1 - ε) * (x / y) ^ (α - ε) * |f y| ≤ |f x| ∧
        |f x| ≤ (1 + ε) * (x / y) ^ (α + ε) * |f y|)
    {x y : ℝ} (hy : X ≤ y) (hxy : y ≤ x) :
    (1 - ε) * (x / y) ^ (α - ε) * |f y| ≤ |f x| :=
  (h x y hy hxy).1

/-- If `f` is eventually non-zero and satisfies Potter's bounds of index `α > -1`,
then `|f|` is at least a positive power of `r`, so `r f r → ∞`. -/
theorem tendsto_r_mul_of_potter {f : ℝ → ℝ} {α : ℝ} (hα : -1 < α)
    (hposf : ∀ᶠ x in atTop, 0 < f x)
    (hpot : (∀ ε : ℝ, 0 < ε → ∃ X : ℝ, 1 ≤ X ∧ ∀ x y : ℝ, X ≤ y → y ≤ x →
      (1 - ε) * (x / y) ^ (α - ε) * |f y| ≤ |f x| ∧
        |f x| ≤ (1 + ε) * (x / y) ^ (α + ε) * |f y|)) :
    Tendsto (fun r => r * f r) atTop atTop := by
  have hα4 : (0:ℝ) < (α + 1) / 4 := by linarith
  obtain ⟨η, hη0, hη1a, hη1b⟩ : ∃ η : ℝ, 0 < η ∧ η < 1 ∧ η < (α + 1) / 2 := by
    refine ⟨min (1/2) ((α + 1) / 4), lt_min (by norm_num) hα4, ?_, ?_⟩
    · exact lt_of_le_of_lt (min_le_left _ _) (by norm_num)
    · calc min (1/2) ((α + 1) / 4) ≤ (α + 1) / 4 := min_le_right _ _
        _ < (α + 1) / 2 := by linarith
  obtain ⟨X₀, hX₀1, hX₀⟩ := hpot η hη0
  obtain ⟨X₁, hX₁⟩ := eventually_atTop.1 hposf
  set X := max X₀ X₁ with hXdef
  have hX1 : 1 ≤ X := le_trans hX₀1 (le_max_left _ _)
  have hXX₀ : X₀ ≤ X := le_max_left _ _
  have hneX : 0 < f X := hX₁ X (le_max_right _ _)
  have hpos : 0 < |f X| := abs_pos.2 (ne_of_gt hneX)
  -- for `s ≥ X`, `|f s| ≥ c s^{α-η}`
  have hc : 0 < (1 - η) * X ^ (-(α - η)) * |f X| := by
    have h1 : 0 < 1 - η := by linarith
    have h2 : 0 < X ^ (-(α - η)) := Real.rpow_pos_of_pos (by linarith) _
    positivity
  have hbound : ∀ s : ℝ, X ≤ s →
      (1 - η) * X ^ (-(α - η)) * |f X| * s ^ (α - η) ≤ |f s| := by
    intro s hs
    have h1 := potter_lower hX₀ hXX₀ hs
    have h2 : (s / X) ^ (α - η) = s ^ (α - η) * X ^ (-(α - η)) := by
      rw [Real.div_rpow (by linarith) (by linarith), Real.rpow_neg (by linarith)]
      ring
    rw [h2] at h1
    calc (1 - η) * X ^ (-(α - η)) * |f X| * s ^ (α - η)
        = (1 - η) * (s ^ (α - η) * X ^ (-(α - η))) * |f X| := by ring
      _ ≤ |f s| := h1
  -- so `s |f s| ≥ c s^{1+α-η} → ∞`
  rw [tendsto_atTop_atTop]
  intro b
  have hexp : 0 < 1 + α - η := by linarith
  have h2 : Tendsto (fun s : ℝ => (1 - η) * X ^ (-(α - η)) * |f X| * s ^ (1 + α - η))
      atTop atTop := by
    have h3 : Tendsto (fun s : ℝ => s ^ (1 + α - η)) atTop atTop :=
      tendsto_rpow_atTop hexp
    exact h3.const_mul_atTop hc
  obtain ⟨R, hR⟩ := (tendsto_atTop_atTop.1 h2) (max b 1)
  refine ⟨max R X, fun r hr => ?_⟩
  have hrR : R ≤ r := le_trans (le_max_left _ _) hr
  have hrX : X ≤ r := le_trans (le_max_right _ _) hr
  have hr1 : 1 ≤ r := le_trans hX1 hrX
  have h4 := hR r hrR
  have h5 : (1 - η) * X ^ (-(α - η)) * |f X| * r ^ (1 + α - η)
      = r * ((1 - η) * X ^ (-(α - η)) * |f X| * r ^ (α - η)) := by
    rw [show 1 + α - η = α - η + 1 by ring,
      Real.rpow_add (by linarith : (0:ℝ) < r) (α - η) 1, Real.rpow_one]
    ring
  rw [h5] at h4
  have h6 := hbound r hrX
  have hr0 : 0 < r := by linarith
  have h7 : r * ((1 - η) * X ^ (-(α - η)) * |f X| * r ^ (α - η)) ≤ r * |f r| := by
    have hnn : 0 ≤ (1 - η) * X ^ (-(α - η)) * |f X| * r ^ (α - η) := by
      have : 0 ≤ r ^ (α - η) := Real.rpow_nonneg hr0.le _
      have : 0 < 1 - η := by linarith
      positivity
    exact mul_le_mul_of_nonneg_left h6 hr0.le
  have hfrpos : 0 < f r := hX₁ r (le_trans (le_max_right _ _) hrX)
  have h8 : r * |f r| ≤ r * f r := by
    rw [abs_of_pos hfrpos]
  have : b ≤ r * |f r| := le_trans (le_max_left b 1) (le_trans h4 h7)
  linarith [h8]

/-- **Upper block.** For `0 < δ < 1`, the integral over `[δr, r]` satisfies
`(∫_{δr}^r f)/(r f(r)) → (1-δ^{α+1})/(α+1)`. -/
theorem tendsto_upper_block {f : ℝ → ℝ} {α η X δ : ℝ}
    (hη0 : 0 < η) (hη1 : η < 1 / 2) (hαη : -1 < α - η) (hXpos : 0 < X)
    (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hpotX : ∀ x y : ℝ, X ≤ y → y ≤ x →
      (1 - η) * (x / y) ^ (α - η) * |f y| ≤ |f x| ∧
        |f x| ≤ (1 + η) * (x / y) ^ (α + η) * |f y|)
    (hmeas : Measurable f)
    (hfpos : ∀ s : ℝ, X ≤ s → 0 < f s)
    (hrv : ∀ l : ℝ, 0 < l → Tendsto (fun x => f (l * x) / f x) atTop (𝓝 (l ^ α))) :
    Tendsto (fun r => ∫ u in δ..1, f (r * u) / f r) atTop
      (𝓝 ((1 - δ ^ (α + 1)) / (α + 1))) := by
  have hmain : Tendsto (fun r : ℝ => ∫ u in δ..1, f (r * u) / f r) atTop
      (𝓝 (∫ u in δ..1, u ^ α)) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (bound := fun u => 2 * u ^ (α - η)) ?_ ?_ ?_ ?_
    · filter_upwards with r
      exact ((hmeas.comp (measurable_const.mul measurable_id)).div_const _).aestronglyMeasurable
    · filter_upwards [eventually_ge_atTop (X / δ)] with r hr
      filter_upwards with u hu
      rw [uIoc_of_le hδ1.le] at hu
      have hr0 : 0 < r := lt_of_lt_of_le (div_pos hXpos hδ0) hr
      have hu0 : 0 < u := lt_trans hδ0 hu.1
      have hrueq : r * u ≤ r := by nlinarith [hu.2]
      have hruX : X ≤ r * u := by
        have h1 : X ≤ r * δ := by
          rw [div_le_iff₀ hδ0] at hr
          linarith
        nlinarith [hu.1.le]
      have hlow := potter_lower hpotX hruX hrueq
      have hratio : (r / (r * u)) ^ (α - η) = u ^ (-(α - η)) := by
        have h1 : r / (r * u) = u⁻¹ := by field_simp
        rw [h1, Real.inv_rpow hu0.le, ← Real.rpow_neg hu0.le]
      rw [hratio, Real.rpow_neg hu0.le] at hlow
      have h3 : 0 < u ^ (α - η) := Real.rpow_pos_of_pos hu0 _
      have hlow' : (1 - η) * |f (r * u)| / u ^ (α - η) ≤ |f r| := by
        calc (1 - η) * |f (r * u)| / u ^ (α - η)
            = (1 - η) * (u ^ (α - η))⁻¹ * |f (r * u)| := by ring
          _ ≤ |f r| := hlow
      have hfr : 0 < f r := hfpos r (le_trans hruX hrueq)
      have h1 : |f (r * u)| ≤ |f r| * u ^ (α - η) / (1 - η) := by
        have hA : (1 - η) * |f (r * u)| ≤ |f r| * u ^ (α - η) := by
          rw [div_le_iff₀ h3] at hlow'
          linarith
        rw [le_div_iff₀ (by linarith : 0 < 1 - η)]
        linarith
      rw [Real.norm_eq_abs, abs_div, abs_of_pos hfr, div_le_iff₀ hfr]
      calc |f (r * u)| ≤ |f r| * u ^ (α - η) / (1 - η) := h1
        _ ≤ (2 * u ^ (α - η)) * f r := by
            rw [abs_of_pos hfr, div_le_iff₀ (by linarith : 0 < 1 - η)]
            have h4 : 0 ≤ u ^ (α - η) := Real.rpow_nonneg hu0.le _
            nlinarith [mul_nonneg h4 hfr.le]
    · have hcont : ContinuousOn (fun u : ℝ => 2 * u ^ (α - η)) (uIcc δ 1) := by
        intro u hu
        have hu0 : u ≠ 0 := ne_of_gt (lt_of_lt_of_le hδ0
            (by rw [uIcc_of_le hδ1.le] at hu; exact hu.1))
        exact ((Real.continuousAt_rpow_const u (α - η) (Or.inl hu0)).const_mul 2).continuousWithinAt
      exact hcont.intervalIntegrable
    · filter_upwards with u hu
      rw [uIoc_of_le hδ1.le] at hu
      have := hrv u (lt_trans hδ0 hu.1)
      simpa [mul_comm] using this
  have hval : ∫ u in δ..1, u ^ α = (1 - δ ^ (α + 1)) / (α + 1) := by
    have hzero : (0:ℝ) ∉ uIcc δ 1 := by
      rw [uIcc_of_le hδ1.le]
      exact fun h => (not_le.2 hδ0) h.1
    rw [integral_rpow (Or.inr ⟨by intro h; linarith, hzero⟩), Real.one_rpow]
  rw [hval] at hmain
  exact hmain


/-
**Status of Lemma I.2.10.** The two halves of the classical proof are proved above:

* `tendsto_upper_block` : for fixed `0 < δ < 1`,
  `∫_δ^1 f(r u) du / f(r) → (1-δ^{α+1})/(α+1)` (dominated convergence plus Potter);
* `lower_block_bound` : `∫_X^{δr} |f| ≤ 2δ^{α+1-η}/(α+1-η) · r f(r)` eventually
  (Potter's bound converted into a pointwise estimate and integrated with `∫_X^{δr} s^{α-η} ds`);
* `tendsto_r_mul_of_potter` : `r f(r) → ∞`.

What is *not* yet formalized is only the final ε-bookkeeping: splitting
`∫_1^r = ∫_1^{δr} + ∫_{δr}^r`, using `∫_{δr}^r f = r ∫_δ^1 f(ru) du`, and
letting first `r → ∞` and then `δ → 0`.  No mathematical ingredient is missing;
it is the (tedious) assembly of the three proven blocks.
-/
/-- **Lower block.** If `f` is locally integrable on `(0,∞)` then
`∫_X^{δr} |f| ≤ 2δ^{α+1-η}/(α+1-η) · r f(r)` eventually. -/
theorem lower_block_bound {f : ℝ → ℝ} {α η X δ : ℝ}
    (hη0 : 0 < η) (hη12 : η < 1 / 2) (hαη : -1 < α - η) (hXpos : 0 < X)
    (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hloc : LocallyIntegrableOn f (Ioi 0))
    (hpotX : ∀ x y : ℝ, X ≤ y → y ≤ x →
      (1 - η) * (x / y) ^ (α - η) * |f y| ≤ |f x| ∧
        |f x| ≤ (1 + η) * (x / y) ^ (α + η) * |f y|)
    (hfpos : ∀ s : ℝ, X ≤ s → 0 < f s) :
    ∀ᶠ r in atTop, ∫ s in X..δ * r, |f s|
      ≤ (2 * δ ^ (α + 1 - η) / (α + 1 - η)) * (r * f r) := by
  filter_upwards [eventually_ge_atTop (X / δ), eventually_gt_atTop (0:ℝ)] with r hr hr0
  have hXδr : X ≤ δ * r := by
    rw [div_le_iff₀ hδ0] at hr
    linarith
  have hδr0 : 0 < δ * r := by positivity
  have hδr_le : δ * r ≤ r := by nlinarith
  have hXr : X ≤ r := le_trans hXδr hδr_le
  have hfr : 0 < f r := hfpos r hXr
  -- integrability of `|f|` on `[X, δr]`
  have hIntf : IntervalIntegrable (fun s => |f s|) volume X (δ * r) := by
    have h1 : IntegrableOn (fun s => |f s|) (Icc X (δ * r)) volume := by
      have h2 : IntegrableOn f (Icc X (δ * r)) volume :=
        (locallyIntegrableOn_iff (isLocallyClosed_Ioi) |>.1 hloc) (Icc X (δ*r))
          (fun x hx => lt_of_lt_of_le hXpos hx.1) isCompact_Icc
      exact h2.abs
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le hXδr (by simp)).2 h1
  -- integrability of the comparison function
  have hIntg : IntervalIntegrable
      (fun s : ℝ => 2 * |f r| * r ^ (-(α - η)) * s ^ (α - η)) volume X (δ * r) := by
    have hcont : ContinuousOn (fun s : ℝ => s ^ (α - η)) (uIcc X (δ * r)) := by
      intro s hs
      rw [uIcc_of_le hXδr] at hs
      exact (Real.continuousAt_rpow_const s (α - η)
        (Or.inl (ne_of_gt (lt_of_lt_of_le hXpos hs.1)))).continuousWithinAt
    have h2 : ContinuousOn (fun s : ℝ => 2 * |f r| * r ^ (-(α - η)) * s ^ (α - η))
        (uIcc X (δ * r)) := by
      have h3 := hcont.const_mul (2 * |f r| * r ^ (-(α - η)))
      simpa [mul_assoc] using h3
    exact h2.intervalIntegrable
  -- pointwise comparison
  have hpt : ∀ s ∈ Icc X (δ * r),
      |f s| ≤ 2 * |f r| * r ^ (-(α - η)) * s ^ (α - η) := by
    intro s hs
    have hs0 : 0 < s := lt_of_lt_of_le hXpos hs.1
    have hlow := potter_lower hpotX (x := r) (y := s) hs.1 (le_trans hs.2 hδr_le)
    have hratio : (r / s) ^ (α - η) = r ^ (α - η) * (s ^ (α - η))⁻¹ := by
      rw [Real.div_rpow (le_of_lt hr0) hs0.le, div_eq_mul_inv]
    rw [hratio] at hlow
    have hpos1 : 0 < 1 - η := by linarith
    have h3 : 0 < r ^ (α - η) := Real.rpow_pos_of_pos hr0 _
    have h4 : 0 < s ^ (α - η) := Real.rpow_pos_of_pos hs0 _
    -- multiply `hlow` by `s^{α-η}`
    have h5 : (1 - η) * r ^ (α - η) * |f s| ≤ |f r| * s ^ (α - η) := by
      have h6 := mul_le_mul_of_nonneg_right hlow h4.le
      have h7 : (1 - η) * (r ^ (α - η) * (s ^ (α - η))⁻¹) * |f s| * s ^ (α - η)
          = (1 - η) * r ^ (α - η) * |f s| := by
        field_simp
      linarith [h6, h7 ▸ h6]
    -- divide by `(1-η) r^{α-η}`
    have h8 : |f s| ≤ |f r| * s ^ (α - η) / ((1 - η) * r ^ (α - η)) := by
      rw [le_div_iff₀ (by positivity : 0 < (1 - η) * r ^ (α - η))]
      linarith
    have h9 : |f r| * s ^ (α - η) / ((1 - η) * r ^ (α - η))
        = ((1 - η)⁻¹ * |f r| * r ^ (-(α - η))) * s ^ (α - η) := by
      rw [Real.rpow_neg (le_of_lt hr0)]
      field_simp
    have h10 : (1 - η)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith : (0:ℝ) < 1 - η) (by norm_num : (0:ℝ) < 2)]
      linarith
    have hnn : 0 ≤ |f r| * r ^ (-(α - η)) * s ^ (α - η) := by positivity
    calc |f s| ≤ ((1 - η)⁻¹ * |f r| * r ^ (-(α - η))) * s ^ (α - η) := by rw [← h9]; exact h8
      _ ≤ 2 * |f r| * r ^ (-(α - η)) * s ^ (α - η) := by
          nlinarith [h10, hnn]
  have hmono := intervalIntegral.integral_mono_on hXδr hIntf hIntg hpt
  -- evaluate the comparison integral
  have hzero : (0:ℝ) ∉ uIcc X (δ * r) := by
    rw [uIcc_of_le hXδr]
    exact fun h => (not_le.2 hXpos) h.1
  have hInt : ∫ s in X..δ * r, s ^ (α - η) = ((δ * r) ^ (α - η + 1) - X ^ (α - η + 1)) /
      (α - η + 1) := by
    rw [integral_rpow (Or.inr ⟨by intro h; linarith, hzero⟩)]
  have hInt_le : ∫ s in X..δ * r, s ^ (α - η) ≤ (δ * r) ^ (α - η + 1) / (α - η + 1) := by
    rw [hInt]
    have hXpow : 0 ≤ X ^ (α - η + 1) := Real.rpow_nonneg hXpos.le _
    have hden : 0 < α - η + 1 := by linarith
    have hle : ((δ * r) ^ (α - η + 1) - X ^ (α - η + 1)) ≤ (δ * r) ^ (α - η + 1) := by
      linarith
    exact div_le_div_of_nonneg_right hle hden.le
  have hIntg_val : ∫ s in X..δ * r, 2 * |f r| * r ^ (-(α - η)) * s ^ (α - η)
      = 2 * |f r| * r ^ (-(α - η)) * ∫ s in X..δ * r, s ^ (α - η) := by
    rw [intervalIntegral.integral_const_mul]
  calc ∫ s in X..δ * r, |f s|
      ≤ 2 * |f r| * r ^ (-(α - η)) * ∫ s in X..δ * r, s ^ (α - η) := by
        rw [← hIntg_val]; exact hmono
    _ ≤ 2 * |f r| * r ^ (-(α - η)) * ((δ * r) ^ (α - η + 1) / (α - η + 1)) := by
        have hnn : 0 ≤ 2 * |f r| * r ^ (-(α - η)) := by positivity
        exact mul_le_mul_of_nonneg_left hInt_le hnn
    _ = (2 * δ ^ (α + 1 - η) / (α + 1 - η)) * (r * f r) := by
        rw [abs_of_pos hfr, Real.rpow_neg (le_of_lt hr0), Real.mul_rpow (le_of_lt hδ0) hr0.le]
        rw [show α - η + 1 = α + 1 - η by ring,
          show α + 1 - η = (α - η) + 1 by ring,
          Real.rpow_add hr0 (α - η) 1, Real.rpow_one]
        field_simp



/-- **Lemma I.2.10 (Karamata's integral theorem; Feller VIII.9.1).**
If `f` is measurable, locally integrable on `(0,∞)`, eventually positive, regularly
varying of index `α > -1`, and satisfies Potter's bounds, then
`∫_1^r f ∼ r f(r)/(α+1)`. -/
theorem lemma_I_2_10 {f : ℝ → ℝ} {α : ℝ} (hα : -1 < α)
    (hmeas : Measurable f) (hloc : LocallyIntegrableOn f (Ioi 0))
    (hposf : ∀ᶠ x in atTop, 0 < f x)
    (hrv : RegularlyVarying α f)
    (hpot : (∀ ε : ℝ, 0 < ε → ∃ X : ℝ, 1 ≤ X ∧ ∀ x y : ℝ, X ≤ y → y ≤ x →
      (1 - ε) * (x / y) ^ (α - ε) * |f y| ≤ |f x| ∧
        |f x| ≤ (1 + ε) * (x / y) ^ (α + ε) * |f y|)) :
    Tendsto (fun r => (∫ s in 1..r, f s) / (r * f r)) atTop (𝓝 (1 / (α + 1))) := by
  classical
  have hα4 : (0:ℝ) < (α + 1) / 4 := by linarith
  obtain ⟨η, hη0, hη12, hη2⟩ : ∃ η : ℝ, 0 < η ∧ η < 1/2 ∧ η < (α + 1) / 2 := by
    refine ⟨min (1/4) ((α + 1) / 4), ?_, ?_, ?_⟩
    · exact lt_min (by norm_num) hα4
    · exact lt_of_le_of_lt (min_le_left _ _) (by norm_num)
    · calc min (1/4) ((α + 1) / 4) ≤ (α + 1) / 4 := min_le_right _ _
        _ < (α + 1) / 2 := by linarith
  have hαη : -1 < α - η := by linarith
  obtain ⟨X₀, hX₀1, hX₀⟩ := hpot η hη0
  obtain ⟨X₁, hX₁⟩ := eventually_atTop.1 hposf
  set X : ℝ := max X₀ X₁ with hXdef
  have hX1 : 1 ≤ X := le_trans hX₀1 (le_max_left _ _)
  have hXpos : 0 < X := lt_of_lt_of_le one_pos hX1
  have hpotX : ∀ x y : ℝ, X ≤ y → y ≤ x →
      (1 - η) * (x / y) ^ (α - η) * |f y| ≤ |f x| ∧
        |f x| ≤ (1 + η) * (x / y) ^ (α + η) * |f y| :=
    fun x y hy hxy => hX₀ x y (le_trans (le_max_left _ _) hy) hxy
  have hfpos : ∀ s : ℝ, X ≤ s → 0 < f s :=
    fun s hs => hX₁ s (le_trans (le_max_right _ _) hs)
  have hrv' : ∀ l : ℝ, 0 < l → Tendsto (fun x => f (l * x) / f x) atTop (𝓝 (l ^ α)) := hrv.2.2
  have hbig : Tendsto (fun r => r * f r) atTop atTop := tendsto_r_mul_of_potter hα hposf hpot
  -- interval integrability on every `[p,q] ⊂ (0,∞)`
  have hIntf : ∀ p q : ℝ, 0 < p → p ≤ q → IntervalIntegrable f volume p q := by
    intro p q hp hpq
    have h1 : IntegrableOn f (Icc p q) volume :=
      (locallyIntegrableOn_iff (isLocallyClosed_Ioi) |>.1 hloc) (Icc p q)
        (fun x hx => lt_of_lt_of_le hp hx.1) isCompact_Icc
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le hpq (by simp)).2 h1
  -- limits at `δ → 0`
  have hpow0 : ∀ s : ℝ, 0 < s → Tendsto (fun δ : ℝ => δ ^ s) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    intro s hs
    have h1 : Tendsto (fun δ : ℝ => δ ^ (-s)) (𝓝[>] (0:ℝ)) atTop :=
      tendsto_rpow_neg_nhdsGT_zero (by linarith)
    have h2 : Tendsto (fun δ : ℝ => (δ ^ (-s))⁻¹) (𝓝[>] (0:ℝ)) (𝓝 0) := h1.inv_tendsto_atTop
    exact h2.congr' (by
      filter_upwards [self_mem_nhdsWithin] with δ hδ
      rw [Real.rpow_neg (le_of_lt hδ), inv_inv])
  have hlimA : Tendsto (fun δ : ℝ => 2 * δ ^ (α + 1 - η) / (α + 1 - η)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have h1 := hpow0 (α + 1 - η) (by linarith)
    simpa using (h1.const_mul 2).div_const (α + 1 - η)
  have hlimB : Tendsto (fun δ : ℝ => δ ^ (α + 1) / (α + 1)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have h1 := hpow0 (α + 1) (by linarith)
    simpa using h1.div_const (α + 1)
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- choose `δ` with both budgets
  obtain ⟨δ, hδ0, hδ1, hδA, hδB⟩ : ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
      2 * δ ^ (α + 1 - η) / (α + 1 - η) < ε / 8 ∧ δ ^ (α + 1) / (α + 1) < ε / 8 := by
    obtain ⟨δA, hδApos, hδA⟩ := Metric.tendsto_nhdsWithin_nhds.1 hlimA (ε/8) (by linarith)
    obtain ⟨δB, hδBpos, hδB⟩ := Metric.tendsto_nhdsWithin_nhds.1 hlimB (ε/8) (by linarith)
    refine ⟨min (min (δA/2) (δB/2)) (1/2), lt_min (lt_min (by linarith) (by linarith))
        (by norm_num),
      lt_of_le_of_lt (min_le_right _ _) (by norm_num), ?_, ?_⟩
    · have hpos : 0 < min (min (δA/2) (δB/2)) (1/2) :=
        lt_min (lt_min (by linarith) (by linarith)) (by norm_num)
      have hlt : min (min (δA/2) (δB/2)) (1/2) < δA := by
        have h2 : min (min (δA/2) (δB/2)) (1/2) ≤ δA/2 :=
          le_trans (min_le_left _ _) (min_le_left _ _)
        linarith
      have h2 := hδA hpos (by rw [Real.dist_eq, sub_zero, abs_of_pos hpos]; exact hlt)
      rw [Real.dist_eq, sub_zero] at h2
      have h3 : 0 ≤ 2 * (min (min (δA/2) (δB/2)) (1/2)) ^ (α + 1 - η) / (α + 1 - η) := by
        have h4 : 0 < α + 1 - η := by linarith
        positivity
      rwa [abs_of_nonneg h3] at h2
    · have hpos : 0 < min (min (δA/2) (δB/2)) (1/2) :=
        lt_min (lt_min (by linarith) (by linarith)) (by norm_num)
      have hlt : min (min (δA/2) (δB/2)) (1/2) < δB := by
        have h2 : min (min (δA/2) (δB/2)) (1/2) ≤ δB/2 :=
          le_trans (min_le_left _ _) (min_le_right _ _)
        linarith
      have h2 := hδB hpos (by rw [Real.dist_eq, sub_zero, abs_of_pos hpos]; exact hlt)
      rw [Real.dist_eq, sub_zero] at h2
      have h3 : 0 ≤ (min (min (δA/2) (δB/2)) (1/2)) ^ (α + 1) / (α + 1) := by
        have h4 : 0 < α + 1 := by linarith
        positivity
      rwa [abs_of_nonneg h3] at h2
  -- the two blocks
  have hupper := tendsto_upper_block (f := f) hη0 hη12 hαη hXpos hδ0 hδ1 hpotX hmeas hfpos hrv'
  have hlowb := lower_block_bound (f := f) hη0 hη12 hαη hXpos hδ0 hδ1 hloc hpotX hfpos
  -- `|∫_1^X f| / (r f r) → 0`
  have hC₀ : ∀ᶠ r in atTop, |∫ s in 1..X, f s| / (r * f r) < ε / 8 := by
    have h1 : Tendsto (fun r : ℝ => |∫ s in 1..X, f s| / (r * f r)) atTop (𝓝 0) := by
      have h2 : Tendsto (fun r : ℝ => (r * f r)⁻¹) atTop (𝓝 0) := hbig.inv_tendsto_atTop
      have h3 : Tendsto (fun r : ℝ => |∫ s in 1..X, f s| * (r * f r)⁻¹) atTop (𝓝 0) := by
        simpa using h2.const_mul (|∫ s in 1..X, f s|)
      exact h3.congr' (by filter_upwards with r; rw [div_eq_mul_inv])
    obtain ⟨R, hR⟩ := Metric.tendsto_atTop.1 h1 (ε/8) (by linarith)
    filter_upwards [eventually_ge_atTop R, eventually_ge_atTop X, eventually_gt_atTop (0:ℝ)]
      with r hr hrX hr0
    have h5 := hR r hr
    rw [Real.dist_eq, sub_zero] at h5
    rwa [abs_of_nonneg (by have hfr : 0 < f r := hfpos r hrX; positivity :
      (0:ℝ) ≤ |∫ s in 1..X, f s| / (r * f r))] at h5
  -- the lower block
  have hlow' : ∀ᶠ r in atTop, |(∫ s in 1..δ * r, f s) / (r * f r)| < ε / 4 := by
    filter_upwards [hC₀, hlowb, eventually_ge_atTop X, eventually_gt_atTop (0:ℝ),
      eventually_ge_atTop (X / δ)] with r hC hlowr hrX hr0 hrδ
    have hXδr : X ≤ δ * r := by
      rw [div_le_iff₀ hδ0] at hrδ
      linarith
    have hfr : 0 < f r := hfpos r hrX
    have hrfr : 0 < r * f r := by positivity
    have hsplit2 : ∫ s in 1..δ * r, f s = (∫ s in 1..X, f s) + (∫ s in X..δ * r, f s) := by
      simpa using (intervalIntegral.integral_add_adjacent_intervals
        (hIntf 1 X one_pos hX1) (hIntf X (δ * r) hXpos hXδr)).symm
    have habs : |∫ s in 1..δ * r, f s| ≤ |∫ s in 1..X, f s| + ∫ s in X..δ * r, |f s| := by
      rw [hsplit2]
      calc |(∫ s in 1..X, f s) + (∫ s in X..δ * r, f s)|
          ≤ |∫ s in 1..X, f s| + |∫ s in X..δ * r, f s| :=
              abs_add_le (∫ s in 1..X, f s) (∫ s in X..δ * r, f s)
        _ ≤ |∫ s in 1..X, f s| + ∫ s in X..δ * r, |f s| := by
            have h3 : |∫ s in X..δ * r, f s| ≤ ∫ s in X..δ * r, |f s| :=
              intervalIntegral.abs_integral_le_integral_abs hXδr
            linarith
    have h1 : |(∫ s in 1..δ * r, f s) / (r * f r)|
        = |∫ s in 1..δ * r, f s| / (r * f r) := by
      rw [abs_div, abs_of_pos hrfr]
    rw [h1]
    have h4 : (∫ s in X..δ * r, |f s|) / (r * f r) ≤ 2 * δ ^ (α + 1 - η) / (α + 1 - η) := by
      rw [div_le_iff₀ hrfr]
      linarith
    have h5 : |∫ s in 1..δ * r, f s| / (r * f r)
        ≤ (|∫ s in 1..X, f s| + ∫ s in X..δ * r, |f s|) / (r * f r) := by
      gcongr
    have h6 : (|∫ s in 1..X, f s| + ∫ s in X..δ * r, |f s|) / (r * f r)
        = |∫ s in 1..X, f s| / (r * f r) + (∫ s in X..δ * r, |f s|) / (r * f r) := by
      field_simp
    linarith
  -- assemble
  have hupper' : ∀ᶠ r in atTop,
      |(∫ u in δ..1, f (r * u) / f r) - (1 - δ ^ (α + 1)) / (α + 1)| < ε / 4 := by
    obtain ⟨R, hR⟩ := Metric.tendsto_atTop.1 hupper (ε/4) (by linarith)
    filter_upwards [eventually_ge_atTop R] with r hr
    have h5 := hR r hr
    rwa [Real.dist_eq] at h5
  have hfinal : ∀ᶠ r in atTop,
      |(∫ s in 1..r, f s) / (r * f r) - 1 / (α + 1)| < ε := by
    filter_upwards [hlow', hupper', eventually_ge_atTop (max X (1/δ)),
      eventually_ge_atTop (X/δ), eventually_gt_atTop (0:ℝ)] with r hlow hup hr hrδ hr0
    -- decomposition at this `r`
    have hXr : X ≤ r := le_trans (le_max_left _ _) hr
    have hinv : 1/δ ≤ r := le_trans (le_max_right _ _) hr
    have hδr0 : 0 < δ * r := by positivity
    have hδr1 : (1:ℝ) ≤ δ * r := by
      rw [div_le_iff₀ hδ0] at hinv
      linarith
    have hδrX : X ≤ δ * r := by
      rw [div_le_iff₀ hδ0] at hrδ
      linarith
    have hfr : 0 < f r := hfpos r hXr
    have hrfr : 0 < r * f r := by positivity
    have hsplit : ∫ s in 1..r, f s = (∫ s in 1..δ * r, f s) + (∫ s in δ * r..r, f s) :=
      (intervalIntegral.integral_add_adjacent_intervals
        (hIntf 1 (δ * r) one_pos hδr1) (hIntf (δ * r) r hδr0 (by nlinarith))).symm
    have hsub : (∫ s in δ * r..r, f s) / (r * f r) = ∫ u in δ..1, f (r * u) / f r := by
      have h := intervalIntegral.integral_comp_mul_left (a := δ) (b := 1) (c := r) f (ne_of_gt hr0)
      rw [smul_eq_mul] at h
      rw [show r * δ = δ * r by ring, show r * 1 = r by ring] at h
      rw [show (∫ u in δ..1, f (r * u) / f r) = (∫ u in δ..1, f (r * u)) / f r from
        intervalIntegral.integral_div (f r) (fun u => f (r * u)), h]
      field_simp
    have hdec : (∫ s in 1..r, f s) / (r * f r)
        = (∫ s in 1..δ * r, f s) / (r * f r) + ∫ u in δ..1, f (r * u) / f r := by
      rw [hsplit, add_div, hsub]
    rw [hdec]
    set A := (∫ s in 1..δ * r, f s) / (r * f r) with hAdef
    set B := ∫ u in δ..1, f (r * u) / f r with hBdef
    set d := (1 - δ ^ (α + 1)) / (α + 1) with hddef
    set c := 1 / (α + 1) with hcdef
    have hkey : A + B - c = A + (B - d) + (d - c) := by ring
    have h2 : |A + (B - d) + (d - c)| ≤ |A| + |B - d| + |d - c| := by
      calc |A + (B - d) + (d - c)| ≤ |A + (B - d)| + |d - c| := abs_add_le _ _
        _ ≤ (|A| + |B - d|) + |d - c| := by
            have h4 := abs_add_le A (B - d)
            linarith
    have hdc : |d - c| = δ ^ (α + 1) / (α + 1) := by
      rw [hddef, hcdef, div_sub_div_same,
        show (1 - δ ^ (α + 1)) - 1 = -δ ^ (α + 1) by ring,
        show -δ ^ (α + 1) / (α + 1) = -(δ ^ (α + 1) / (α + 1)) from neg_div _ _,
        abs_neg, abs_of_nonneg (div_nonneg (by positivity) (by linarith : (0:ℝ) ≤ α + 1))]
    have hdlt : |d - c| < ε / 8 := by rw [hdc]; exact hδB
    rw [hkey]
    have hAl : |A| < ε / 4 := by rw [hAdef]; exact hlow
    have hBl : |B - d| < ε / 4 := by rw [hBdef, hddef]; exact hup
    calc |A + (B - d) + (d - c)| ≤ |A| + |B - d| + |d - c| := h2
      _ < ε := by linarith
  obtain ⟨N, hN⟩ := eventually_atTop.1 hfinal
  exact ⟨N, fun n hn => by
    rw [Real.dist_eq]
    exact hN n hn⟩

/-! ### Witness: the constant function `1` (index `0`) -/

example : Tendsto (fun r => (∫ s in (1 : ℝ)..r, (fun _ : ℝ => (1 : ℝ)) s) / (r * 1)) atTop
    (𝓝 (1 / (0 + 1))) :=
  lemma_I_2_10 (f := fun _ => 1) (α := 0) (by norm_num) measurable_const
    (locallyIntegrableOn_const _) (Eventually.of_forall fun _ => one_pos)
    ((slowlyVarying_iff_regularlyVarying_zero).1 (slowlyVarying_const one_pos))
    (fun ε hε => ⟨1, le_rfl, fun x y hy hxy => by
      have hy0 : 0 < y := lt_of_lt_of_le one_pos hy
      have hxy1 : 1 ≤ x / y := (one_le_div hy0).2 hxy
      simp only [abs_one, mul_one, zero_sub, zero_add]
      constructor
      · calc (1 - ε) * (x / y) ^ (-ε) ≤ 1 * 1 := by
              gcongr
              · linarith
              · exact Real.rpow_le_one_of_one_le_of_nonpos hxy1 (by linarith)
          _ = 1 := one_mul 1
      · calc (1 : ℝ) = 1 * 1 := (one_mul 1).symm
          _ ≤ (1 + ε) * (x / y) ^ ε := by
              gcongr
              · linarith
              · exact Real.one_le_rpow hxy1 hε.le⟩)

end PercLib.Analysis
