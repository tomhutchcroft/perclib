/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Ported from the source repository `yujinhkim/lrp`, branch `critical-lrp-1`, commit
`d382e4c28d92dd4e698ebf4f2aaf0bc932ae73fc`, file `PercLib/CriticalLRP/ODE.lean` (blob `2294eb5a37`),
contributed by `yujinhkim`; licence Apache-2.0 as declared in that commit's file headers and
`third_party/critical-lrp/NOTICE.md`. Upstream origin `yujinhkim/Critical-Long-range-percolation` at
`3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf` (not independently verified). Changes: focused imports,
no disabled linters or `autoImplicit`, namespace `PercLib.Analysis`, and the helper
`intervalIntegrable_of_integrableOn_uIcc` replaced by mathlib's
`MeasureTheory.IntegrableOn.intervalIntegrable`.

Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1, Lemma I.4.5 (p. 35).
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The Riccati comparison ODE: Lemma I.4.5 (1)-(3)

For `A, α, r₀ > 0` and `f > 0` differentiable on `[r₀, ∞)`:

* `lemma_I_4_5_one_nocont`: `A x^{-α-1} f² ≤ f'` on `[r₀, ∞)` gives `f r ≤ (α/A) r^α`;
* `lemma_I_4_5_two_nocont`: `f → ∞` and `f' ≤ A x^{-α-1} f²` give `(α/A) r^α ≤ f r`;
* `inv_eq_of_ode` and `lemma_I_4_5_three`: for `f' = A (1 - h) t^{-α-1} f²` with `h` measurable
  and bounded by `C` on `[r₀, ∞)`,
  `1/f r = 1/f R + (A/α)(r^{-α} - R^{-α}) - A ∫_r^R h s s^{-α-1}`, and if `f → ∞`,
  `f r = (α/A) r^α / (1 - α r^α ∫_{(r,∞)} h s s^{-α-1})`;
* `inv_eq_of_hasDerivWithinAt` and `one_sub_mul_integral_Ioi_pos_and_eq_div_of_hasDerivWithinAt`:
  the same with `f` differentiable on `[r₀, ∞)` one-sided at `r₀` and `h` measurable on
  `[r₀, ∞)`, together with strict positivity of the denominator;
* `tendsto_rpow_mul_integral_Ioi_mul_rpow_neg` and `isEquivalent_rpow_of_hasDerivWithinAt_riccati`:
  if moreover `h → 0`, the relative error vanishes and `f r ~ (α/A) r^α`.

No continuity of `f'` is assumed. The auxiliary function `1/f - (A/α) r^{-α}` is monotone.
-/

@[expose] public section

noncomputable section

namespace PercLib.Analysis

open Filter Set MeasureTheory
open scoped Topology

/-- A measurable function bounded on `uIcc a b` is interval integrable on `a..b`. -/
theorem intervalIntegrable_of_bound {f : ℝ → ℝ} {a b C : ℝ}
    (hmeas : AEStronglyMeasurable f (volume.restrict (uIcc a b)))
    (hC : ∀ᵐ x ∂(volume.restrict (uIcc a b)), ‖f x‖ ≤ C) :
    IntervalIntegrable f volume a b :=
  IntegrableOn.intervalIntegrable
    (IntegrableOn.of_bound (isCompact_uIcc (a := a) (b := b)).measure_lt_top hmeas C hC)

/-- **Lemma I.4.5(1)** without a continuity hypothesis on `f'`:
if `f > 0` and `f'(r) ≥ A r^{-α-1} f(r)²` for all `r ≥ r₀`, then
`f(r) ≤ (α/A) r^α` for all `r ≥ r₀`. -/
theorem lemma_I_4_5_one_nocont {f f' : ℝ → ℝ} {A α r₀ : ℝ}
    (hA : 0 < A) (hα : 0 < α) (hr₀ : 0 < r₀)
    (hderiv : ∀ x, r₀ ≤ x → HasDerivAt f (f' x) x)
    (hpos : ∀ x, r₀ ≤ x → 0 < f x)
    (hineq : ∀ x, r₀ ≤ x → A * x ^ (-α - 1) * (f x) ^ 2 ≤ f' x) :
    ∀ r, r₀ ≤ r → f r ≤ α / A * r ^ α := by
  -- the auxiliary function
  set H : ℝ → ℝ := fun x => (f x)⁻¹ - (A / α) * x ^ (-α) with hH
  -- its derivative on `(r₀, ∞)`
  have hHderiv : ∀ x, r₀ < x → HasDerivAt H (-(f' x / (f x) ^ 2) - (A / α) *
      (-α * x ^ (-α - 1))) x := by
    intro x hx
    have hxr : r₀ ≤ x := le_of_lt hx
    have hxpos : 0 < x := lt_of_lt_of_le hr₀ hxr
    have h1 : HasDerivAt (fun y => (f y)⁻¹) (-(f' x / (f x) ^ 2)) x := by
      have := (hderiv x hxr).inv (ne_of_gt (hpos x hxr))
      rwa [neg_div] at this
    have h2 : HasDerivAt (fun y : ℝ => x ^ (-α)) 0 x := hasDerivAt_const x _
    have h3 : HasDerivAt (fun y : ℝ => (A / α) * y ^ (-α))
        ((A / α) * (-α * x ^ (-α - 1))) x :=
      (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hxpos))).const_mul (A / α)
    exact h1.sub h3
  -- the derivative is nonpositive
  have hHnonpos : ∀ x, r₀ < x → -(f' x / (f x) ^ 2) - (A / α) * (-α * x ^ (-α - 1)) ≤ 0 := by
    intro x hx
    have hxr : r₀ ≤ x := le_of_lt hx
    have hxpos : 0 < x := lt_of_lt_of_le hr₀ hxr
    have hfpos : 0 < f x := hpos x hxr
    have hsq : 0 < (f x) ^ 2 := by positivity
    have hineq' : A * x ^ (-α - 1) ≤ f' x / (f x) ^ 2 := by
      rw [le_div_iff₀ hsq]
      exact hineq x hxr
    have hAα : A / α * α = A := by field_simp
    have heq : -(f' x / (f x) ^ 2) - (A / α) * (-α * x ^ (-α - 1))
        = -(f' x / (f x) ^ 2 - A * x ^ (-α - 1)) := by
      rw [← hAα]
      field_simp
      ring
    rw [heq]
    linarith
  -- hence `H` is antitone on `[r₀, ∞)`
  have hanti : AntitoneOn H (Ici r₀) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici r₀) ?_ ?_ ?_
    · -- continuity of `H` on `[r₀, ∞)`
      intro x hx
      rw [mem_Ici] at hx
      rcases eq_or_lt_of_le hx with hx' | hx'
      · subst hx'
        have hfcont : ContinuousAt f r₀ := (hderiv r₀ le_rfl).continuousAt
        have h1 : ContinuousAt (fun y => (f y)⁻¹) r₀ :=
          hfcont.inv₀ (ne_of_gt (hpos r₀ le_rfl))
        have h2 : ContinuousAt (fun y : ℝ => (A / α) * y ^ (-α)) r₀ :=
          (Real.continuousAt_rpow_const r₀ (-α) (Or.inl (ne_of_gt hr₀))).const_mul (A / α)
        exact (h1.sub h2).continuousWithinAt
      · exact (hHderiv x hx').differentiableAt.continuousAt.continuousWithinAt
    · -- differentiability on the interior
      intro x hx
      rw [interior_Ici] at hx
      exact (hHderiv x hx).differentiableAt.differentiableWithinAt
    · -- derivative sign
      intro x hx
      rw [interior_Ici] at hx
      rw [(hHderiv x hx).deriv]
      exact hHnonpos x hx
  intro r hr
  have hrpos : 0 < r := lt_of_lt_of_le hr₀ hr
  -- `H r ≥ H R ≥ -(A/α) R^{-α}` for all `R ≥ r`, hence `H r ≥ 0`
  have hkey : 0 ≤ H r := by
    have hmono : ∀ R, r ≤ R → H R ≤ H r := fun R hR =>
      hanti (mem_Ici.2 (le_trans hr le_rfl)) (mem_Ici.2 (le_trans hr hR)) hR
    have hlow : ∀ R, r ≤ R → -((A / α) * R ^ (-α)) ≤ H r := by
      intro R hR
      have hRpos : 0 < R := lt_of_lt_of_le hrpos hR
      have h1 : (0 : ℝ) ≤ (f R)⁻¹ := inv_nonneg.2 (le_of_lt (hpos R (le_trans hr hR)))
      have h2 : (f R)⁻¹ - (A / α) * R ^ (-α) ≤ H r := hmono R hR
      linarith
    have htend : Tendsto (fun R : ℝ => -((A / α) * R ^ (-α))) atTop (𝓝 0) := by
      have h0 : Tendsto (fun R : ℝ => R ^ (-α)) atTop (𝓝 0) := tendsto_rpow_neg_atTop hα
      simpa using (h0.const_mul (A / α)).neg
    exact le_of_tendsto htend (eventually_atTop.2 ⟨r, hlow⟩)
  -- conclude
  have hfr : 0 < f r := hpos r hr
  have hH' : (A / α) * r ^ (-α) ≤ (f r)⁻¹ := by
    have := hkey
    simp only [hH] at this
    linarith
  have h1 : (A / α) * r ^ (-α) * f r ≤ 1 := by
    have h2 := mul_le_mul_of_nonneg_right hH' (le_of_lt hfr)
    rwa [inv_mul_cancel₀ (ne_of_gt hfr)] at h2
  have h2 : f r ≤ 1 / ((A / α) * r ^ (-α)) := by
    rw [le_div_iff₀ (by positivity)]
    simpa only [mul_comm] using h1
  have h3 : 1 / ((A / α) * r ^ (-α)) = α / A * r ^ α := by
    rw [Real.rpow_neg hrpos.le, one_div, mul_inv]
    field_simp
  linarith [h2, h3.le, h3.symm.le]

open Filter Set MeasureTheory
open scoped Topology


/-- **Lemma I.4.5(2)** without a continuity hypothesis on `f'`. -/
theorem lemma_I_4_5_two_nocont {f f' : ℝ → ℝ} {A α r₀ : ℝ}
    (hA : 0 < A) (hα : 0 < α) (hr₀ : 0 < r₀)
    (hderiv : ∀ x, r₀ ≤ x → HasDerivAt f (f' x) x)
    (hpos : ∀ x, r₀ ≤ x → 0 < f x)
    (hinf : Tendsto f atTop atTop)
    (hineq : ∀ x, r₀ ≤ x → f' x ≤ A * x ^ (-α - 1) * (f x) ^ 2) :
    ∀ r, r₀ ≤ r → α / A * r ^ α ≤ f r := by
  set H : ℝ → ℝ := fun x => (f x)⁻¹ - (A / α) * x ^ (-α) with hH
  have hHderiv : ∀ x, r₀ < x →
      HasDerivAt H (-(f' x / (f x) ^ 2) - (A / α) * (-α * x ^ (-α - 1))) x := by
    intro x hx
    have hxr : r₀ ≤ x := le_of_lt hx
    have hxpos : 0 < x := lt_of_lt_of_le hr₀ hxr
    have h1 : HasDerivAt (fun y => (f y)⁻¹) (-(f' x / (f x) ^ 2)) x := by
      have h := (hderiv x hxr).inv (ne_of_gt (hpos x hxr))
      rwa [neg_div] at h
    have h2 : HasDerivAt (fun y => (A / α) * y ^ (-α))
        ((A / α) * (-α * x ^ (-α - 1))) x :=
      (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hxpos))).const_mul (A / α)
    exact h1.sub h2
  have hHnonneg : ∀ x, r₀ < x →
      0 ≤ -(f' x / (f x) ^ 2) - (A / α) * (-α * x ^ (-α - 1)) := by
    intro x hx
    have hxr : r₀ ≤ x := le_of_lt hx
    have hfpos : 0 < f x := hpos x hxr
    have hsq : 0 < (f x) ^ 2 := by positivity
    have hineq' : f' x / (f x) ^ 2 ≤ A * x ^ (-α - 1) := by
      rw [div_le_iff₀ hsq]
      exact hineq x hxr
    have hAα : A / α * α = A := by field_simp
    have heq : -(f' x / (f x) ^ 2) - (A / α) * (-α * x ^ (-α - 1)) =
        A * x ^ (-α - 1) - f' x / (f x) ^ 2 := by
      rw [← hAα]
      field_simp
      ring
    rw [heq]
    linarith
  have hmonoOn : MonotoneOn H (Ici r₀) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici r₀) ?_ ?_ ?_
    · intro x hx
      rw [mem_Ici] at hx
      rcases eq_or_lt_of_le hx with hx' | hx'
      · subst hx'
        have hfcont : ContinuousAt f r₀ := (hderiv r₀ le_rfl).continuousAt
        have h1 : ContinuousAt (fun y => (f y)⁻¹) r₀ :=
          hfcont.inv₀ (ne_of_gt (hpos r₀ le_rfl))
        have h2 : ContinuousAt (fun y : ℝ => (A / α) * y ^ (-α)) r₀ :=
          (Real.continuousAt_rpow_const r₀ (-α) (Or.inl (ne_of_gt hr₀))).const_mul (A / α)
        exact (h1.sub h2).continuousWithinAt
      · exact (hHderiv x hx').differentiableAt.continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      exact (hHderiv x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      rw [(hHderiv x hx).deriv]
      exact hHnonneg x hx
  intro r hr
  have hrpos : 0 < r := lt_of_lt_of_le hr₀ hr
  have hkey : H r ≤ 0 := by
    have hmono : ∀ R, r ≤ R → H r ≤ H R := fun R hR =>
      hmonoOn (mem_Ici.2 (le_trans hr le_rfl)) (mem_Ici.2 (le_trans hr hR)) hR
    have htend : Tendsto H atTop (𝓝 0) := by
      have hinv : Tendsto (fun R : ℝ => (f R)⁻¹) atTop (𝓝 0) := hinf.inv_tendsto_atTop
      have hpow : Tendsto (fun R : ℝ => R ^ (-α)) atTop (𝓝 0) := tendsto_rpow_neg_atTop hα
      have hlim := hinv.sub (hpow.const_mul (A / α))
      simpa only [hH, mul_zero, sub_zero] using hlim
    exact ge_of_tendsto htend (eventually_atTop.2 ⟨r, hmono⟩)
  have hfr : 0 < f r := hpos r hr
  have hbound : (f r)⁻¹ ≤ (A / α) * r ^ (-α) := by
    have h := hkey
    simp only [hH] at h
    linarith
  have hposB : 0 < (A / α) * r ^ (-α) := by positivity
  have hinv := (inv_le_comm₀ hfr hposB).mp hbound
  have heq : ((A / α) * r ^ (-α))⁻¹ = α / A * r ^ α := by
    rw [Real.rpow_neg hrpos.le, mul_inv, inv_inv]
    field_simp
  exact heq ▸ hinv

open Filter Set MeasureTheory
open scoped Topology


/-- `s ↦ h s * s ^ (-α-1)` is integrable on `Ioi r` for `r > 0`, `α > 0`, `h`
a.e.-strongly measurable on `Ioi r` and bounded on `[r,∞)`. -/
theorem integrableOn_Ioi_mul_rpow_neg_of_bound {h : ℝ → ℝ} {α r C : ℝ} (hr : 0 < r)
    (hα : 0 < α) (hmeas : AEStronglyMeasurable h (volume.restrict (Ioi r)))
    (hC : ∀ t, r ≤ t → |h t| ≤ C) :
    IntegrableOn (fun s => h s * s ^ (-α - 1)) (Ioi r) := by
  have hbound : IntegrableOn (fun s => |C| * s ^ (-α - 1)) (Ioi r) := by
    have h1 : IntegrableOn (fun s : ℝ => s ^ (-α - 1)) (Ioi r) :=
      integrableOn_Ioi_rpow_of_lt (by linarith : -α - 1 < -1) hr
    exact h1.const_mul _
  refine Integrable.mono hbound ?_ ?_
  · exact hmeas.mul (measurable_id.pow_const _).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs0 : 0 < s := lt_of_lt_of_le hr hs.le
    have hCs : |h s| ≤ |C| := le_trans (hC s hs.le) (le_abs_self C)
    have hpos : 0 ≤ s ^ (-α - 1) := Real.rpow_nonneg hs0.le _
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hpos,
      Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg C) hpos)]
    exact mul_le_mul_of_nonneg_right hCs hpos

/-- `s ↦ h s * s ^ (-α-1)` is integrable on `Ioi r` for `r > 0`, `α > 0`, `h`
measurable and bounded on `[r,∞)`. -/
theorem integrableOn_mul_rpow_neg {h : ℝ → ℝ} {α r C : ℝ} (hr : 0 < r) (hα : 0 < α)
    (hmeas : Measurable h) (hC : ∀ t, r ≤ t → |h t| ≤ C) :
    IntegrableOn (fun s => h s * s ^ (-α - 1)) (Ioi r) :=
  integrableOn_Ioi_mul_rpow_neg_of_bound hr hα hmeas.aestronglyMeasurable hC

/-- A function measurable on the subtype `Ici r₀` is a.e.-strongly measurable for Lebesgue
measure restricted to `Ici r₀`. -/
theorem aestronglyMeasurable_restrict_Ici_of_measurable_domRestrict {h : ℝ → ℝ} {r₀ : ℝ}
    (hmeas : Measurable ((Ici r₀).domRestrict h)) :
    AEStronglyMeasurable h (volume.restrict (Ici r₀)) :=
  ((aemeasurable_restrict_iff_comap_subtype measurableSet_Ici).2
    hmeas.aemeasurable).aestronglyMeasurable

/-- Finite-`R` form of the integral identity, with `f` differentiable on `[r₀, ∞)` (one-sided at
`r₀`) and `h` measurable and bounded on `[r₀, ∞)`: for `r₀ ≤ r ≤ R`,
`1/f r = 1/f R + (A/α)(r^{-α} - R^{-α}) - A ∫_r^R h s s^{-α-1} ds`. -/
theorem inv_eq_of_hasDerivWithinAt {f f' h : ℝ → ℝ} {A α r₀ C : ℝ}
    (hA : 0 < A) (hα : 0 < α) (hr₀ : 0 < r₀)
    (hderiv : ∀ t, r₀ ≤ t → HasDerivWithinAt f (f' t) (Ici r₀) t)
    (hpos : ∀ t, r₀ ≤ t → 0 < f t)
    (hode : ∀ t, r₀ ≤ t → f' t = A * (1 - h t) * t ^ (-α - 1) * (f t) ^ 2)
    (hmeas : Measurable ((Ici r₀).domRestrict h)) (hC : ∀ t, r₀ ≤ t → |h t| ≤ C)
    {r R : ℝ} (hr : r₀ ≤ r) (hrR : r ≤ R) :
    (f r)⁻¹ = (f R)⁻¹ + A / α * (r ^ (-α) - R ^ (-α)) - A * ∫ s in r..R, h s * s ^ (-α - 1) := by
  have hr0 : 0 < r := lt_of_lt_of_le hr₀ hr
  have hae : AEStronglyMeasurable h (volume.restrict (Ioi r)) :=
    (aestronglyMeasurable_restrict_Ici_of_measurable_domRestrict hmeas).mono_measure
      (Measure.restrict_mono (fun x hx => mem_Ici.2 (hr.trans (le_of_lt hx))) le_rfl)
  have hI2 : IntervalIntegrable (fun t => h t * t ^ (-α - 1)) volume r R :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hrR).2
      ((integrableOn_Ioi_mul_rpow_neg_of_bound hr0 hα hae
        (fun t ht => hC t (hr.trans ht))).mono_set Ioc_subset_Ioi_self)
  have hzero : (0 : ℝ) ∉ uIcc r R := by
    rw [uIcc_of_le hrR]
    exact fun hmem => (not_le.2 hr0) hmem.1
  have hI1 : IntervalIntegrable (fun t : ℝ => t ^ (-α - 1)) volume r R :=
    intervalIntegral.intervalIntegrable_rpow (Or.inr hzero)
  have hpt : ∀ t, r₀ ≤ t → f' t / (f t) ^ 2 = A * t ^ (-α - 1) - A * (h t * t ^ (-α - 1)) := by
    intro t ht
    have hft : f t ≠ 0 := ne_of_gt (hpos t ht)
    rw [hode t ht]
    field_simp
  have hInt_f : IntervalIntegrable (fun t => f' t / (f t) ^ 2) volume r R := by
    refine ((hI1.const_mul A).sub (hI2.const_mul A)).congr (fun t ht => ?_)
    rw [uIoc_of_le hrR] at ht
    exact (hpt t (hr.trans ht.1.le)).symm
  have hcont : ContinuousOn (fun u => -(f u)⁻¹) (Icc r R) := by
    intro t ht
    have htr : r₀ ≤ t := hr.trans ht.1
    exact (((hderiv t htr).continuousWithinAt.mono
      (fun x hx => mem_Ici.2 (hr.trans hx.1))).inv₀ (ne_of_gt (hpos t htr))).neg
  have hderivinv : ∀ t ∈ Ioo r R,
      HasDerivWithinAt (fun u => -(f u)⁻¹) (f' t / (f t) ^ 2) (Ioi t) t := by
    intro t ht
    have htr : r₀ < t := hr.trans_lt ht.1
    have h1 := (((hderiv t htr.le).hasDerivAt (Ici_mem_nhds htr)).inv
      (ne_of_gt (hpos t htr.le))).neg
    exact (h1.congr_deriv (by ring)).hasDerivWithinAt
  have hFTC : ∫ t in r..R, f' t / (f t) ^ 2 = -(f R)⁻¹ + (f r)⁻¹ := by
    rw [intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hrR hcont hderivinv hInt_f]
    ring
  have hsplit : ∫ t in r..R, f' t / (f t) ^ 2
      = A * (∫ t in r..R, t ^ (-α - 1)) - A * (∫ t in r..R, h t * t ^ (-α - 1)) := by
    have hpt' : ∀ t ∈ uIcc r R,
        f' t / (f t) ^ 2 = A * t ^ (-α - 1) - A * (h t * t ^ (-α - 1)) := by
      intro t ht
      rw [uIcc_of_le hrR] at ht
      exact hpt t (hr.trans ht.1)
    rw [intervalIntegral.integral_congr hpt',
      intervalIntegral.integral_sub (hI1.const_mul A) (hI2.const_mul A),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hrpow : ∫ t in r..R, t ^ (-α - 1) = (r ^ (-α) - R ^ (-α)) / α := by
    rw [integral_rpow (Or.inr ⟨by intro h; linarith, hzero⟩)]
    have h1 : -α - 1 + 1 = -α := by ring
    rw [h1]
    field_simp
    ring
  calc (f r)⁻¹ = (f R)⁻¹ + ∫ t in r..R, f' t / (f t) ^ 2 := by rw [hFTC]; ring
    _ = (f R)⁻¹ + (A * (∫ t in r..R, t ^ (-α - 1))
          - A * (∫ t in r..R, h t * t ^ (-α - 1))) := by rw [hsplit]
    _ = (f R)⁻¹ + A / α * (r ^ (-α) - R ^ (-α))
          - A * ∫ s in r..R, h s * s ^ (-α - 1) := by
        rw [hrpow]; ring

/-- Finite-`R` form of the integral identity: for `r₀ ≤ r ≤ R`,
`1/f r = 1/f R + (A/α)(r^{-α} - R^{-α}) - A ∫_r^R h s s^{-α-1} ds`. -/
theorem inv_eq_of_ode {f f' h : ℝ → ℝ} {A α r₀ C : ℝ}
    (hA : 0 < A) (hα : 0 < α) (hr₀ : 0 < r₀)
    (hderiv : ∀ t, r₀ ≤ t → HasDerivAt f (f' t) t)
    (hpos : ∀ t, r₀ ≤ t → 0 < f t)
    (hode : ∀ t, r₀ ≤ t → f' t = A * (1 - h t) * t ^ (-α - 1) * (f t) ^ 2)
    (hmeas : Measurable h) (hC : ∀ t, r₀ ≤ t → |h t| ≤ C)
    {r R : ℝ} (hr : r₀ ≤ r) (hrR : r ≤ R) :
    (f r)⁻¹ = (f R)⁻¹ + A / α * (r ^ (-α) - R ^ (-α)) - A * ∫ s in r..R, h s * s ^ (-α - 1) :=
  inv_eq_of_hasDerivWithinAt hA hα hr₀ (fun t ht => (hderiv t ht).hasDerivWithinAt) hpos hode
    (hmeas.comp measurable_subtype_coe) hC hr hrR

/-- Tail form of the integral identity: under the hypotheses of `inv_eq_of_hasDerivWithinAt`
and `f → ∞`, `1/f r = (A/α) r^{-α} - A ∫_r^∞ h s s^{-α-1} ds` for every `r ≥ r₀`. -/
theorem inv_eq_sub_integral_Ioi_of_hasDerivWithinAt {f f' h : ℝ → ℝ} {A α r₀ C : ℝ}
    (hA : 0 < A) (hα : 0 < α) (hr₀ : 0 < r₀)
    (hderiv : ∀ t, r₀ ≤ t → HasDerivWithinAt f (f' t) (Ici r₀) t)
    (hpos : ∀ t, r₀ ≤ t → 0 < f t)
    (hinf : Tendsto f atTop atTop)
    (hode : ∀ t, r₀ ≤ t → f' t = A * (1 - h t) * t ^ (-α - 1) * (f t) ^ 2)
    (hmeas : Measurable ((Ici r₀).domRestrict h)) (hC : ∀ t, r₀ ≤ t → |h t| ≤ C)
    {r : ℝ} (hr : r₀ ≤ r) :
    (f r)⁻¹ = A / α * r ^ (-α) - A * ∫ s in Ioi r, h s * s ^ (-α - 1) := by
  have hr0 : 0 < r := hr₀.trans_le hr
  have hae : AEStronglyMeasurable h (volume.restrict (Ioi r)) :=
    (aestronglyMeasurable_restrict_Ici_of_measurable_domRestrict hmeas).mono_measure
      (Measure.restrict_mono (fun x hx => mem_Ici.2 (hr.trans (le_of_lt hx))) le_rfl)
  have hIint : IntegrableOn (fun s => h s * s ^ (-α - 1)) (Ioi r) :=
    integrableOn_Ioi_mul_rpow_neg_of_bound hr0 hα hae (fun t ht => hC t (hr.trans ht))
  have hlim : Tendsto (fun R : ℝ =>
      (f R)⁻¹ + A / α * (r ^ (-α) - R ^ (-α)) - A * ∫ s in r..R, h s * s ^ (-α - 1))
      atTop (𝓝 (A / α * r ^ (-α) - A * ∫ s in Ioi r, h s * s ^ (-α - 1))) := by
    have h1 : Tendsto (fun R : ℝ => (f R)⁻¹) atTop (𝓝 0) := hinf.inv_tendsto_atTop
    have h3 : Tendsto (fun R : ℝ => A / α * (r ^ (-α) - R ^ (-α))) atTop
        (𝓝 (A / α * r ^ (-α))) := by
      simpa using (tendsto_const_nhds.sub (tendsto_rpow_neg_atTop hα)).const_mul (A / α)
    have h4 := (intervalIntegral_tendsto_integral_Ioi r hIint tendsto_id).const_mul A
    simpa using (h1.add h3).sub h4
  refine tendsto_nhds_unique (tendsto_const_nhds.congr' ?_) hlim
  filter_upwards [eventually_ge_atTop r] with R hR
  exact inv_eq_of_hasDerivWithinAt hA hα hr₀ hderiv hpos hode hmeas hC hr hR

/-- Under the hypotheses of `inv_eq_of_hasDerivWithinAt` and `f → ∞`, for every `r ≥ r₀` the
denominator `1 - α r^α ∫_r^∞ h s s^{-α-1} ds` is strictly positive and
`f r = (α/A) r^α / (1 - α r^α ∫_r^∞ h s s^{-α-1} ds)`. -/
theorem one_sub_mul_integral_Ioi_pos_and_eq_div_of_hasDerivWithinAt {f f' h : ℝ → ℝ}
    {A α r₀ C : ℝ} (hA : 0 < A) (hα : 0 < α) (hr₀ : 0 < r₀)
    (hderiv : ∀ t, r₀ ≤ t → HasDerivWithinAt f (f' t) (Ici r₀) t)
    (hpos : ∀ t, r₀ ≤ t → 0 < f t)
    (hinf : Tendsto f atTop atTop)
    (hode : ∀ t, r₀ ≤ t → f' t = A * (1 - h t) * t ^ (-α - 1) * (f t) ^ 2)
    (hmeas : Measurable ((Ici r₀).domRestrict h)) (hC : ∀ t, r₀ ≤ t → |h t| ≤ C) :
    ∀ r, r₀ ≤ r → 0 < 1 - α * r ^ α * ∫ s in Ioi r, h s * s ^ (-α - 1) ∧
      f r = α / A * r ^ α / (1 - α * r ^ α * ∫ s in Ioi r, h s * s ^ (-α - 1)) := by
  intro r hr
  have hr0 : 0 < r := hr₀.trans_le hr
  have hrα : 0 < r ^ α := Real.rpow_pos_of_pos hr0 α
  have hfr : 0 < f r := hpos r hr
  have heq : 1 - α * r ^ α * (∫ s in Ioi r, h s * s ^ (-α - 1)) = α / A * r ^ α * (f r)⁻¹ := by
    rw [inv_eq_sub_integral_Ioi_of_hasDerivWithinAt hA hα hr₀ hderiv hpos hinf hode hmeas hC hr,
      Real.rpow_neg hr0.le]
    field_simp
  rw [heq]
  refine ⟨by positivity, ?_⟩
  field_simp

/-- **Lemma I.4.5(3)**. -/
theorem lemma_I_4_5_three {f f' h : ℝ → ℝ} {A α r₀ C : ℝ}
    (hA : 0 < A) (hα : 0 < α) (hr₀ : 0 < r₀)
    (hderiv : ∀ t, r₀ ≤ t → HasDerivAt f (f' t) t)
    (hpos : ∀ t, r₀ ≤ t → 0 < f t)
    (hinf : Tendsto f atTop atTop)
    (hode : ∀ t, r₀ ≤ t → f' t = A * (1 - h t) * t ^ (-α - 1) * (f t) ^ 2)
    (hmeas : Measurable h) (hC : ∀ t, r₀ ≤ t → |h t| ≤ C) :
    ∀ r, r₀ ≤ r →
      f r = (α / A) * r ^ α / (1 - α * r ^ α * ∫ s in Ioi r, h s * s ^ (-α - 1)) := fun r hr =>
  (one_sub_mul_integral_Ioi_pos_and_eq_div_of_hasDerivWithinAt hA hα hr₀
    (fun t ht => (hderiv t ht).hasDerivWithinAt) hpos hinf hode
    (hmeas.comp measurable_subtype_coe) hC r hr).2

/-- If `α > 0` and `h → 0`, then `α r^α ∫_r^∞ h s s^{-α-1} ds → 0`: the integral is bounded by
`sup_{s ≥ r} |h s|` after normalisation. No measurability of `h` is needed. -/
theorem tendsto_rpow_mul_integral_Ioi_mul_rpow_neg {h : ℝ → ℝ} {α : ℝ} (hα : 0 < α)
    (hh : Tendsto h atTop (𝓝 0)) :
    Tendsto (fun r => α * r ^ α * ∫ s in Ioi r, h s * s ^ (-α - 1)) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hh (ε / 2) (by positivity)
  refine ⟨max N 1, fun r hr => ?_⟩
  have hrN : N ≤ r := (le_max_left _ _).trans hr
  have hr0 : 0 < r := one_pos.trans_le ((le_max_right _ _).trans hr)
  have hrα : 0 < r ^ α := Real.rpow_pos_of_pos hr0 α
  have hbint : IntegrableOn (fun s : ℝ => ε / 2 * s ^ (-α - 1)) (Ioi r) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : -α - 1 < -1) hr0).const_mul _
  have hbound : ‖∫ s in Ioi r, h s * s ^ (-α - 1)‖ ≤ ∫ s in Ioi r, ε / 2 * s ^ (-α - 1) := by
    refine norm_integral_le_of_norm_le hbint ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs0 : 0 < s := hr0.trans hs
    have hpow : 0 ≤ s ^ (-α - 1) := Real.rpow_nonneg hs0.le _
    have hhs : |h s| ≤ ε / 2 := by
      have := hN s (hrN.trans hs.le)
      rw [Real.dist_eq, sub_zero] at this
      exact this.le
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hpow]
    exact mul_le_mul_of_nonneg_right hhs hpow
  have hval : ∫ s in Ioi r, ε / 2 * s ^ (-α - 1) = ε / 2 * (r ^ (-α) / α) := by
    rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith : -α - 1 < -1) hr0]
    congr 1
    rw [show -α - 1 + 1 = -α by ring, neg_div_neg_eq]
  rw [hval, Real.norm_eq_abs] at hbound
  rw [Real.dist_eq, sub_zero, abs_mul, abs_of_pos (by positivity : 0 < α * r ^ α)]
  calc α * r ^ α * |∫ s in Ioi r, h s * s ^ (-α - 1)|
      ≤ α * r ^ α * (ε / 2 * (r ^ (-α) / α)) :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = ε / 2 := by
        rw [Real.rpow_neg hr0.le]
        field_simp
    _ < ε := by linarith

/-- Under the hypotheses of `inv_eq_of_hasDerivWithinAt`, `f → ∞` and `h → 0`,
`f r ~ (α/A) r^α`. -/
theorem isEquivalent_rpow_of_hasDerivWithinAt_riccati {f f' h : ℝ → ℝ} {A α r₀ C : ℝ}
    (hA : 0 < A) (hα : 0 < α) (hr₀ : 0 < r₀)
    (hderiv : ∀ t, r₀ ≤ t → HasDerivWithinAt f (f' t) (Ici r₀) t)
    (hpos : ∀ t, r₀ ≤ t → 0 < f t)
    (hinf : Tendsto f atTop atTop)
    (hode : ∀ t, r₀ ≤ t → f' t = A * (1 - h t) * t ^ (-α - 1) * (f t) ^ 2)
    (hmeas : Measurable ((Ici r₀).domRestrict h)) (hC : ∀ t, r₀ ≤ t → |h t| ≤ C)
    (hh : Tendsto h atTop (𝓝 0)) :
    Asymptotics.IsEquivalent atTop f fun r => α / A * r ^ α := by
  refine Asymptotics.isEquivalent_of_tendsto_one ?_
  have hlim : Tendsto (fun r => (1 - α * r ^ α * ∫ s in Ioi r, h s * s ^ (-α - 1))⁻¹) atTop
      (𝓝 1) := by
    simpa using (tendsto_const_nhds.sub (tendsto_rpow_mul_integral_Ioi_mul_rpow_neg hα hh)).inv₀
      (by norm_num : (1 : ℝ) - 0 ≠ 0)
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop r₀] with r hr
  have hr0 : 0 < r := hr₀.trans_le hr
  have hrα : 0 < r ^ α := Real.rpow_pos_of_pos hr0 α
  obtain ⟨hpos', hform⟩ := one_sub_mul_integral_Ioi_pos_and_eq_div_of_hasDerivWithinAt hA hα hr₀
    hderiv hpos hinf hode hmeas hC r hr
  rw [Pi.div_apply, hform]
  field_simp

/-! ### Non-vacuity -/

/-- `x^{-2} x² = 1` for `x > 0`. -/
private theorem rpow_neg_two_mul_sq {x : ℝ} (hx : 0 < x) : x ^ (-1 - 1 : ℝ) * x ^ 2 = 1 := by
  rw [show (-1 - 1 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hx.le, Real.rpow_natCast,
    inv_mul_cancel₀ (by positivity)]

/-- Non-vacuity: `f r = (α/A) r^α = r` with `h = 0`, at `A = α = r₀ = 1`, satisfies the hypotheses
of all three items, with equality in the differential inequalities. -/
example :
    (∀ r : ℝ, 1 ≤ r → r ≤ 1 / 1 * r ^ (1 : ℝ)) ∧ (∀ r : ℝ, 1 ≤ r → 1 / 1 * r ^ (1 : ℝ) ≤ r) ∧
      ∀ r : ℝ, 1 ≤ r → r = (1 / 1) * r ^ (1 : ℝ) /
        (1 - 1 * r ^ (1 : ℝ) * ∫ s in Ioi r, (fun _ : ℝ => (0 : ℝ)) s * s ^ (-1 - 1 : ℝ)) := by
  have hd : ∀ x : ℝ, 1 ≤ x → HasDerivAt (fun y : ℝ => y) ((fun _ : ℝ => (1 : ℝ)) x) x :=
    fun x _ => hasDerivAt_id' x
  have hp : ∀ x : ℝ, 1 ≤ x → 0 < (fun y : ℝ => y) x := fun x hx => by simp only; linarith
  refine ⟨lemma_I_4_5_one_nocont one_pos one_pos one_pos hd hp fun x hx => ?_,
    lemma_I_4_5_two_nocont one_pos one_pos one_pos hd hp tendsto_id fun x hx => ?_,
    lemma_I_4_5_three (C := 0) one_pos one_pos one_pos hd hp tendsto_id (fun t ht => ?_)
      measurable_const (fun t _ => by simp)⟩
  · simp only [one_mul]; rw [rpow_neg_two_mul_sq (by linarith)]
  · simp only [one_mul]; rw [rpow_neg_two_mul_sq (by linarith)]
  · simp only [sub_zero, one_mul, mul_one]; rw [rpow_neg_two_mul_sq (by linarith)]

end PercLib.Analysis
