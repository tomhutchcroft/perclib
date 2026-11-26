/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-16, against pinned mathlib. No upstream proof is copied.
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

/-!
# Three asymptotic regimes for a linear equation with integrable coefficient error (GAF9)

Let `r₀ ≥ 1` and `α, c > 0`. Suppose:
* `S ≥ 0` is absolutely continuous on every `[r₀, R]`;
* `S' = (2α/r + e) S + g` a.e. on `[r₀, ∞)`, with `e` integrable on `[r₀, ∞)`;
* `g ≥ 0` is locally integrable and `g ~ c r^{α+1}`.

Then (`isEquivalent_linearODE_lt`, `isEquivalent_linearODE_eq`, `exists_isEquivalent_linearODE_gt`):
* `S ~ c r^{α+2}/(2 - α)` if `α < 2`;
* `S ~ c r⁴ log r` if `α = 2`;
* `S ~ K r^{2α}` for some `K > 0` if `α > 2`.

If moreover `m ~ m₀ r^α` with `m₀ > 0`, then `√(S/m)` is `≍ r`, `r √(log r)` or `r^{α/2}`
respectively (`isTheta_sqrt_linearODE_lt`, `_eq`, `_gt`).

The proof uses the integrating factor `Φ(r) = r^{2α} e^{E(r)}` with `E(r) = ∫_{r₀}^r e`, so
`(S/Φ)' = g/Φ ~ c e^{-E(∞)} r^{1-α}`. The integral of a function equivalent to a weight is
handled by `tendsto_div_of_ae_deriv_near` and the convergent case by monotone convergence.

No definition is introduced.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Real intervalIntegral Asymptotics
open scoped Topology

namespace PercLib.Analysis

/-! ### Integrating an asymptotic derivative -/

/-- **Integrating an asymptotic derivative.** Let `F` be absolutely continuous on every
`[r₀, R]`, `w ≥ 0` a weight on `[r₀, ∞)` with antiderivative `W → ∞`, and suppose that for every
`δ > 0` eventually `(C - δ) w ≤ F' ≤ (C + δ) w` a.e. Then `F/W → C`. -/
theorem tendsto_div_of_ae_deriv_near {F w W : ℝ → ℝ} {r₀ C : ℝ}
    (hac : ∀ R, r₀ ≤ R → AbsolutelyContinuousOnInterval F r₀ R)
    (hwint : ∀ a b, r₀ ≤ a → a ≤ b → IntervalIntegrable w volume a b)
    (hW : ∀ a b, r₀ ≤ a → a ≤ b → ∫ s in a..b, w s = W b - W a)
    (hWtop : Tendsto W atTop atTop)
    (hder : ∀ δ > 0, ∃ R₁, ∀ᵐ s, R₁ ≤ s →
      (C - δ) * w s ≤ deriv F s ∧ deriv F s ≤ (C + δ) * w s) :
    Tendsto (fun r => F r / W r) atTop (𝓝 C) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨R₁', hR₁'⟩ := hder (ε / 4) (by positivity)
  set R₁ := max R₁' r₀
  have hR₁r₀ : r₀ ≤ R₁ := le_max_right _ _
  set B := |F R₁ - C * W R₁| + ε / 4 * |W R₁| with hBdef
  obtain ⟨R₂, hR₂⟩ := eventually_atTop.1 ((tendsto_atTop.1 hWtop) (4 * B / ε + 1))
  refine ⟨max R₁ R₂, fun R hR => ?_⟩
  have hRR₁ : R₁ ≤ R := (le_max_left _ _).trans hR
  have hWR : 4 * B / ε + 1 ≤ W R := hR₂ R ((le_max_right _ _).trans hR)
  have hB0 : 0 ≤ B := by positivity
  have hWpos : 0 < W R := by
    have : 0 ≤ 4 * B / ε := by positivity
    linarith
  have hacR : AbsolutelyContinuousOnInterval F R₁ R := (hac R (hR₁r₀.trans hRR₁)).mono (by
    rw [uIcc_of_le hRR₁, uIcc_of_le (hR₁r₀.trans hRR₁)]
    exact Icc_subset_Icc hR₁r₀ le_rfl)
  have hFTC := hacR.integral_deriv_eq_sub
  have hae : ∀ᵐ s ∂(volume.restrict (Icc R₁ R)),
      (C - ε / 4) * w s ≤ deriv F s ∧ deriv F s ≤ (C + ε / 4) * w s := by
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hR₁'] with s hs hsI
    exact hs ((le_max_left _ _).trans hsI.1)
  have hwi := hwint R₁ R hR₁r₀ hRR₁
  have hlow : ∫ s in R₁..R, (C - ε / 4) * w s ≤ F R - F R₁ := by
    rw [← hFTC]
    exact integral_mono_ae_restrict hRR₁ (hwi.const_mul _) hacR.intervalIntegrable_deriv
      (hae.mono fun s hs => hs.1)
  have hup : F R - F R₁ ≤ ∫ s in R₁..R, (C + ε / 4) * w s := by
    rw [← hFTC]
    exact integral_mono_ae_restrict hRR₁ hacR.intervalIntegrable_deriv (hwi.const_mul _)
      (hae.mono fun s hs => hs.2)
  rw [intervalIntegral.integral_const_mul, hW R₁ R hR₁r₀ hRR₁] at hlow hup
  -- bounds
  have hBW : B ≤ ε / 4 * W R := by
    have : 4 * B / ε ≤ W R := by linarith
    rw [div_le_iff₀ hε] at this
    linarith
  have h2 : |F R₁ - C * W R₁| ≤ B := by
    have : 0 ≤ ε / 4 * |W R₁| := by positivity
    rw [hBdef]
    linarith
  have h3 : ε / 4 * |W R₁| ≤ B := by
    have := abs_nonneg (F R₁ - C * W R₁)
    rw [hBdef]
    linarith
  obtain ⟨h2a, h2b⟩ := abs_le.1 h2
  have hW1a : -|W R₁| ≤ W R₁ := neg_abs_le _
  have hW1b : W R₁ ≤ |W R₁| := le_abs_self _
  rw [Real.dist_eq, abs_lt, lt_sub_iff_add_lt, sub_lt_iff_lt_add, lt_div_iff₀ hWpos,
    div_lt_iff₀ hWpos]
  have h4 : ε / 4 * W R₁ ≤ ε / 4 * |W R₁| := mul_le_mul_of_nonneg_left hW1b (by positivity)
  have h5 : -(ε / 4 * |W R₁|) ≤ ε / 4 * W R₁ := by
    have := mul_le_mul_of_nonneg_left hW1a (by positivity : (0 : ℝ) ≤ ε / 4)
    linarith
  have e1 : (C - ε / 4) * (W R - W R₁) = C * W R - C * W R₁ - ε / 4 * W R + ε / 4 * W R₁ := by
    ring
  have e2 : (C + ε / 4) * (W R - W R₁) = C * W R - C * W R₁ + ε / 4 * W R - ε / 4 * W R₁ := by
    ring
  have e3 : (C - ε) * W R = C * W R - 4 * (ε / 4 * W R) := by ring
  have e4 : (C + ε) * W R = C * W R + 4 * (ε / 4 * W R) := by ring
  have hεW : 0 < ε / 4 * W R := by positivity
  constructor <;> linarith

/-! ### The integrating factor -/

section Core

variable {α c r₀ : ℝ} {S e g : ℝ → ℝ}

/-- **The integrating factor.** Under the hypotheses of the linear ODE asymptotics, put
`E(r) = ∫_{r₀}^r e` and `U = S r^{-2α} e^{-E}`. Then `U` is absolutely continuous on every `[r₀, R]`
and `S = U r^{2α} e^{E}` on `[r₀, ∞)`. Moreover `U' = ψ ≥ 0` a.e. on `[r₀, ∞)`, where
`ψ(r)/r^{1-α} → c e^{-E(∞)}`. -/
theorem linearODE_core (hr₀ : 1 ≤ r₀) (hc : 0 < c)
    (hSac : ∀ R, r₀ ≤ R → AbsolutelyContinuousOnInterval S r₀ R)
    (hder : ∀ᵐ r, r₀ ≤ r → deriv S r = (2 * α / r + e r) * S r + g r)
    (he : IntegrableOn e (Ici r₀)) (hg0 : ∀ r, r₀ ≤ r → 0 ≤ g r)
    (hg : g ~[atTop] fun r => c * r ^ (α + 1)) :
    ∃ U ψ : ℝ → ℝ,
      (∀ R, r₀ ≤ R → AbsolutelyContinuousOnInterval U r₀ R) ∧
      (∀ r, r₀ ≤ r → S r = U r * (r ^ (2 * α) * Real.exp (∫ s in r₀..r, e s))) ∧
      (∀ᵐ r, r₀ ≤ r → deriv U r = ψ r) ∧ (∀ r, r₀ ≤ r → 0 ≤ ψ r) ∧
      Tendsto (fun r => ψ r / r ^ (1 - α)) atTop
        (𝓝 (c * Real.exp (-∫ s in Ioi r₀, e s))) ∧
      Tendsto (fun r => ∫ s in r₀..r, e s) atTop (𝓝 (∫ s in Ioi r₀, e s)) := by
  set E : ℝ → ℝ := fun r => ∫ s in r₀..r, e s with hE
  set Einf := ∫ s in Ioi r₀, e s with hEinf
  have hr₀0 : 0 < r₀ := by linarith
  have heint : ∀ R, r₀ ≤ R → IntervalIntegrable e volume r₀ R := fun R h =>
    (intervalIntegrable_iff_integrableOn_Icc_of_le h).2 (he.mono_set Icc_subset_Ici_self)
  -- the weight `u = r^{-2α} e^{-E}`
  set u : ℝ → ℝ := fun r => r ^ (-(2 * α)) * Real.exp (-E r) with hu
  have huac : ∀ R, r₀ ≤ R → AbsolutelyContinuousOnInterval u r₀ R := by
    intro R hR
    have hEac : AbsolutelyContinuousOnInterval E r₀ R :=
      (heint R hR).absolutelyContinuousOnInterval_intervalIntegral (c := r₀) left_mem_uIcc
    obtain ⟨B, hB⟩ := isCompact_uIcc.exists_bound_of_continuousOn hEac.neg.continuousOn
    obtain ⟨K, hK⟩ :=
      (Real.contDiff_exp.contDiffOn (s := Icc (-B) B) (n := 1)).exists_lipschitzOnWith
      (by norm_num) (convex_Icc _ _) isCompact_Icc
    have hexp : AbsolutelyContinuousOnInterval (fun r => Real.exp (-E r)) r₀ R :=
      hK.comp_absolutelyContinuousOnInterval (g := fun r => -E r) (fun r hr => by
        have : |-E r| ≤ B := by simpa only [Real.norm_eq_abs, Pi.neg_apply] using hB r hr
        change -E r ∈ Icc (-B) B
        exact ⟨by linarith [neg_abs_le (-E r)], (le_abs_self _).trans this⟩) hEac.neg
    have hpow : AbsolutelyContinuousOnInterval (fun r : ℝ => r ^ (-(2 * α))) r₀ R := by
      refine ContDiffOn.absolutelyContinuousOnInterval fun r hr => ?_
      rw [uIcc_of_le hR] at hr
      exact (Real.contDiffAt_rpow_const_of_ne (hr₀0.trans_le hr.1).ne').contDiffWithinAt
    exact hpow.mul hexp
  set U : ℝ → ℝ := fun r => S r * u r with hUdef
  set ψ : ℝ → ℝ := fun r => g r * u r with hψ
  refine ⟨U, ψ, fun R hR => (hSac R hR).mul (huac R hR), fun r hr => ?_, ?_, fun r hr => ?_,
    ?_, ?_⟩
  · -- `S = U r^{2α} e^{E}`
    have hr0 : 0 < r := hr₀0.trans_le hr
    simp only [hUdef, hu]
    rw [Real.rpow_neg hr0.le, Real.exp_neg]
    have : 0 < r ^ (2 * α) := Real.rpow_pos_of_pos hr0 _
    field_simp
    rfl
  · -- the derivative
    have hSd := ae_all_iff.2 fun n : ℕ =>
      (hSac (r₀ + n) (by linarith [n.cast_nonneg (α := ℝ)])).ae_differentiableAt
    have hEd := ae_all_iff.2 fun n : ℕ =>
      (heint (r₀ + n) (by linarith [n.cast_nonneg (α := ℝ)])).ae_hasDerivAt_integral
    filter_upwards [hSd, hEd, hder] with r hSr hEr hdr hr
    obtain ⟨n, hn⟩ := exists_nat_ge (r - r₀)
    have hmem : r ∈ uIcc r₀ (r₀ + n) := by
      rw [uIcc_of_le (by linarith [n.cast_nonneg (α := ℝ)])]
      exact ⟨hr, by linarith⟩
    have hr0 : 0 < r := hr₀0.trans_le hr
    have h1 := (hSr n hmem).hasDerivAt
    have h2 : HasDerivAt E (e r) r := hEr n hmem r₀ left_mem_uIcc
    have h3 := Real.hasDerivAt_rpow_const (x := r) (p := -(2 * α)) (Or.inl hr0.ne')
    have h4 := h1.mul (h3.mul (h2.neg.exp))
    have h4' : HasDerivAt U (deriv S r * (r ^ (-(2 * α)) * Real.exp (-E r)) +
        S r * (-(2 * α) * r ^ (-(2 * α) - 1) * Real.exp (-E r) +
          r ^ (-(2 * α)) * (Real.exp (-E r) * -e r))) r := h4
    rw [h4'.deriv, hdr hr, Real.rpow_sub_one hr0.ne']
    simp only [hψ, hu]
    field_simp
    ring
  · exact mul_nonneg (hg0 r hr) (mul_nonneg (Real.rpow_nonneg (hr₀0.trans_le hr).le _)
      (Real.exp_pos _).le)
  · -- `ψ/r^{1-α} → c e^{-E(∞)}`
    have hEt : Tendsto E atTop (𝓝 Einf) :=
      intervalIntegral_tendsto_integral_Ioi r₀ (he.mono_set Ioi_subset_Ici_self) tendsto_id
    have hg1 : Tendsto (fun r => g r / (c * r ^ (α + 1))) atTop (𝓝 1) := by
      have := (isEquivalent_iff_tendsto_one (by
        filter_upwards [eventually_gt_atTop 0] with r hr
        exact mul_ne_zero hc.ne' (Real.rpow_pos_of_pos hr _).ne')).1 hg
      exact this
    have hlim := (hg1.mul_const c).mul ((Real.continuous_exp.tendsto _).comp hEt.neg)
    rw [one_mul] at hlim
    refine hlim.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with r hr
    simp only [Function.comp_apply, hψ, hu]
    have e1 : r ^ (α + 1) * r ^ (-(2 * α)) = r ^ (1 - α) := by
      rw [← Real.rpow_add hr]
      congr 1
      ring
    have hr1 : 0 < r ^ (1 - α) := Real.rpow_pos_of_pos hr _
    have hra : 0 < r ^ (α + 1) := Real.rpow_pos_of_pos hr _
    rw [← e1]
    field_simp
  · exact intervalIntegral_tendsto_integral_Ioi r₀ (he.mono_set Ioi_subset_Ici_self) tendsto_id

/-- From the integrating factor: if `U/W → c e^{-E(∞)}` for a positive `W`, then
`S ~ c r^{2α} W`. -/
theorem isEquivalent_of_core {U W : ℝ → ℝ} (hc : 0 < c) (hr₀ : 1 ≤ r₀)
    (hSU : ∀ r, r₀ ≤ r → S r = U r * (r ^ (2 * α) * Real.exp (∫ s in r₀..r, e s)))
    (hE : Tendsto (fun r => ∫ s in r₀..r, e s) atTop (𝓝 (∫ s in Ioi r₀, e s)))
    (hUW : Tendsto (fun r => U r / W r) atTop (𝓝 (c * Real.exp (-∫ s in Ioi r₀, e s))))
    (hWpos : ∀ᶠ r in atTop, 0 < W r) :
    S ~[atTop] fun r => c * r ^ (2 * α) * W r := by
  refine isEquivalent_of_tendsto_one ?_
  have hlim := (hUW.mul ((Real.continuous_exp.tendsto _).comp hE)).div_const c
  have e1 : c * Real.exp (-∫ s in Ioi r₀, e s) * Real.exp (∫ s in Ioi r₀, e s) / c = 1 := by
    rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one, div_self hc.ne']
  rw [e1] at hlim
  refine hlim.congr' ?_
  filter_upwards [hWpos, eventually_ge_atTop r₀] with r hW hr
  have hr0 : 0 < r := by linarith
  have : 0 < r ^ (2 * α) := Real.rpow_pos_of_pos hr0 _
  simp only [Function.comp_apply, Pi.div_apply]
  rw [hSU r hr]
  field_simp

variable (α c r₀ S e g) in
/-- The hypotheses of the linear ODE asymptotics, other than the regime of `α`. -/
theorem linearODE_weight_hder {U ψ : ℝ → ℝ} {C : ℝ}
    (hUd : ∀ᵐ r, r₀ ≤ r → deriv U r = ψ r)
    (hψlim : Tendsto (fun r => ψ r / r ^ (1 - α)) atTop (𝓝 C)) :
    ∀ δ > 0, ∃ R₁, ∀ᵐ s, R₁ ≤ s →
      (C - δ) * s ^ (1 - α) ≤ deriv U s ∧ deriv U s ≤ (C + δ) * s ^ (1 - α) := by
  intro δ hδ
  obtain ⟨R₁, hR₁⟩ := eventually_atTop.1 (Metric.tendsto_nhds.1 hψlim δ hδ)
  refine ⟨max (max R₁ r₀) 1, ?_⟩
  filter_upwards [hUd] with s hs hsR
  have hs0 : 0 < s := by linarith [le_max_right (max R₁ r₀) 1]
  have hw : 0 < s ^ (1 - α) := Real.rpow_pos_of_pos hs0 _
  rw [hs ((le_max_right _ _).trans ((le_max_left _ _).trans hsR))]
  have h := hR₁ s ((le_max_left _ _).trans ((le_max_left _ _).trans hsR))
  rw [Real.dist_eq, abs_lt] at h
  have e : ψ s = ψ s / s ^ (1 - α) * s ^ (1 - α) := by field_simp
  rw [e]
  constructor <;> nlinarith

/-- **Linear ODE asymptotics, `α < 2`.** `S ~ c r^{α+2}/(2 - α)`. -/
theorem isEquivalent_linearODE_lt (hr₀ : 1 ≤ r₀) (hα2 : α < 2) (hc : 0 < c)
    (hSac : ∀ R, r₀ ≤ R → AbsolutelyContinuousOnInterval S r₀ R)
    (hder : ∀ᵐ r, r₀ ≤ r → deriv S r = (2 * α / r + e r) * S r + g r)
    (he : IntegrableOn e (Ici r₀)) (hg0 : ∀ r, r₀ ≤ r → 0 ≤ g r)
    (hg : g ~[atTop] fun r => c * r ^ (α + 1)) :
    S ~[atTop] fun r => c * r ^ (α + 2) / (2 - α) := by
  obtain ⟨U, ψ, hUac, hSU, hUd, -, hψlim, hE⟩ := linearODE_core hr₀ hc hSac hder he hg0 hg
  have hr₀0 : 0 < r₀ := by linarith
  have h2α : 0 < 2 - α := by linarith
  have hUW := tendsto_div_of_ae_deriv_near (F := U) (w := fun s => s ^ (1 - α))
    (W := fun s => s ^ (2 - α) / (2 - α)) hUac
    (fun a b ha hab => ContinuousOn.intervalIntegrable (ContinuousOn.rpow_const continuousOn_id
      fun s hs => Or.inl (by
        rw [uIcc_of_le hab] at hs
        exact (hr₀0.trans_le (ha.trans hs.1)).ne')))
    (fun a b ha hab => by
      rw [integral_rpow (Or.inl (by linarith))]
      rw [show 1 - α + 1 = 2 - α by ring]
      ring)
    ((tendsto_rpow_atTop h2α).atTop_div_const h2α)
    (linearODE_weight_hder α r₀ hUd hψlim)
  have := isEquivalent_of_core hc hr₀ hSU hE hUW
    (by filter_upwards [eventually_gt_atTop 0] with r hr; positivity)
  refine this.congr_right ?_
  filter_upwards [eventually_gt_atTop 0] with r hr
  rw [mul_div_assoc', mul_assoc c, ← Real.rpow_add hr]
  congr 3
  ring

/-- **Linear ODE asymptotics, `α = 2`.** `S ~ c r⁴ log r`. -/
theorem isEquivalent_linearODE_eq (hr₀ : 1 ≤ r₀) (hα2 : α = 2) (hc : 0 < c)
    (hSac : ∀ R, r₀ ≤ R → AbsolutelyContinuousOnInterval S r₀ R)
    (hder : ∀ᵐ r, r₀ ≤ r → deriv S r = (2 * α / r + e r) * S r + g r)
    (he : IntegrableOn e (Ici r₀)) (hg0 : ∀ r, r₀ ≤ r → 0 ≤ g r)
    (hg : g ~[atTop] fun r => c * r ^ (α + 1)) :
    S ~[atTop] fun r => c * r ^ (4 : ℝ) * Real.log r := by
  obtain ⟨U, ψ, hUac, hSU, hUd, -, hψlim, hE⟩ := linearODE_core hr₀ hc hSac hder he hg0 hg
  have hr₀0 : 0 < r₀ := by linarith
  have hUW := tendsto_div_of_ae_deriv_near (F := U) (w := fun s => s ^ (1 - α))
    (W := Real.log) hUac
    (fun a b ha hab => ContinuousOn.intervalIntegrable (ContinuousOn.rpow_const continuousOn_id
      fun s hs => Or.inl (by
        rw [uIcc_of_le hab] at hs
        exact (hr₀0.trans_le (ha.trans hs.1)).ne')))
    (fun a b ha hab => by
      have ha0 : 0 < a := hr₀0.trans_le ha
      rw [hα2, show (1 : ℝ) - 2 = -1 by norm_num]
      simp_rw [Real.rpow_neg_one]
      rw [integral_inv_of_pos ha0 (ha0.trans_le hab), Real.log_div (ha0.trans_le hab).ne' ha0.ne'])
    Real.tendsto_log_atTop
    (linearODE_weight_hder α r₀ hUd hψlim)
  have := isEquivalent_of_core hc hr₀ hSU hE hUW
    (by filter_upwards [eventually_gt_atTop 1] with r hr; exact Real.log_pos hr)
  refine this.congr_right (Eventually.of_forall fun r => ?_)
  rw [hα2]
  norm_num

/-- **Linear ODE asymptotics, `α > 2`.** `S ~ K r^{2α}` for some `K ∈ (0, ∞)`. This case uses
`S ≥ 0`. -/
theorem exists_isEquivalent_linearODE_gt (hr₀ : 1 ≤ r₀) (hα2 : 2 < α) (hc : 0 < c)
    (hS0 : ∀ r, r₀ ≤ r → 0 ≤ S r)
    (hSac : ∀ R, r₀ ≤ R → AbsolutelyContinuousOnInterval S r₀ R)
    (hder : ∀ᵐ r, r₀ ≤ r → deriv S r = (2 * α / r + e r) * S r + g r)
    (he : IntegrableOn e (Ici r₀)) (hg0 : ∀ r, r₀ ≤ r → 0 ≤ g r)
    (hg : g ~[atTop] fun r => c * r ^ (α + 1)) :
    ∃ K > 0, S ~[atTop] fun r => K * r ^ (2 * α) := by
  obtain ⟨U, ψ, hUac, hSU, hUd, hψ0, hψlim, hE⟩ := linearODE_core hr₀ hc hSac hder he hg0 hg
  have hr₀0 : 0 < r₀ := by linarith
  set C := c * Real.exp (-∫ s in Ioi r₀, e s) with hC
  have hC0 : 0 < C := by positivity
  -- `U` is nondecreasing on `[r₀, ∞)`
  have hUint : ∀ a b, r₀ ≤ a → a ≤ b → U b - U a = ∫ s in a..b, ψ s := by
    intro a b ha hab
    have hac : AbsolutelyContinuousOnInterval U a b := (hUac b (ha.trans hab)).mono (by
      rw [uIcc_of_le hab, uIcc_of_le (ha.trans hab)]
      exact Icc_subset_Icc ha le_rfl)
    rw [← hac.integral_deriv_eq_sub]
    refine integral_congr_ae ?_
    filter_upwards [hUd] with s hs hsI
    rw [uIoc_of_le hab] at hsI
    exact hs (ha.trans hsI.1.le)
  have hψint : ∀ a b, r₀ ≤ a → a ≤ b → IntervalIntegrable ψ volume a b := by
    intro a b ha hab
    have hac : AbsolutelyContinuousOnInterval U a b := (hUac b (ha.trans hab)).mono (by
      rw [uIcc_of_le hab, uIcc_of_le (ha.trans hab)]
      exact Icc_subset_Icc ha le_rfl)
    refine hac.intervalIntegrable_deriv.congr_ae ?_
    rw [uIoc_of_le hab]
    filter_upwards [ae_restrict_mem measurableSet_Ioc, ae_restrict_of_ae hUd] with s hsI hs
    exact hs (ha.trans hsI.1.le)
  have hmono : ∀ a b, r₀ ≤ a → a ≤ b → U a ≤ U b := by
    intro a b ha hab
    have := hUint a b ha hab
    have : 0 ≤ ∫ s in a..b, ψ s := integral_nonneg hab fun s hs => hψ0 s (ha.trans hs.1)
    linarith
  -- bounds on `ψ` for large `s`
  obtain ⟨R₁', hR₁'⟩ := eventually_atTop.1 (Metric.tendsto_nhds.1 hψlim (C / 2) (by positivity))
  set R₁ := max R₁' r₀
  have hR₁r₀ : r₀ ≤ R₁ := le_max_right _ _
  have hR₁0 : 0 < R₁ := hr₀0.trans_le hR₁r₀
  have hψb : ∀ s, R₁ ≤ s → C / 2 * s ^ (1 - α) ≤ ψ s ∧ ψ s ≤ 3 * C / 2 * s ^ (1 - α) := by
    intro s hs
    have hs0 : 0 < s := hR₁0.trans_le hs
    have hw : 0 < s ^ (1 - α) := Real.rpow_pos_of_pos hs0 _
    have h := hR₁' s ((le_max_left _ _).trans hs)
    rw [Real.dist_eq, abs_lt] at h
    have e : ψ s = ψ s / s ^ (1 - α) * s ^ (1 - α) := by field_simp
    rw [e]
    constructor <;> nlinarith
  have hpow : ∀ a b, 0 < a → a ≤ b →
      ∫ s in a..b, s ^ (1 - α) = (b ^ (2 - α) - a ^ (2 - α)) / (2 - α) := by
    intro a b ha hab
    rw [integral_rpow (Or.inr ⟨by linarith, by
      rw [uIcc_of_le hab]
      exact fun h => (lt_irrefl 0) (ha.trans_le h.1)⟩)]
    rw [show 1 - α + 1 = 2 - α by ring]
  have hpowint : ∀ a b, 0 < a → a ≤ b → IntervalIntegrable (fun s => s ^ (1 - α)) volume a b :=
    fun a b ha hab => ContinuousOn.intervalIntegrable (ContinuousOn.rpow_const continuousOn_id
      fun s hs => Or.inl (by
        rw [uIcc_of_le hab] at hs
        exact (ha.trans_le hs.1).ne'))
  -- `U` is bounded above
  have hbdd : ∀ b, R₁ ≤ b → U b ≤ U R₁ + 3 * C / 2 * (R₁ ^ (2 - α) / (α - 2)) := by
    intro b hb
    rw [← sub_le_iff_le_add', hUint R₁ b hR₁r₀ hb]
    calc ∫ s in R₁..b, ψ s ≤ ∫ s in R₁..b, 3 * C / 2 * s ^ (1 - α) :=
          integral_mono_on hb (hψint R₁ b hR₁r₀ hb) ((hpowint R₁ b hR₁0 hb).const_mul _)
            fun s hs => (hψb s hs.1).2
      _ = 3 * C / 2 * ((b ^ (2 - α) - R₁ ^ (2 - α)) / (2 - α)) := by
          rw [intervalIntegral.integral_const_mul, hpow R₁ b hR₁0 hb]
      _ ≤ 3 * C / 2 * (R₁ ^ (2 - α) / (α - 2)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have : 0 ≤ b ^ (2 - α) := Real.rpow_nonneg (hR₁0.trans_le hb).le _
          have h1 : (2 : ℝ) - α ≠ 0 := by linarith
          have h1' : α - 2 ≠ 0 := by linarith
          have h2 : (b ^ (2 - α) - R₁ ^ (2 - α)) / (2 - α) =
              (R₁ ^ (2 - α) - b ^ (2 - α)) / (α - 2) := by
            field_simp
            ring
          rw [h2]
          exact div_le_div_of_nonneg_right (by linarith) (by linarith)
  -- the limit
  set f : ℝ → ℝ := fun r => U (max r R₁) with hf
  have hfmono : Monotone f := fun a b hab =>
    hmono _ _ (hR₁r₀.trans (le_max_right _ _)) (max_le_max hab le_rfl)
  have hfbdd : BddAbove (range f) := ⟨U R₁ + 3 * C / 2 * (R₁ ^ (2 - α) / (α - 2)),
    by rintro _ ⟨r, rfl⟩; exact hbdd _ (le_max_right _ _)⟩
  set Uinf := ⨆ r, f r with hUinf
  have hflim : Tendsto f atTop (𝓝 Uinf) := tendsto_atTop_ciSup hfmono hfbdd
  have hUlim : Tendsto U atTop (𝓝 Uinf) := hflim.congr' (by
    filter_upwards [eventually_ge_atTop R₁] with r hr
    simp only [hf, max_eq_left hr])
  -- `U_∞ > 0`
  have hUR₁ : 0 ≤ U R₁ := by
    have h := hSU R₁ hR₁r₀
    have hpos : 0 < R₁ ^ (2 * α) * Real.exp (∫ s in r₀..R₁, e s) := by positivity
    have := hS0 R₁ hR₁r₀
    rw [h] at this
    exact nonneg_of_mul_nonneg_left this hpos
  have hUinf0 : 0 < Uinf := by
    have h1 : U (R₁ + 1) ≤ Uinf := by
      have := le_ciSup hfbdd (R₁ + 1)
      simpa [hf, max_eq_left (by linarith : R₁ ≤ R₁ + 1)] using this
    have h2 : 0 < ∫ s in R₁..R₁ + 1, ψ s := by
      calc (0 : ℝ) < ∫ s in R₁..R₁ + 1, C / 2 * s ^ (1 - α) := by
            rw [intervalIntegral.integral_const_mul]
            refine mul_pos (by positivity) (intervalIntegral_pos_of_pos_on
              (hpowint R₁ (R₁ + 1) hR₁0 (by linarith)) (fun s hs => ?_) (by linarith))
            exact Real.rpow_pos_of_pos (hR₁0.trans hs.1) _
        _ ≤ ∫ s in R₁..R₁ + 1, ψ s :=
            integral_mono_on (by linarith) ((hpowint R₁ (R₁ + 1) hR₁0 (by linarith)).const_mul _)
              (hψint R₁ (R₁ + 1) hR₁r₀ (by linarith)) fun s hs => (hψb s hs.1).1
    have := hUint R₁ (R₁ + 1) hR₁r₀ (by linarith)
    linarith
  -- assembling
  refine ⟨Uinf * Real.exp (∫ s in Ioi r₀, e s), by positivity, isEquivalent_of_tendsto_one ?_⟩
  have hlim := (hUlim.mul ((Real.continuous_exp.tendsto _).comp hE)).div_const
    (Uinf * Real.exp (∫ s in Ioi r₀, e s))
  rw [div_self (by positivity)] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop r₀] with r hr
  have hr0 : 0 < r := hr₀0.trans_le hr
  have : 0 < r ^ (2 * α) := Real.rpow_pos_of_pos hr0 _
  simp only [Function.comp_apply, Pi.div_apply]
  rw [hSU r hr]
  field_simp

end Core

/-! ### The ratio `√(S/m)` -/

/-- If `S ~ T`, `m ~ m₀ r^α`, and `T/(m₀ r^α) = K W²` eventually with `K > 0` and `W > 0`,
then `√(S/m) ≍ W`. -/
theorem isTheta_sqrt_div {S m T W : ℝ → ℝ} {m₀ α K : ℝ} (hS : S ~[atTop] T)
    (hm : m ~[atTop] fun r => m₀ * r ^ α) (hK : 0 < K)
    (hT : ∀ᶠ r in atTop, T r / (m₀ * r ^ α) = K * W r ^ 2) (hW : ∀ᶠ r in atTop, 0 < W r) :
    (fun r => Real.sqrt (S r / m r)) =Θ[atTop] W := by
  have h1 : (fun r => S r / m r) ~[atTop] fun r => K * W r ^ 2 :=
    (hS.div hm).congr_right hT
  have hv : ∀ᶠ r in atTop, 0 < K * W r ^ 2 := by
    filter_upwards [hW] with r hr
    positivity
  have h2 : Tendsto (fun r => (S r / m r) / (K * W r ^ 2)) atTop (𝓝 1) :=
    (isEquivalent_iff_tendsto_one (hv.mono fun r hr => hr.ne')).1 h1
  have h3 : (fun r => Real.sqrt (S r / m r)) ~[atTop] fun r => Real.sqrt K * W r := by
    refine isEquivalent_of_tendsto_one ?_
    have := (Real.continuous_sqrt.tendsto 1).comp h2
    rw [Real.sqrt_one] at this
    refine this.congr' ?_
    filter_upwards [hW] with r hr
    simp only [Function.comp_apply, Pi.div_apply]
    rw [Real.sqrt_div' _ (by positivity), Real.sqrt_mul hK.le, Real.sqrt_sq hr.le]
  exact h3.isTheta.trans ((isTheta_refl W atTop).const_mul_left (Real.sqrt_pos.2 hK).ne')

section Ratio

variable {α c r₀ m₀ : ℝ} {S e g m : ℝ → ℝ}

/-- **Ratio, `α < 2`.** If moreover `m ~ m₀ r^α` with `m₀ > 0`, then `√(S/m) ≍ r`. -/
theorem isTheta_sqrt_linearODE_lt (hr₀ : 1 ≤ r₀) (hα2 : α < 2) (hc : 0 < c)
    (hSac : ∀ R, r₀ ≤ R → AbsolutelyContinuousOnInterval S r₀ R)
    (hder : ∀ᵐ r, r₀ ≤ r → deriv S r = (2 * α / r + e r) * S r + g r)
    (he : IntegrableOn e (Ici r₀)) (hg0 : ∀ r, r₀ ≤ r → 0 ≤ g r)
    (hg : g ~[atTop] fun r => c * r ^ (α + 1)) (hm₀ : 0 < m₀)
    (hm : m ~[atTop] fun r => m₀ * r ^ α) :
    (fun r => Real.sqrt (S r / m r)) =Θ[atTop] fun r => r := by
  have h2α : 0 < 2 - α := by linarith
  refine isTheta_sqrt_div (isEquivalent_linearODE_lt hr₀ hα2 hc hSac hder he hg0 hg) hm
    (K := c / ((2 - α) * m₀)) (by positivity) ?_ (eventually_gt_atTop 0)
  filter_upwards [eventually_gt_atTop 0] with r hr
  have : 0 < r ^ α := Real.rpow_pos_of_pos hr _
  rw [Real.rpow_add hr, Real.rpow_two]
  field_simp

/-- **Ratio, `α = 2`.** If moreover `m ~ m₀ r^α` with `m₀ > 0`, then
`√(S/m) ≍ r √(log r)`. -/
theorem isTheta_sqrt_linearODE_eq (hr₀ : 1 ≤ r₀) (hα2 : α = 2) (hc : 0 < c)
    (hSac : ∀ R, r₀ ≤ R → AbsolutelyContinuousOnInterval S r₀ R)
    (hder : ∀ᵐ r, r₀ ≤ r → deriv S r = (2 * α / r + e r) * S r + g r)
    (he : IntegrableOn e (Ici r₀)) (hg0 : ∀ r, r₀ ≤ r → 0 ≤ g r)
    (hg : g ~[atTop] fun r => c * r ^ (α + 1)) (hm₀ : 0 < m₀)
    (hm : m ~[atTop] fun r => m₀ * r ^ α) :
    (fun r => Real.sqrt (S r / m r)) =Θ[atTop] fun r => r * Real.sqrt (Real.log r) := by
  refine isTheta_sqrt_div (isEquivalent_linearODE_eq hr₀ hα2 hc hSac hder he hg0 hg) hm
    (K := c / m₀) (by positivity) ?_ ?_
  · filter_upwards [eventually_gt_atTop 1] with r hr
    have hr0 : 0 < r := by linarith
    have hl : 0 < Real.log r := Real.log_pos hr
    rw [hα2, mul_pow, Real.sq_sqrt hl.le,
      show (4 : ℝ) = (2 : ℕ) + (2 : ℕ) by norm_num, Real.rpow_add hr0, Real.rpow_natCast]
    have : 0 < r ^ 2 := by positivity
    field_simp
    norm_cast
  · filter_upwards [eventually_gt_atTop 1] with r hr
    have := Real.sqrt_pos.2 (Real.log_pos hr)
    have : 0 < r := by linarith
    positivity

/-- **Ratio, `α > 2`.** If moreover `m ~ m₀ r^α` with `m₀ > 0`, then
`√(S/m) ≍ r^{α/2}`. -/
theorem isTheta_sqrt_linearODE_gt (hr₀ : 1 ≤ r₀) (hα2 : 2 < α) (hc : 0 < c)
    (hS0 : ∀ r, r₀ ≤ r → 0 ≤ S r)
    (hSac : ∀ R, r₀ ≤ R → AbsolutelyContinuousOnInterval S r₀ R)
    (hder : ∀ᵐ r, r₀ ≤ r → deriv S r = (2 * α / r + e r) * S r + g r)
    (he : IntegrableOn e (Ici r₀)) (hg0 : ∀ r, r₀ ≤ r → 0 ≤ g r)
    (hg : g ~[atTop] fun r => c * r ^ (α + 1)) (hm₀ : 0 < m₀)
    (hm : m ~[atTop] fun r => m₀ * r ^ α) :
    (fun r => Real.sqrt (S r / m r)) =Θ[atTop] fun r => r ^ (α / 2) := by
  obtain ⟨K, hK, hSK⟩ := exists_isEquivalent_linearODE_gt hr₀ hα2 hc hS0 hSac hder he hg0 hg
  refine isTheta_sqrt_div hSK hm (K := K / m₀) (by positivity) ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with r hr
    have : 0 < r ^ α := Real.rpow_pos_of_pos hr _
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le, show α / 2 * ((2 : ℕ) : ℝ) = α by
      push_cast; ring, show 2 * α = α + α by ring, Real.rpow_add hr]
    field_simp
  · filter_upwards [eventually_gt_atTop 0] with r hr
    exact Real.rpow_pos_of_pos hr _

end Ratio

/-! ### Non-vacuity: `e ≡ 0`, `g = r^{α+1}`, `r₀ = 1` -/

/-- `α = 1`: `S = r³` solves `S' = (2/r) S + r²`, and `isEquivalent_linearODE_lt` gives `S ~ r³`. -/
example : (fun r : ℝ => r ^ 3) ~[atTop] fun r => 1 * r ^ ((1 : ℝ) + 2) / (2 - 1) :=
  isEquivalent_linearODE_lt (r₀ := 1) (e := fun _ => 0) (g := fun r => 1 * r ^ ((1 : ℝ) + 1))
    le_rfl (by norm_num) one_pos
    (fun R _ => ContDiffOn.absolutelyContinuousOnInterval (contDiff_id.pow 3).contDiffOn)
    (Eventually.of_forall fun r hr => by
      have hr0 : r ≠ 0 := by linarith
      rw [show (1 : ℝ) + 1 = (2 : ℕ) by norm_num, Real.rpow_natCast]
      simp only [deriv_pow_field, add_zero]
      field_simp
      ring)
    integrableOn_zero (fun r hr => mul_nonneg zero_le_one (Real.rpow_nonneg (by linarith) _))
    IsEquivalent.refl

/-- `α = 2`: `S = r⁴ log r` solves `S' = (4/r) S + r³`, and `isEquivalent_linearODE_eq` gives
`S ~ r⁴ log r`. -/
example : (fun r : ℝ => r ^ 4 * Real.log r) ~[atTop] fun r => 1 * r ^ (4 : ℝ) * Real.log r :=
  isEquivalent_linearODE_eq (α := 2) (r₀ := 1) (e := fun _ => 0)
    (g := fun r => 1 * r ^ ((2 : ℝ) + 1)) le_rfl rfl one_pos
    (fun R hR => ContDiffOn.absolutelyContinuousOnInterval fun r hr => by
      rw [uIcc_of_le hR] at hr
      have hr0 : r ≠ 0 := by linarith [hr.1]
      exact ((contDiffAt_id.pow 4).mul (Real.contDiffAt_log.2 hr0)).contDiffWithinAt)
    (Eventually.of_forall fun r hr => by
      have hr0 : r ≠ 0 := by linarith
      have hd := ((hasDerivAt_pow 4 r).mul (Real.hasDerivAt_log hr0))
      change deriv ((fun x : ℝ => x ^ 4) * Real.log) r = _
      rw [hd.deriv, show (2 : ℝ) + 1 = (3 : ℕ) by norm_num, Real.rpow_natCast]
      field_simp
      ring)
    integrableOn_zero (fun r hr => mul_nonneg zero_le_one (Real.rpow_nonneg (by linarith) _))
    IsEquivalent.refl

/-- `α = 3`: `S = r⁶ - r⁵ ≥ 0` solves `S' = (6/r) S + r⁴`, and `exists_isEquivalent_linearODE_gt`
gives `S ~ K r⁶` with `K > 0`. -/
example : ∃ K > 0, (fun r : ℝ => r ^ 6 - r ^ 5) ~[atTop] fun r => K * r ^ (2 * (3 : ℝ)) :=
  exists_isEquivalent_linearODE_gt (α := 3) (r₀ := 1) (e := fun _ => 0)
    (g := fun r => 1 * r ^ ((3 : ℝ) + 1)) le_rfl (by norm_num) one_pos
    (fun r hr => by
      have : r ^ 5 ≤ r ^ 6 := pow_le_pow_right₀ hr (by norm_num)
      linarith)
    (fun R _ => ContDiffOn.absolutelyContinuousOnInterval
      ((contDiff_id.pow 6).sub (contDiff_id.pow 5)).contDiffOn)
    (Eventually.of_forall fun r hr => by
      have hr0 : r ≠ 0 := by linarith
      have hd := (hasDerivAt_pow 6 r).sub (hasDerivAt_pow 5 r)
      change deriv ((fun x : ℝ => x ^ 6) - fun x : ℝ => x ^ 5) r = _
      rw [hd.deriv, show (3 : ℝ) + 1 = (4 : ℕ) by norm_num, Real.rpow_natCast]
      field_simp
      ring)
    integrableOn_zero (fun r hr => mul_nonneg zero_le_one (Real.rpow_nonneg (by linarith) _))
    IsEquivalent.refl

end PercLib.Analysis
