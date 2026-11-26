/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-21, against pinned mathlib. No upstream proof is copied.
-/
module

public import PercLib.Analysis.LogarithmicCorrections
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Riccati propagation with a linear error term

Let `f > 0` be absolutely continuous on `[r, R]` with `0 < r` and
`f' ≤ A t^{-α-1} f² + e t⁻¹ f` almost everywhere. Then `t ↦ t^e / f t` is absolutely
continuous with derivative at least `-A t^{e-α-1}`, and integrating gives a lower bound for
`R^e / f R`. Below the threshold `f r ≤ (α - e) r^α / A` this yields an upper bound for `f R`.

## Main results

* `rpow_div_sub_le_rpow_div_of_deriv_le`: the integrated inequality
  `r^e / f r - A/(α - e) (r^{e-α} - R^{e-α}) ≤ R^e / f R`.
* `one_div_sub_add_mul_rpow_pos`: positivity of the bracket below the threshold.
* `le_rpow_mul_inv_of_deriv_le_mul_sq_add`: the bound `f R ≤ (R/r)^e B(R)⁻¹`.
* `le_inv_mul_rpow_mul_of_deriv_le_mul_sq_add`: `f R ≤ θ⁻¹ (R/r)^e f r` under the stronger
  threshold `f r ≤ (1 - θ)(α - e) r^α / A`.

No definition is introduced.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Real intervalIntegral

namespace PercLib.Analysis

/-- **Integrated inequality.** Let `0 < r ≤ R`, `e ≠ α`, and let `f > 0` be absolutely
continuous on `[r, R]` with `f' ≤ A t^{-α-1} f² + e t⁻¹ f` a.e. there. Then
`r^e / f r - A/(α - e) (r^{e-α} - R^{e-α}) ≤ R^e / f R`. -/
theorem rpow_div_sub_le_rpow_div_of_deriv_le {f : ℝ → ℝ} {α A e r R : ℝ} (hr : 0 < r)
    (hrR : r ≤ R) (he : e ≠ α) (hf : AbsolutelyContinuousOnInterval f r R)
    (hpos : ∀ t ∈ Icc r R, 0 < f t)
    (hder : ∀ᵐ t, t ∈ Icc r R →
      deriv f t ≤ A * t ^ (-α - 1) * f t ^ 2 + e * t⁻¹ * f t) :
    r ^ e / f r - A / (α - e) * (r ^ (e - α) - R ^ (e - α)) ≤ R ^ e / f R := by
  have hI : uIcc r R = Icc r R := uIcc_of_le hrR
  have hmem : ∀ x ∈ uIcc r R, 0 < x := fun x hx => hr.trans_le (by rw [hI] at hx; exact hx.1)
  have hpowAC : AbsolutelyContinuousOnInterval (fun t => t ^ e) r R :=
    ContDiffOn.absolutelyContinuousOnInterval
      (contDiffOn_id.rpow_const_of_ne fun x hx => (hmem x hx).ne')
  have hg : AbsolutelyContinuousOnInterval (fun t => t ^ e / f t) r R := by
    simpa only [div_eq_mul_inv] using
      hpowAC.fun_mul (absolutelyContinuousOnInterval_inv hrR hf hpos)
  have hderg : ∀ᵐ t, t ∈ Icc r R →
      -A * t ^ (e - α - 1) ≤ deriv (fun t => t ^ e / f t) t := by
    filter_upwards [hf.ae_differentiableAt, hder] with t hd hb ht
    have ht0 : 0 < t := hr.trans_le ht.1
    have hft := hpos t ht
    have hd' := (hd (hI ▸ ht)).hasDerivAt
    have h2 := (hasDerivAt_rpow_const (p := e) (Or.inl ht0.ne')).div hd' hft.ne'
    rw [show (fun t => t ^ e / f t) = (fun x => x ^ e) / f from rfl, h2.deriv,
      le_div_iff₀ (by positivity)]
    have e1 : t ^ e * t ^ (-α - 1) = t ^ (e - α - 1) := by
      rw [← rpow_add ht0]
      congr 1
      ring
    have e2 : t ^ e * t⁻¹ = t ^ (e - 1) := by rw [rpow_sub_one ht0.ne', div_eq_mul_inv]
    have hte : 0 ≤ t ^ e := (rpow_pos_of_pos ht0 e).le
    have h3 := mul_le_mul_of_nonneg_left (hb ht) hte
    have h4 : t ^ e * (A * t ^ (-α - 1) * f t ^ 2 + e * t⁻¹ * f t) =
        A * t ^ (e - α - 1) * f t ^ 2 + e * t ^ (e - 1) * f t := by
      rw [← e1, ← e2]
      ring
    linarith
  have h0 : (0 : ℝ) ∉ uIcc r R := fun h => (lt_irrefl 0) (hmem 0 h)
  have hcont : IntervalIntegrable (fun t => -A * t ^ (e - α - 1)) volume r R :=
    ContinuousOn.intervalIntegrable (continuousOn_const.mul
      (ContinuousOn.rpow_const continuousOn_id fun s hs => Or.inl (hmem s hs).ne'))
  have hint := integral_le_sub_of_ae_le_deriv hrR hg hcont hderg
  have hne : e - α - 1 ≠ -1 := fun h => he (by linarith)
  rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inr ⟨hne, h0⟩)] at hint
  have hsub : e - α - 1 + 1 = e - α := by ring
  rw [hsub] at hint
  have h1 : (e - α) ≠ 0 := sub_ne_zero.2 he
  have h2 : (α - e) ≠ 0 := sub_ne_zero.2 he.symm
  have key : -A * ((R ^ (e - α) - r ^ (e - α)) / (e - α)) =
      -(A / (α - e) * (r ^ (e - α) - R ^ (e - α))) := by
    field_simp
    ring
  linarith

/-- **Positivity of the bracket.** If `e < α`, `A, r, R, x > 0` and `x ≤ (α - e) r^α / A`,
then `1/x - A/((α - e) r^α) + A/((α - e) r^α) (r/R)^{α-e} > 0`. -/
theorem one_div_sub_add_mul_rpow_pos {α A e r R x : ℝ} (heα : e < α) (hA : 0 < A)
    (hr : 0 < r) (hR : 0 < R) (hx : 0 < x) (hxr : x ≤ (α - e) * r ^ α / A) :
    0 < 1 / x - A / ((α - e) * r ^ α) + A / ((α - e) * r ^ α) * (r / R) ^ (α - e) := by
  have hden : 0 < (α - e) * r ^ α := mul_pos (by linarith) (rpow_pos_of_pos hr α)
  rw [le_div_iff₀ hA] at hxr
  have h1 : A / ((α - e) * r ^ α) ≤ 1 / x := by
    rw [div_le_div_iff₀ hden hx]
    linarith
  have h2 : 0 < A / ((α - e) * r ^ α) * (r / R) ^ (α - e) :=
    mul_pos (div_pos hA hden) (rpow_pos_of_pos (div_pos hr hR) _)
  linarith

/-- **Subthreshold Riccati propagation.** Let `e < α`, `A > 0`, `0 < r ≤ R`, and let `f > 0`
be absolutely continuous on `[r, R]` with `f' ≤ A t^{-α-1} f² + e t⁻¹ f` a.e. there. If
`f r ≤ (α - e) r^α / A`, then
`f R ≤ (R/r)^e (1/f r - A/((α - e) r^α) + A/((α - e) r^α) (r/R)^{α-e})⁻¹`. -/
theorem le_rpow_mul_inv_of_deriv_le_mul_sq_add {f : ℝ → ℝ} {α A e r R : ℝ} (heα : e < α)
    (hA : 0 < A) (hr : 0 < r) (hrR : r ≤ R) (hf : AbsolutelyContinuousOnInterval f r R)
    (hpos : ∀ t ∈ Icc r R, 0 < f t)
    (hder : ∀ᵐ t, t ∈ Icc r R →
      deriv f t ≤ A * t ^ (-α - 1) * f t ^ 2 + e * t⁻¹ * f t)
    (hfr : f r ≤ (α - e) * r ^ α / A) :
    f R ≤ (R / r) ^ e *
      (1 / f r - A / ((α - e) * r ^ α) + A / ((α - e) * r ^ α) * (r / R) ^ (α - e))⁻¹ := by
  have hR : 0 < R := hr.trans_le hrR
  have hfr0 := hpos r ⟨le_rfl, hrR⟩
  have hfR0 := hpos R ⟨hrR, le_rfl⟩
  have hB := one_div_sub_add_mul_rpow_pos heα hA hr hR hfr0 hfr
  set B := 1 / f r - A / ((α - e) * r ^ α) + A / ((α - e) * r ^ α) * (r / R) ^ (α - e)
  have hint := rpow_div_sub_le_rpow_div_of_deriv_le hr hrR heα.ne hf hpos hder
  have hre : 0 < r ^ e := rpow_pos_of_pos hr e
  have hrα : 0 < r ^ α := rpow_pos_of_pos hr α
  have hRe : 0 < R ^ e := rpow_pos_of_pos hR e
  have hRα : 0 < R ^ α := rpow_pos_of_pos hR α
  have hαe : α - e ≠ 0 := sub_ne_zero.2 heα.ne'
  have heq : r ^ e * B = r ^ e / f r - A / (α - e) * (r ^ (e - α) - R ^ (e - α)) := by
    simp only [B, rpow_sub hr, rpow_sub hR, div_rpow hr.le hR.le]
    field_simp
    ring
  rw [← heq, le_div_iff₀ hfR0] at hint
  rw [div_rpow hR.le hr.le, div_mul_eq_mul_div, le_div_iff₀ hre, ← div_eq_mul_inv,
    le_div_iff₀ hB]
  linarith [show f R * r ^ e * B = r ^ e * B * f R by ring]

/-- **Subthreshold propagation with a margin.** Under the hypotheses of
`le_rpow_mul_inv_of_deriv_le_mul_sq_add`, if `0 < θ` and
`f r ≤ (1 - θ)(α - e) r^α / A`, then `f R ≤ θ⁻¹ (R/r)^e f r`. -/
theorem le_inv_mul_rpow_mul_of_deriv_le_mul_sq_add {f : ℝ → ℝ} {α A e r R θ : ℝ}
    (heα : e < α) (hA : 0 < A) (hr : 0 < r) (hrR : r ≤ R)
    (hf : AbsolutelyContinuousOnInterval f r R) (hpos : ∀ t ∈ Icc r R, 0 < f t)
    (hder : ∀ᵐ t, t ∈ Icc r R →
      deriv f t ≤ A * t ^ (-α - 1) * f t ^ 2 + e * t⁻¹ * f t)
    (hθ0 : 0 < θ) (hfr : f r ≤ (1 - θ) * (α - e) * r ^ α / A) :
    f R ≤ θ⁻¹ * (R / r) ^ e * f r := by
  have hR : 0 < R := hr.trans_le hrR
  have hfr0 := hpos r ⟨le_rfl, hrR⟩
  have hden : 0 < (α - e) * r ^ α := mul_pos (by linarith) (rpow_pos_of_pos hr α)
  have hfr' : f r ≤ (α - e) * r ^ α / A := by
    refine hfr.trans (div_le_div_of_nonneg_right ?_ hA.le)
    nlinarith
  have hmain := le_rpow_mul_inv_of_deriv_le_mul_sq_add heα hA hr hrR hf hpos hder hfr'
  have hB := one_div_sub_add_mul_rpow_pos heα hA hr hR hfr0 hfr'
  set B := 1 / f r - A / ((α - e) * r ^ α) + A / ((α - e) * r ^ α) * (r / R) ^ (α - e)
  have h1 : A / ((α - e) * r ^ α) ≤ (1 - θ) / f r := by
    rw [div_le_div_iff₀ hden hfr0]
    rw [le_div_iff₀ hA] at hfr
    linarith
  have h2 : 0 < A / ((α - e) * r ^ α) * (r / R) ^ (α - e) :=
    mul_pos (div_pos hA hden) (rpow_pos_of_pos (div_pos hr hR) _)
  have hθB : θ / f r ≤ B := by
    have : θ / f r = 1 / f r - (1 - θ) / f r := by ring
    simp only [B]
    linarith
  have hBinv : B⁻¹ ≤ f r / θ := by
    rw [← inv_div]
    exact inv_anti₀ (div_pos hθ0 hfr0) hθB
  have hq : 0 ≤ (R / r) ^ e := (rpow_pos_of_pos (div_pos hR hr) e).le
  calc f R ≤ (R / r) ^ e * B⁻¹ := hmain
    _ ≤ (R / r) ^ e * (f r / θ) := mul_le_mul_of_nonneg_left hBinv hq
    _ = θ⁻¹ * (R / r) ^ e * f r := by ring

end PercLib.Analysis
