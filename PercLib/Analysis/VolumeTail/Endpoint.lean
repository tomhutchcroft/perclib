/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
The moment endpoint `a ≥ 1` of Proposition I.3.2 of T. Hutchcroft, *Critical long-range
percolation I: High effective dimension*, arXiv:2508.18807v1, §I.3.2, and the resulting
Tauberian step (I.3.2) ⟹ (I.3.3) with the domain condition `1 / a ≤ 1` discharged.

Adapted from the repository `yujinhkim/lrp`, branch `critical-lrp-1`, commit
`d382e4c28d92dd4e698ebf4f2aaf0bc932ae73fc`, file
`PercLib/CriticalLRP/Analysis/I32Endpoint.lean`; licence Apache-2.0 as declared in that
commit's file headers and `third_party/critical-lrp/NOTICE.md`; upstream
`yujinhkim/Critical-Long-range-percolation` at `3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf`.
Modified: `RegularlyVaryingAtTop f ρ` becomes `RegularlyVarying ρ f` of
`PercLib/Analysis/RegularVariation/Defs.lean`; the source's `mean`, `secMoment` and `sbMean` are
written out; Jensen's inequality is taken from mathlib's variance (`variance_eq_sub`); the
Potter argument of `tendsto_div_rpow_zero_of_regularlyVarying` is replaced by the decay of a
regularly varying function of negative index (`RegularlyVarying.tendsto_nhds_zero_of_neg`),
which needs no measurability; the hypotheses `Measurable f`, `Measurable g`,
`∀ᶠ x in atTop, 0 < g x`, the support hypothesis on the moment laws and the first-moment
integrability are removed (unused); `sbMean_nonneg`, `A3const_at_one` and `A4const_at_one` are
not ported (one-line consequences of `div_nonneg`, `Real.rpow_one` and `Real.Gamma_one` once
the definitions are written out); declarations are renamed; `import Mathlib`, `autoImplicit`,
disabled linters and `#print` lines are removed.
-/
module

public import PercLib.Analysis.VolumeTail.Normalizer
public import Mathlib.Probability.Moments.Variance

/-! # The moment endpoint of Proposition I.3.2

For a probability law on `ℝ` with finite second moment and positive mean, Jensen's inequality
gives `E X ≤ E X² / E X`. Consequently hypotheses 1 and 2 of Proposition I.3.2
(`E_r X ~ A₁ r^α`, `E_r X² / E_r X ~ A₂ f(r)` with `f` regularly varying of index `a α`) force
`a ≥ 1`, which is the domain `1 / a ≤ 1` of the Tauberian step.

## Main results

* `integral_id_le_integral_sq_div`: `E X ≤ E X² / E X`.
* `RegularlyVarying.tendsto_nhds_zero_of_neg`, `RegularlyVarying.tendsto_div_rpow_nhds_zero`:
  a regularly varying function of negative index tends to `0`; `f x / x^σ → 0` above the index.
* `one_le_of_tendsto_div_of_tendsto_div`: hypotheses 1 and 2 force `a ≥ 1`.
* `tendsto_measure_Ici_div_of_tendsto_laplace_div_of_moments`: (I.3.3) from (I.3.2) and
  hypotheses 1 and 2, with `1 / a ≤ 1` derived.

These are analytic steps of the proof of Proposition I.3.2, not that proposition.
-/

@[expose] public section

open Filter Set MeasureTheory ProbabilityTheory
open scoped Topology

namespace PercLib.Analysis

/-! ### The size-biased mean dominates the mean -/

/-- **`E X ≤ E X² / E X`** for a probability law on `ℝ` with `E X² < ∞` and `E X > 0`
(Jensen's inequality for `t ↦ t²`). -/
theorem integral_id_le_integral_sq_div {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (h2 : Integrable (fun x : ℝ => x ^ 2) μ) (hpos : 0 < ∫ x, x ∂μ) :
    ∫ x, x ∂μ ≤ (∫ x, x ^ 2 ∂μ) / ∫ x, x ∂μ := by
  have hX : MemLp (fun x : ℝ => x) 2 μ :=
    (memLp_two_iff_integrable_sq aestronglyMeasurable_id).2 h2
  have hvar := variance_eq_sub hX
  have h0 := variance_nonneg (fun x : ℝ => x) μ
  rw [hvar] at h0
  rw [le_div_iff₀ hpos]
  simp only [Pi.pow_apply] at h0
  nlinarith

/-! ### Regular variation of negative index -/

/-- **A regularly varying function of negative index tends to `0`.** -/
theorem RegularlyVarying.tendsto_nhds_zero_of_neg {f : ℝ → ℝ} {ρ : ℝ} (hρ : ρ < 0)
    (hf : RegularlyVarying ρ f) : Tendsto f atTop (𝓝 0) := by
  have h := (hf.inv.tendsto_atTop' (neg_pos.2 hρ)).inv_tendsto_atTop
  refine h.congr' ?_
  filter_upwards [hf.eventually_pos] with x _
  simp

/-- **A regularly varying function is `o(x^σ)` above its index**: if `f` is regularly varying of
index `ρ < σ`, then `f x / x^σ → 0`. -/
theorem RegularlyVarying.tendsto_div_rpow_nhds_zero {f : ℝ → ℝ} {ρ σ : ℝ} (hσ : ρ < σ)
    (hf : RegularlyVarying ρ f) : Tendsto (fun x => f x / x ^ σ) atTop (𝓝 0) := by
  refine ((hf.mul (regularlyVarying_rpow (-σ))).tendsto_nhds_zero_of_neg (by linarith)).congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [Real.rpow_neg hx.le, div_eq_mul_inv]

/-! ### The endpoint `a ≥ 1` -/

/-- **Hypotheses 1 and 2 of Proposition I.3.2 force `a ≥ 1`.** Let `ψ r / (A₁ r^α) → 1` and
`φ r / (A₂ f r) → 1` with `A₁, A₂, α, a > 0`, `f` regularly varying of index `a α`, and
`ψ ≤ φ` eventually (true for the mean and the size-biased mean of a law, by
`integral_id_le_integral_sq_div`). Then `1 ≤ a`: otherwise `A₂ f r ≳ φ r ≥ ψ r ≳ A₁ r^α`
contradicts `f r / r^α → 0`. -/
theorem one_le_of_tendsto_div_of_tendsto_div {f ψ φ : ℝ → ℝ} {A₁ A₂ α a : ℝ}
    (hA₁ : 0 < A₁) (hA₂ : 0 < A₂) (hα : 0 < α) (hf : RegularlyVarying (a * α) f)
    (hge : ∀ᶠ r in atTop, ψ r ≤ φ r)
    (h1 : Tendsto (fun r => ψ r / (A₁ * r ^ α)) atTop (𝓝 1))
    (h2 : Tendsto (fun r => φ r / (A₂ * f r)) atTop (𝓝 1)) :
    1 ≤ a := by
  by_contra hcon
  push Not at hcon
  have hidx : a * α < α := by nlinarith
  have hdecay := hf.tendsto_div_rpow_nhds_zero hidx
  have hψlow : ∀ᶠ r in atTop, A₁ / 2 * r ^ α ≤ ψ r := by
    filter_upwards [h1.eventually (eventually_gt_nhds (by norm_num : (1 / 2 : ℝ) < 1)),
      eventually_gt_atTop (0 : ℝ)] with r hr hrpos
    have hden : 0 < A₁ * r ^ α := mul_pos hA₁ (Real.rpow_pos_of_pos hrpos α)
    rw [lt_div_iff₀ hden] at hr
    linarith
  have hφup : ∀ᶠ r in atTop, φ r ≤ 2 * A₂ * f r := by
    filter_upwards [h2.eventually (eventually_lt_nhds (by norm_num : (1 : ℝ) < 2)),
      hf.eventually_pos] with r hr hfr
    rw [div_lt_iff₀ (mul_pos hA₂ hfr)] at hr
    linarith
  have hlow : ∀ᶠ r in atTop, A₁ / (4 * A₂) ≤ f r / r ^ α := by
    filter_upwards [hψlow, hφup, hge, eventually_gt_atTop (0 : ℝ)] with r h1r h2r h3r hrpos
    have hrα : 0 < r ^ α := Real.rpow_pos_of_pos hrpos α
    rw [le_div_iff₀ hrα, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  obtain ⟨r, hr1, hr2⟩ := (hlow.and (hdecay.eventually (gt_mem_nhds (by positivity :
    (0 : ℝ) < A₁ / (4 * A₂))))).exists
  linarith

/-- **(I.3.3) from (I.3.2) and hypotheses 1 and 2 of Proposition I.3.2**, with the Tauberian
domain `1 / a ≤ 1` derived. Let `μ_r` be probability laws with `E_r X² < ∞`, `E_r X > 0`,
`E_r X / (A₁ r^α) → 1` and `(E_r X² / E_r X) / (A₂ f r) → 1` for `f` regularly varying of index
`a α`. If `g` is regularly varying of index `1 / (a α)`, `A₃ ≠ 0`, and the law `μ` on `[0, ∞)`
satisfies `E_μ[1 - e^{-hX}] / (A₃ g(1/h)^α h) → 1` as `h ↓ 0`, then
`μ([x, ∞)) / ((A₃ / Γ(1/a)) g(x)^α / x) → 1`. -/
theorem tendsto_measure_Ici_div_of_tendsto_laplace_div_of_moments (mu : ℝ → Measure ℝ)
    (hmu : ∀ r, IsProbabilityMeasure (mu r))
    (hint2 : ∀ r, Integrable (fun x : ℝ => x ^ 2) (mu r)) (hEpos : ∀ r, 0 < ∫ x, x ∂mu r)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : μ (Iio 0) = 0)
    {a α A₁ A₂ A₃ : ℝ} (hA₁ : 0 < A₁) (hA₂ : 0 < A₂) (hα : 0 < α) (ha : 0 < a)
    {f : ℝ → ℝ} (hf : RegularlyVarying (a * α) f)
    (h1 : Tendsto (fun r => (∫ x, x ∂mu r) / (A₁ * r ^ α)) atTop (𝓝 1))
    (h2 : Tendsto (fun r => (∫ x, x ^ 2 ∂mu r) / (∫ x, x ∂mu r) / (A₂ * f r)) atTop (𝓝 1))
    {g : ℝ → ℝ} (hg : RegularlyVarying (1 / (a * α)) g) (hA₃ : A₃ ≠ 0)
    (hmain : Tendsto (fun h : ℝ =>
      (∫ s, (1 - Real.exp (-(h * s))) ∂μ) / (A₃ * (g (1 / h) ^ α * h)))
      (𝓝[>] (0 : ℝ)) (𝓝 1)) :
    Tendsto (fun x : ℝ => (μ (Ici x)).toReal /
      ((A₃ / Real.Gamma (1 / a)) * (g x ^ α / x))) atTop (𝓝 1) := by
  have hge : ∀ᶠ r in atTop, (∫ x, x ∂mu r) ≤ (∫ x, x ^ 2 ∂mu r) / ∫ x, x ∂mu r :=
    Eventually.of_forall fun r => integral_id_le_integral_sq_div (hint2 r) (hEpos r)
  have hone := one_le_of_tendsto_div_of_tendsto_div hA₁ hA₂ hα hf hge h1 h2
  have ha1 : 1 / a ≤ 1 := by
    rw [div_le_one ha]
    exact hone
  exact tendsto_measure_Ici_div_of_tendsto_laplace_div μ hμ ha hα ha1 hg hA₃ hmain

end PercLib.Analysis
