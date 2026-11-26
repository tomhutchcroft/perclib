/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
The constants `A₃`, `A₄` of Proposition I.3.2 for the chi-square limit law, for T. Hutchcroft,
*Critical long-range percolation I*, arXiv:2508.18807v1, Proposition I.3.2 and the proof of
(I.1.7), p. 32.

Ported from the repository `yujinhkim/lrp`, branch `critical-lrp-1`, commit
`d382e4c28d92dd4e698ebf4f2aaf0bc932ae73fc`, file
`PercLib/CriticalLRP/Analysis/ChiSquareA3.lean`; licence Apache-2.0 as declared in that
commit's file headers and `third_party/critical-lrp/NOTICE.md`; upstream
`yujinhkim/Critical-Long-range-percolation` at `3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf`.
Modified: the source's `Qinf` (the law of `Z²`, `Z` standard normal) is the chi-square law
`gammaMeasure (1/2) (1/2)` of `PercLib/Probability/ChiSquareDeterminacy.lean`; the Gaussian
half-moment, the layer-cake identity and the evaluation `√(1 + 2λ) - 1` of the source are
replaced by `integral_exp_neg_mul_gammaMeasure_one_half`,
`integral_one_sub_exp_neg_mul_div_eq` and `integral_one_sub_exp_neg_mul_div_gammaMeasure_one_half`
of `PercLib/Probability/ChiSquareMoments.lean`, and the elementary limit
`tendsto_sqrt_inv_mul_sub_one` by `tendsto_sqrt_one_add_two_mul_sub_one_div_sqrt` there; the
definitions `A3const`, `A4const`, `A3chi`, `A4chi` are written out;
`hypotheses_three_four_nonvacuous` becomes `gammaMeasure_singleton` and an example;
`import Mathlib`, `autoImplicit`, disabled linters and `#print` lines are removed.
-/
module

public import PercLib.Probability.ChiSquareMoments

/-! # The constants of Proposition I.3.2 for the chi-square limit law

Proposition I.3.2 defines
`A₃ = (A₁ / A₂^{1/a}) lim_{λ→∞} λ^{-(a-1)/a} ∫ (1 - e^{-λx}) / x dQ_∞(x)` and
`A₄ = A₃ / Γ(1/a)`. In the proof of (I.1.7), `Q_∞` is the chi-square law with one degree of
freedom, `gammaMeasure (1/2) (1/2)`, and `a = 2`; the kernel integral is `√(1 + 2λ) - 1`
(`integral_one_sub_exp_neg_mul_div_gammaMeasure_one_half`).

## Main results

* `tendsto_rpow_mul_integral_chiSquare`: `λ^{-(2-1)/2} ∫ (1 - e^{-λx}) / x dQ_∞ → √2`; the
  normalised kernel tends to `0` for `a > 2` (`tendsto_rpow_mul_integral_chiSquare_of_two_lt`)
  and to `+∞` for `0 < a < 2` (`tendsto_rpow_mul_integral_chiSquare_of_lt_two`).
* `div_rpow_mul_sqrt_two_eq`, `div_rpow_mul_sqrt_two_div_Gamma_eq`: `A₃ = √2 A₁ / √A₂` and
  `A₄ = √2 A₁ / (√A₂ √π)` at `a = 2`; `div_rpow_mul_sqrt_two_pos`: both are positive.
* `tendsto_div_mul_sqrt_one_add_two_mul_sub_one`: the prefactor of (I.3.7) tends to `A₃`.
* `rpow_div_mul_rpow_mul_eq`, `rpow_rpow_div_eq_sqrt_inv`: scale selection and the tail
  exponent `n^{-1/2}` for `f(r) = r^{2α}`.
* `gammaMeasure_singleton`: a gamma law has no atoms (hypothesis (4) at `Q_∞`).
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Real
open scoped NNReal Topology

namespace PercLib.Analysis

open PercLib.Probability

/-- A gamma law has no atoms; in particular the chi-square law gives `{0}` measure `0`. -/
theorem gammaMeasure_singleton (a r x : ℝ) : gammaMeasure a r {x} = 0 :=
  withDensity_absolutelyContinuous _ _ (Real.volume_singleton)

/-! ### The `A₃` limit -/

/-- `√(2 + 1/λ) - (√λ)⁻¹ → √2`. -/
theorem tendsto_sqrt_two_add_inv_sub_sqrt_inv :
    Tendsto (fun lam : ℝ => √(2 + 1 / lam) - (√lam)⁻¹) atTop (𝓝 (√2)) := by
  have h1 : Tendsto (fun lam : ℝ => √(2 + 1 / lam)) atTop (𝓝 (√2)) := by
    refine continuous_sqrt.continuousAt.tendsto.comp ?_
    simpa using (tendsto_const_nhds (x := (2 : ℝ))).add (tendsto_inv_atTop_zero (𝕜 := ℝ))
  have h2 : Tendsto (fun lam : ℝ => (√lam)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_sqrt_atTop
  simpa using h1.sub h2

/-- `√(1 + 2λ) - 1 = √λ (√(2 + 1/λ) - (√λ)⁻¹)` for `λ > 0`. -/
theorem sqrt_one_add_two_mul_sub_one_eq {lam : ℝ} (hlam : 0 < lam) :
    √(1 + 2 * lam) - 1 = √lam * (√(2 + 1 / lam) - (√lam)⁻¹) := by
  have hl : √lam ≠ 0 := (Real.sqrt_pos.mpr hlam).ne'
  have hm : √lam * √(2 + 1 / lam) = √(1 + 2 * lam) := by
    rw [← Real.sqrt_mul hlam.le]
    congr 1
    field_simp
    ring
  rw [mul_sub, hm, mul_inv_cancel₀ hl]

/-- The normalised `A₃` kernel equals `λ^{1/a - 1/2} (√(2 + 1/λ) - (√λ)⁻¹)` for `λ > 0`. -/
theorem rpow_mul_integral_chiSquare_eventuallyEq {a : ℝ} (ha : a ≠ 0) :
    (fun lam : ℝ => lam ^ (-((a - 1) / a)) *
        ∫ x, (1 - exp (-(lam * x))) / x ∂gammaMeasure (1 / 2) (1 / 2)) =ᶠ[atTop]
      fun lam => lam ^ (1 / a - 1 / 2) * (√(2 + 1 / lam) - (√lam)⁻¹) := by
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with lam hlam
  rw [integral_one_sub_exp_neg_mul_div_gammaMeasure_one_half hlam.le,
      sqrt_one_add_two_mul_sub_one_eq hlam,
    ← mul_assoc, sqrt_eq_rpow, ← rpow_add hlam]
  congr 2
  field_simp
  ring

/-- **The `A₃` limit for the chi-square law** (`a = 2`): `λ^{-(2-1)/2} ∫ f_λ dQ_∞ → √2`. -/
theorem tendsto_rpow_mul_integral_chiSquare :
    Tendsto (fun lam : ℝ => lam ^ (-((2 - 1) / 2) : ℝ) *
        ∫ x, (1 - exp (-(lam * x))) / x ∂gammaMeasure (1 / 2) (1 / 2)) atTop (𝓝 (√2)) := by
  rw [tendsto_congr' (rpow_mul_integral_chiSquare_eventuallyEq two_ne_zero)]
  simpa using tendsto_sqrt_two_add_inv_sub_sqrt_inv

/-- **For `a > 2` the `A₃` limit is `0`** for the chi-square law. -/
theorem tendsto_rpow_mul_integral_chiSquare_of_two_lt {a : ℝ} (ha : 2 < a) :
    Tendsto (fun lam : ℝ => lam ^ (-((a - 1) / a)) *
        ∫ x, (1 - exp (-(lam * x))) / x ∂gammaMeasure (1 / 2) (1 / 2)) atTop (𝓝 0) := by
  have ha0 : 0 < a := by linarith
  rw [tendsto_congr' (rpow_mul_integral_chiSquare_eventuallyEq ha0.ne')]
  have hexp : 0 < 1 / 2 - 1 / a := by
    rw [sub_pos]
    exact one_div_lt_one_div_of_lt two_pos ha
  have hsmall : Tendsto (fun lam : ℝ => lam ^ (1 / a - 1 / 2)) atTop (𝓝 0) := by
    convert tendsto_rpow_neg_atTop hexp using 2
    ring_nf
  simpa using hsmall.mul tendsto_sqrt_two_add_inv_sub_sqrt_inv

/-- **For `0 < a < 2` the `A₃` kernel diverges** for the chi-square law. -/
theorem tendsto_rpow_mul_integral_chiSquare_of_lt_two {a : ℝ} (ha : 0 < a)
    (ha2 : a < 2) :
    Tendsto (fun lam : ℝ => lam ^ (-((a - 1) / a)) *
        ∫ x, (1 - exp (-(lam * x))) / x ∂gammaMeasure (1 / 2) (1 / 2)) atTop atTop := by
  rw [tendsto_congr' (rpow_mul_integral_chiSquare_eventuallyEq ha.ne')]
  have hexp : 0 < 1 / a - 1 / 2 := by
    rw [sub_pos]
    exact one_div_lt_one_div_of_lt ha ha2
  exact (tendsto_rpow_atTop hexp).atTop_mul_pos (Real.sqrt_pos.mpr two_pos)
    tendsto_sqrt_two_add_inv_sub_sqrt_inv

/-! ### The constants `A₃` and `A₄` at `a = 2` -/

/-- **`A₃ = √2 A₁ / √A₂`** for the chi-square law at `a = 2`, where
`A₃ = (A₁ / A₂^{1/2}) √2`. -/
theorem div_rpow_mul_sqrt_two_eq (A₁ A₂ : ℝ) :
    A₁ / A₂ ^ ((1 : ℝ) / 2) * √2 = √2 * A₁ / √A₂ := by
  rw [← sqrt_eq_rpow]
  ring

/-- **`A₄ = A₃ / Γ(1/2) = √2 A₁ / (√A₂ √π)`** for the chi-square law at `a = 2`. -/
theorem div_rpow_mul_sqrt_two_div_Gamma_eq (A₁ A₂ : ℝ) :
    A₁ / A₂ ^ ((1 : ℝ) / 2) * √2 / Gamma (1 / 2) = √2 * A₁ / (√A₂ * √π) := by
  rw [Gamma_one_half_eq, div_rpow_mul_sqrt_two_eq, div_div]

/-- `A₃ = √π A₄` at `a = 2`. -/
theorem div_rpow_mul_sqrt_two_eq_sqrt_pi_mul (A₁ A₂ : ℝ) :
    A₁ / A₂ ^ ((1 : ℝ) / 2) * √2 = √π * (A₁ / A₂ ^ ((1 : ℝ) / 2) * √2 / Gamma (1 / 2)) := by
  rw [Gamma_one_half_eq]
  have : √π ≠ 0 := (Real.sqrt_pos.mpr pi_pos).ne'
  field_simp

/-- For `A₁, A₂ > 0` the constants `A₃` and `A₄` are positive. -/
theorem div_rpow_mul_sqrt_two_pos {A₁ A₂ : ℝ} (hA₁ : 0 < A₁) (hA₂ : 0 < A₂) :
    0 < A₁ / A₂ ^ ((1 : ℝ) / 2) * √2 ∧
      0 < A₁ / A₂ ^ ((1 : ℝ) / 2) * √2 / Gamma (1 / 2) := by
  rw [div_rpow_mul_sqrt_two_div_Gamma_eq, div_rpow_mul_sqrt_two_eq]
  have := Real.sqrt_pos.mpr hA₂
  exact ⟨by positivity, by positivity⟩

/-- **The prefactor of (I.3.7) tends to `A₃`**: `A₁ / (A₂^{1/2} λ^{1 - 1/2}) (√(1 + 2λ) - 1)`
tends to `(A₁ / A₂^{1/2}) √2` as `λ → ∞`. -/
theorem tendsto_div_mul_sqrt_one_add_two_mul_sub_one (A₁ A₂ : ℝ) :
    Tendsto (fun lam : ℝ => A₁ / (A₂ ^ ((1 : ℝ) / 2) * lam ^ (1 - (1 : ℝ) / 2)) *
        (√(1 + 2 * lam) - 1)) atTop (𝓝 (A₁ / A₂ ^ ((1 : ℝ) / 2) * √2)) := by
  refine (tendsto_sqrt_one_add_two_mul_sub_one_div_sqrt.const_mul
    (A₁ / A₂ ^ ((1 : ℝ) / 2))).congr' ?_
  filter_upwards with lam
  rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, ← sqrt_eq_rpow lam]
  ring

/-- **Scale selection for `f(r) = r^{2α}` at `a = 2`**: the inverse of `f` is `y ↦ y^{1/(2α)}`,
and `f^{-1}(λ / (A₂ h))^α h = √(λ / A₂) √h`. -/
theorem rpow_div_mul_rpow_mul_eq {α A₂ h lam : ℝ} (hα : 0 < α) (hA₂ : 0 < A₂) (hh : 0 < h)
    (hlam : 0 < lam) :
    ((lam / (A₂ * h)) ^ (1 / (2 * α))) ^ α * h = √(lam / A₂) * √h := by
  have hy : 0 < lam / (A₂ * h) := by positivity
  have hs : √h ≠ 0 := (Real.sqrt_pos.mpr hh).ne'
  have hsplit : √(lam / (A₂ * h)) = √(lam / A₂) / √h := by
    rw [show lam / (A₂ * h) = lam / A₂ / h by field_simp, Real.sqrt_div' _ hh.le]
  rw [← rpow_mul hy.le, show 1 / (2 * α) * α = 1 / 2 by field_simp, ← sqrt_eq_rpow, hsplit,
    div_mul_eq_mul_div, div_eq_iff hs, mul_assoc, Real.mul_self_sqrt hh.le]

/-- **The tail exponent at `a = 2`**: for `f(r) = r^{2α}`, `f^{-1}(n)^α / n = n^{-1/2}`, so (I.3.3)
reads `P(|K| ≥ n) ~ A₄ / √n`. -/
theorem rpow_rpow_div_eq_sqrt_inv {α n : ℝ} (hα : 0 < α) (hn : 0 < n) :
    (n ^ (1 / (2 * α))) ^ α / n = (√n)⁻¹ := by
  rw [← rpow_mul hn.le, show 1 / (2 * α) * α = 1 / 2 by field_simp, ← sqrt_eq_rpow]
  rw [← inv_div, Real.div_sqrt]

/-- Non-vacuity of hypotheses (3) and (4) of Proposition I.3.2 at the chi-square law: the
constant family `Q_r = Q_∞` converges weakly, and `Q_∞` has no atom at `0`. -/
example :
    haveI := isProbabilityMeasure_gammaMeasure (a := 1 / 2) (r := 1 / 2) (by norm_num)
      (by norm_num)
    Tendsto (fun _ : ℝ => (gammaMeasure (1 / 2) (1 / 2)).toProbabilityMeasure) atTop
        (𝓝 (gammaMeasure (1 / 2) (1 / 2)).toProbabilityMeasure) ∧
      gammaMeasure (1 / 2) (1 / 2) {0} = 0 :=
  ⟨tendsto_const_nhds, gammaMeasure_singleton _ _ _⟩

end PercLib.Analysis
