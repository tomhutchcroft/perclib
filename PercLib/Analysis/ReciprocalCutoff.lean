/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-21, against pinned mathlib. No upstream proof is copied.
-/
module

public import PercLib.Analysis.ReciprocalODE

/-!
# A reciprocal cutoff bound and the minimum of the cutoff and full values

Let `α, A > 0` and let `f : ℝ → ℝ` be positive, nondecreasing and locally absolutely continuous
on `[1, ∞)`, with limit `X ∈ (0, ∞]` (as an element of `ℝ≥0∞`), and suppose
`f' ≤ A r^{-α-1} f²` almost everywhere on `[1, ∞)`. Applying `le_of_deriv_le_mul_sq` on
`[r, R]` and letting `R → ∞` gives `(1/X + (A/α) r^{-α})⁻¹ ≤ f r`, with `1/∞ = 0`. If moreover
`f r ≤ C r^α`, then `f r ≤ min (C r^α) X`, and `f r` is comparable to `min (r^α) X` with
constants depending only on `α`, `A` and `C`.

## Main results

* `inv_le_of_deriv_le_rpow_mul_sq`: the lower bound `((X⁻¹).toReal + (A/α) r^{-α})⁻¹ ≤ f r`.
* `ofReal_le_of_monotoneOn_of_tendsto`: a function nondecreasing on `[1, ∞)` stays below its
  limit.
* `ofReal_le_min_of_monotoneOn_of_tendsto`: the upper bound `f r ≤ min (C r^α) X`.
* `ofReal_mem_Icc_mul_min_of_deriv_le_rpow_mul_sq`: `f r` lies between `c₁ min (r^α) X` and
  `c₂ min (r^α) X` with `c₁ = (1 + A/α)⁻¹` and `c₂ = max C 1`.

No definition is introduced.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Real intervalIntegral
open scoped Topology ENNReal

namespace PercLib.Analysis

variable {f : ℝ → ℝ} {X : ℝ≥0∞} {α A C : ℝ}

/-- A function nondecreasing on `[1, ∞)` whose values converge in `ℝ≥0∞` to `X` stays below
`X`. -/
theorem ofReal_le_of_monotoneOn_of_tendsto (hmono : MonotoneOn f (Ici 1))
    (hlim : Tendsto (fun r => ENNReal.ofReal (f r)) atTop (𝓝 X)) {r : ℝ} (hr : 1 ≤ r) :
    ENNReal.ofReal (f r) ≤ X := by
  refine ge_of_tendsto hlim ?_
  filter_upwards [eventually_ge_atTop r] with R hR
  exact ENNReal.ofReal_le_ofReal (hmono (mem_Ici.2 hr) (mem_Ici.2 (hr.trans hR)) hR)

/-- `∫_r^R A s^{-α-1} ds ≤ (A/α) r^{-α}` for `0 < r ≤ R`, `α, A > 0`. -/
theorem integral_mul_rpow_neg_sub_one_le (hα : 0 < α) (hA : 0 < A) {r R : ℝ} (hr : 0 < r)
    (hrR : r ≤ R) : ∫ s in r..R, A * s ^ (-α - 1) ≤ A / α * r ^ (-α) := by
  have h0 : (0 : ℝ) ∉ uIcc r R := by
    rw [uIcc_of_le hrR]
    exact fun h => (lt_irrefl 0) (hr.trans_le h.1)
  rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inr ⟨by linarith, h0⟩)]
  have e : -α - 1 + 1 = -α := by ring
  rw [e]
  have hR : 0 ≤ R ^ (-α) := rpow_nonneg (hr.le.trans hrR) _
  have hk : 0 ≤ A / α := (div_pos hA hα).le
  have : A * ((R ^ (-α) - r ^ (-α)) / (-α)) = A / α * r ^ (-α) - A / α * R ^ (-α) := by
    field_simp
    ring
  rw [this]
  nlinarith

/-- **Reciprocal cutoff lower bound.** Let `α, A > 0` and let `f` be positive, nondecreasing
and locally absolutely continuous on `[1, ∞)`, with `ofReal (f r) → X` in `ℝ≥0∞`. If
`f' ≤ A s^{-α-1} f²` a.e. on `[1, ∞)`, then `((X⁻¹).toReal + (A/α) r^{-α})⁻¹ ≤ f r` for
`r ≥ 1` (so the term `X⁻¹` vanishes when `X = ∞`). -/
theorem inv_le_of_deriv_le_rpow_mul_sq (hα : 0 < α) (hA : 0 < A)
    (hpos : ∀ r, 1 ≤ r → 0 < f r) (hmono : MonotoneOn f (Ici 1))
    (hac : ∀ p q, 1 ≤ p → p ≤ q → AbsolutelyContinuousOnInterval f p q)
    (hlim : Tendsto (fun r => ENNReal.ofReal (f r)) atTop (𝓝 X))
    (hder : ∀ᵐ s, 1 ≤ s → deriv f s ≤ A * s ^ (-α - 1) * f s ^ 2) {r : ℝ} (hr : 1 ≤ r) :
    ((X⁻¹).toReal + A / α * r ^ (-α))⁻¹ ≤ f r := by
  have hr0 : 0 < r := one_pos.trans_le hr
  -- `X ≠ 0`, so `X⁻¹` is finite
  have hX0 : X ≠ 0 :=
    (ENNReal.ofReal_pos.2 (hpos r hr)).trans_le
      (ofReal_le_of_monotoneOn_of_tendsto hmono hlim hr) |>.ne'
  have hXinv : X⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 hX0
  -- `1 / f R → (X⁻¹).toReal`
  have hinv : Tendsto (fun R => (f R)⁻¹) atTop (𝓝 (X⁻¹).toReal) := by
    have h1 := (ENNReal.tendsto_toReal hXinv).comp (tendsto_inv_iff.2 hlim)
    refine h1.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with R hR
    simp [ENNReal.toReal_inv, ENNReal.toReal_ofReal (hpos R hR).le]
  have hk : 0 < A / α * r ^ (-α) := mul_pos (div_pos hA hα) (rpow_pos_of_pos hr0 _)
  have hden : (X⁻¹).toReal + A / α * r ^ (-α) ≠ 0 := by
    have := ENNReal.toReal_nonneg (a := X⁻¹)
    positivity
  have hg : Tendsto (fun R => ((f R)⁻¹ + A / α * r ^ (-α))⁻¹) atTop
      (𝓝 ((X⁻¹).toReal + A / α * r ^ (-α))⁻¹) :=
    (hinv.add_const _).inv₀ hden
  refine le_of_tendsto hg ?_
  filter_upwards [eventually_ge_atTop r] with R hR
  have hrR : r ≤ R := hR
  have hpos' : ∀ s ∈ Icc r R, 0 < f s := fun s hs => hpos s (hr.trans hs.1)
  have ha : IntervalIntegrable (fun s => A * s ^ (-α - 1)) volume r R := by
    refine ContinuousOn.intervalIntegrable ?_
    refine continuousOn_const.mul (ContinuousOn.rpow_const continuousOn_id fun s hs => ?_)
    rw [uIcc_of_le hrR] at hs
    exact Or.inl (hr0.trans_le hs.1).ne'
  have ha0 : ∀ s ∈ Icc r R, 0 ≤ A * s ^ (-α - 1) := fun s hs =>
    mul_nonneg hA.le (rpow_nonneg (hr0.trans_le hs.1).le _)
  have hder' : ∀ᵐ s, s ∈ Icc r R → deriv f s ≤ A * s ^ (-α - 1) * f s ^ 2 := by
    filter_upwards [hder] with s hs hsI
    exact hs (hr.trans hsI.1)
  have hmain := le_of_deriv_le_mul_sq (hac r R hr hrR) hpos' ha ha0 hder'
    (left_mem_Icc.2 hrR)
  have hint := integral_mul_rpow_neg_sub_one_le hα hA hr0 hrR
  have hfR := hpos R (hr.trans hrR)
  have hI0 : 0 ≤ ∫ s in r..R, A * s ^ (-α - 1) := integral_nonneg hrR fun s hs => ha0 s hs
  refine le_trans ?_ hmain
  rw [one_div]
  exact inv_anti₀ (by positivity) (by linarith)

/-- **Upper bound.** If `f` is nondecreasing on `[1, ∞)` with `ofReal (f r) → X` and
`f r ≤ C r^α` on `[1, ∞)`, then `ofReal (f r) ≤ min (ofReal (C r^α)) X` for `r ≥ 1`. -/
theorem ofReal_le_min_of_monotoneOn_of_tendsto (hmono : MonotoneOn f (Ici 1))
    (hlim : Tendsto (fun r => ENNReal.ofReal (f r)) atTop (𝓝 X))
    (hC : ∀ r, 1 ≤ r → f r ≤ C * r ^ α) {r : ℝ} (hr : 1 ≤ r) :
    ENNReal.ofReal (f r) ≤ min (ENNReal.ofReal (C * r ^ α)) X :=
  le_min (ENNReal.ofReal_le_ofReal (hC r hr)) (ofReal_le_of_monotoneOn_of_tendsto hmono hlim hr)

/-- **Lower comparability.** Under the hypotheses of `inv_le_of_deriv_le_rpow_mul_sq`,
`(1 + A/α)⁻¹ min (r^α) X ≤ f r` for `r ≥ 1`. -/
theorem ofReal_mul_min_le_of_deriv_le_rpow_mul_sq (hα : 0 < α) (hA : 0 < A)
    (hpos : ∀ r, 1 ≤ r → 0 < f r) (hmono : MonotoneOn f (Ici 1))
    (hac : ∀ p q, 1 ≤ p → p ≤ q → AbsolutelyContinuousOnInterval f p q)
    (hlim : Tendsto (fun r => ENNReal.ofReal (f r)) atTop (𝓝 X))
    (hder : ∀ᵐ s, 1 ≤ s → deriv f s ≤ A * s ^ (-α - 1) * f s ^ 2) {r : ℝ} (hr : 1 ≤ r) :
    ENNReal.ofReal (1 + A / α)⁻¹ * min (ENNReal.ofReal (r ^ α)) X ≤ ENNReal.ofReal (f r) := by
  have hr0 : 0 < r := one_pos.trans_le hr
  have hrα : 0 < r ^ α := rpow_pos_of_pos hr0 _
  have hlow := inv_le_of_deriv_le_rpow_mul_sq hα hA hpos hmono hac hlim hder hr
  have hfX := ofReal_le_of_monotoneOn_of_tendsto hmono hlim hr
  set m := min (ENNReal.ofReal (r ^ α)) X with hm
  have hm0 : m ≠ 0 := by
    rw [hm]
    refine (lt_min (ENNReal.ofReal_pos.2 hrα) ?_).ne'
    exact (ENNReal.ofReal_pos.2 (hpos r hr)).trans_le hfX
  have hmtop : m ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (min_le_left _ _)
  set m' := m.toReal with hm'
  have hm'0 : 0 < m' := ENNReal.toReal_pos hm0 hmtop
  have hmr : m' ≤ r ^ α := by
    rw [hm', ← ENNReal.toReal_ofReal hrα.le]
    exact ENNReal.toReal_mono ENNReal.ofReal_ne_top (min_le_left _ _)
  have hXm : (X⁻¹).toReal ≤ m'⁻¹ := by
    rw [hm', ← ENNReal.toReal_inv]
    exact ENNReal.toReal_mono (ENNReal.inv_ne_top.2 hm0)
      (ENNReal.inv_le_inv.2 (min_le_right _ _))
  have hrinv : r ^ (-α) ≤ m'⁻¹ := by
    rw [rpow_neg hr0.le]
    exact inv_anti₀ hm'0 hmr
  have hk : 0 ≤ A / α := (div_pos hA hα).le
  have hsum : (X⁻¹).toReal + A / α * r ^ (-α) ≤ (1 + A / α) * m'⁻¹ := by
    nlinarith [mul_le_mul_of_nonneg_left hrinv hk]
  have hpos2 : 0 < (X⁻¹).toReal + A / α * r ^ (-α) := by
    have := ENNReal.toReal_nonneg (a := X⁻¹)
    have := rpow_pos_of_pos hr0 (-α)
    have := div_pos hA hα
    positivity
  have hreal : (1 + A / α)⁻¹ * m' ≤ f r := by
    refine le_trans ?_ hlow
    have e : (1 + A / α)⁻¹ * m' = ((1 + A / α) * m'⁻¹)⁻¹ := by
      rw [mul_inv, inv_inv]
    rw [e]
    exact inv_anti₀ hpos2 hsum
  calc ENNReal.ofReal (1 + A / α)⁻¹ * m = ENNReal.ofReal ((1 + A / α)⁻¹ * m') := by
        rw [ENNReal.ofReal_mul (inv_nonneg.2 (by positivity)), hm', ENNReal.ofReal_toReal hmtop]
    _ ≤ ENNReal.ofReal (f r) := ENNReal.ofReal_le_ofReal hreal

/-- **Upper comparability.** If `f` is nondecreasing on `[1, ∞)` with `ofReal (f r) → X` and
`f r ≤ C r^α` on `[1, ∞)`, then `ofReal (f r) ≤ max C 1 · min (r^α) X` for `r ≥ 1`. -/
theorem ofReal_le_mul_min_of_monotoneOn_of_tendsto (hmono : MonotoneOn f (Ici 1))
    (hlim : Tendsto (fun r => ENNReal.ofReal (f r)) atTop (𝓝 X))
    (hC : ∀ r, 1 ≤ r → f r ≤ C * r ^ α) {r : ℝ} (hr : 1 ≤ r) :
    ENNReal.ofReal (f r) ≤ ENNReal.ofReal (max C 1) * min (ENNReal.ofReal (r ^ α)) X := by
  have hr0 : 0 < r := one_pos.trans_le hr
  have hc : 1 ≤ max C 1 := le_max_right _ _
  rcases le_total (ENNReal.ofReal (r ^ α)) X with h | h
  · rw [min_eq_left h, ← ENNReal.ofReal_mul (by linarith)]
    refine ENNReal.ofReal_le_ofReal ((hC r hr).trans ?_)
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (rpow_pos_of_pos hr0 _).le
  · rw [min_eq_right h]
    refine (ofReal_le_of_monotoneOn_of_tendsto hmono hlim hr).trans ?_
    calc X = 1 * X := (one_mul X).symm
      _ ≤ ENNReal.ofReal (max C 1) * X := by
        gcongr
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal hc

/-- **Comparability.** Under the hypotheses of `inv_le_of_deriv_le_rpow_mul_sq` and
`f r ≤ C r^α` on `[1, ∞)`, `ofReal (f r)` lies between `(1 + A/α)⁻¹ min (r^α) X` and
`max C 1 · min (r^α) X` for `r ≥ 1`. -/
theorem ofReal_mem_Icc_mul_min_of_deriv_le_rpow_mul_sq (hα : 0 < α) (hA : 0 < A)
    (hpos : ∀ r, 1 ≤ r → 0 < f r) (hmono : MonotoneOn f (Ici 1))
    (hac : ∀ p q, 1 ≤ p → p ≤ q → AbsolutelyContinuousOnInterval f p q)
    (hlim : Tendsto (fun r => ENNReal.ofReal (f r)) atTop (𝓝 X))
    (hder : ∀ᵐ s, 1 ≤ s → deriv f s ≤ A * s ^ (-α - 1) * f s ^ 2)
    (hC : ∀ r, 1 ≤ r → f r ≤ C * r ^ α) {r : ℝ} (hr : 1 ≤ r) :
    ENNReal.ofReal (f r) ∈ Icc (ENNReal.ofReal (1 + A / α)⁻¹ * min (ENNReal.ofReal (r ^ α)) X)
      (ENNReal.ofReal (max C 1) * min (ENNReal.ofReal (r ^ α)) X) :=
  ⟨ofReal_mul_min_le_of_deriv_le_rpow_mul_sq hα hA hpos hmono hac hlim hder hr,
    ofReal_le_mul_min_of_monotoneOn_of_tendsto hmono hlim hC hr⟩

end PercLib.Analysis
