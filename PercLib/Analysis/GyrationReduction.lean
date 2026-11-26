/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
The analytic reduction of Proposition I.5.2 (radius of gyration) to Lemma I.5.7 and
Proposition I.4.2, from T. Hutchcroft, *Critical long-range percolation I: High effective
dimension*, arXiv:2508.18807v1, §I.5.1.

Adapted from the repository `yujinhkim/lrp`, branch `critical-lrp-1`, commit
`d382e4c28d92dd4e698ebf4f2aaf0bc932ae73fc`, file
`PercLib/CriticalLRP/Analysis/GyrationReduction.lean`; licence Apache-2.0 as declared in that
commit's file headers and `third_party/critical-lrp/NOTICE.md`; upstream
`yujinhkim/Critical-Long-range-percolation` at `3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf`.
Modified: `RegularlyVaryingAtTop` becomes `RegularlyVarying` of
`PercLib/Analysis/RegularVariation/Defs.lean`; the definition `driver α c Q` is written out as
`fun r => c * Q * r ^ (2 + α)`, and its lemmas `measurable_driver`, `driver_pos`, `driver_rv`
and `regularlyVarying_const_mul_rpow` are replaced by `regularlyVarying_rpow` and
`RegularlyVarying.const_mul`; `not_regularlyVarying_zero` is not ported, its content being
`RegularlyVarying.eventually_pos`; hypotheses not used by the proofs are dropped; the critical
case uses the eventual form of the logarithmic corollary of Lemma I.5.6; the limit of positive
semidefinite forms is stated along an arbitrary nontrivial filter; declarations are renamed;
`autoImplicit`, disabled linters and `#print` lines are removed.
-/
module

public import PercLib.Analysis.CriticalLogODE
public import PercLib.Analysis.GyrationODE
public import Mathlib.LinearAlgebra.BilinearForm.Properties

/-! # Proposition I.5.2 from the gyration asymptotic

Write `F r = E_{β_c,r}[Σ_{x ∈ K} ⟨x, u⟩²]`, `G r = E_{β_c,r}|K|`, `c = α² / β_c` and
`Q = ∫_B ⟨y, u⟩² dy`. Lemma I.5.7 of the paper states
`F' r ∼ (2 α F r + c Q r ^ (2 + α)) / r`, and Proposition I.4.2 states `G r ∼ (α / β_c) r ^ α`.
Both are results of the paper about the percolation model; here they enter as explicit
hypotheses on functions `F`, `G` of a real variable, and this file proves the analytic part of
Proposition I.5.2 from them. Proposition I.5.2 itself is not asserted.

## Main results

* `regularlyVarying_max_of_tendsto_gyration_deriv_ratio`: `F` is regularly varying of index
  `max (2 α) (2 + α)`.
* `tendsto_gyration_driver_div_of_two_lt`, `tendsto_div_gyration_driver_of_lt`,
  `tendsto_div_rpow_of_tendsto_gyration_deriv_ratio_of_lt`: the cases `α > 2` and `α < 2`.
* `tendsto_div_rpow_mul_log_of_gyration_log_error_ode`: the critical case `α = 2`, via
  Lemma I.5.6.
* `tendsto_div_rpow_sub_mul_of_tendsto_div_rpow`: quotient of two power asymptotics.
* `tendsto_div_rpow_two_mul_of_lt`, `tendsto_div_rpow_two_mul_log_mul_of_two`,
  `tendsto_div_rpow_mul_of_two_lt`: the resulting asymptotics of `F / G`.
* `gyration_limit_pos_of_two_lt`: the `α > 2` limit constant of the exact ODE is positive.
* `LinearMap.BilinForm.isPosSemidef_of_tendsto`: a pointwise limit of positive semidefinite
  bilinear forms is positive semidefinite.
-/

@[expose] public section

open Filter Set MeasureTheory
open scoped Topology

namespace PercLib.Analysis

/-! ### Regular variation and the non-critical cases -/

/-- The driving term `r ↦ c Q r ^ (2 + α)` is measurable, positive on `(0, ∞)` and regularly
varying of index `2 + α`. -/
private theorem gyration_driver_facts {α c Q : ℝ} (hcQ : 0 < c * Q) :
    Measurable (fun r : ℝ => c * Q * r ^ (2 + α)) ∧
      (∀ r : ℝ, 0 < r → 0 < c * Q * r ^ (2 + α)) ∧
      RegularlyVarying (2 + α) (fun r : ℝ => c * Q * r ^ (2 + α)) :=
  ⟨measurable_const.mul (measurable_id.pow_const _),
    fun _ hr => mul_pos hcQ (Real.rpow_pos_of_pos hr _),
    (regularlyVarying_rpow (2 + α)).const_mul hcQ⟩

/-- **Lemma I.5.7 implies regular variation** (first sentence of Proposition I.5.2): if `F > 0`
is differentiable on `(0, ∞)` with `F' r / ((2 α F r + c Q r ^ (2 + α)) / r) → 1`, `α > 0` and
`c Q > 0`, then `F` is regularly varying of index `max (2 α) (2 + α)`. -/
theorem regularlyVarying_max_of_tendsto_gyration_deriv_ratio {F F' : ℝ → ℝ} {α c Q : ℝ}
    (hα : 0 < α) (hcQ : 0 < c * Q)
    (hFpos : ∀ x, 0 < x → 0 < F x)
    (hderiv : ∀ x, 0 < x → HasDerivAt F (F' x) x)
    (hasym : Tendsto (fun r => F' r / ((2 * α * F r + c * Q * r ^ (2 + α)) / r)) atTop (𝓝 1)) :
    RegularlyVarying (max (2 * α) (2 + α)) F := by
  obtain ⟨hm, hpos, hrv⟩ := gyration_driver_facts hcQ
  exact (regularlyVarying_max_and_tendsto_of_tendsto_deriv_ratio (by linarith) (by linarith) hm
    hrv hpos hFpos hderiv hasym).1

/-- **The case `α > 2`**: under the gyration asymptotic the driving term is negligible,
`c Q r ^ (2 + α) / F r → 0`. -/
theorem tendsto_gyration_driver_div_of_two_lt {F F' : ℝ → ℝ} {α c Q : ℝ}
    (hα2 : 2 < α) (hcQ : 0 < c * Q)
    (hFpos : ∀ x, 0 < x → 0 < F x)
    (hderiv : ∀ x, 0 < x → HasDerivAt F (F' x) x)
    (hasym : Tendsto (fun r => F' r / ((2 * α * F r + c * Q * r ^ (2 + α)) / r)) atTop (𝓝 1)) :
    Tendsto (fun r => c * Q * r ^ (2 + α) / F r) atTop (𝓝 0) := by
  obtain ⟨hm, hpos, hrv⟩ := gyration_driver_facts hcQ
  exact ((regularlyVarying_max_and_tendsto_of_tendsto_deriv_ratio (by linarith) (by linarith) hm
    hrv hpos hFpos hderiv hasym).2 (by linarith)).1

/-- **Proposition I.5.2 (1), ratio form**: for `0 < α < 2`, under the gyration asymptotic,
`F r / (c Q r ^ (2 + α)) → 1 / (2 - α)` (Lemma I.4.21 with `a = 2 α < b = 2 + α`). -/
theorem tendsto_div_gyration_driver_of_lt {F F' : ℝ → ℝ} {α c Q : ℝ}
    (hα : 0 < α) (hα2 : α < 2) (hcQ : 0 < c * Q)
    (hderiv : ∀ x, 0 < x → HasDerivAt F (F' x) x)
    (hasym : Tendsto (fun r => F' r / ((2 * α * F r + c * Q * r ^ (2 + α)) / r)) atTop (𝓝 1)) :
    Tendsto (fun r => F r / (c * Q * r ^ (2 + α))) atTop (𝓝 (1 / (2 - α))) := by
  obtain ⟨hm, hpos, hrv⟩ := gyration_driver_facts hcQ
  have hlim := (tendsto_div_of_tendsto_deriv_ratio hm hrv (by linarith) (by linarith) hderiv
    hasym).const_mul (1 / (2 - α))
  rw [mul_one] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  have := (hpos r hr).ne'
  have : (2 : ℝ) - α ≠ 0 := by linarith
  have h2 : (2 : ℝ) + α - 2 * α = 2 - α := by ring
  rw [h2]
  field_simp

/-- **Proposition I.5.2 (1)**: for `0 < α < 2`, under the gyration asymptotic,
`F r / r ^ (2 + α) → c Q / (2 - α)`. -/
theorem tendsto_div_rpow_of_tendsto_gyration_deriv_ratio_of_lt {F F' : ℝ → ℝ} {α c Q : ℝ}
    (hα : 0 < α) (hα2 : α < 2) (hcQ : 0 < c * Q)
    (hderiv : ∀ x, 0 < x → HasDerivAt F (F' x) x)
    (hasym : Tendsto (fun r => F' r / ((2 * α * F r + c * Q * r ^ (2 + α)) / r)) atTop (𝓝 1)) :
    Tendsto (fun r => F r / r ^ (2 + α)) atTop (𝓝 (c * Q / (2 - α))) := by
  have hlim := (tendsto_div_gyration_driver_of_lt hα hα2 hcQ hderiv hasym).mul_const (c * Q)
  rw [one_div_mul_eq_div] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  have := (Real.rpow_pos_of_pos hr (2 + α)).ne'
  have := hcQ.ne'
  field_simp
  rw [mul_assoc, mul_div_cancel_right₀ _ hcQ.ne']

/-! ### The critical case `α = 2` -/

/-- **Proposition I.5.2 (2)**: in the critical case `α = 2`, if eventually
`F' = (1 - δ) 4 F / r + c Q r ^ 4 / r` with `δ` a logarithmically integrable error function,
`F` eventually positive and differentiable, and `c Q > 0`, then `F r / (r ^ 4 log r) → c Q`. -/
theorem tendsto_div_rpow_mul_log_of_gyration_log_error_ode {F F' δ : ℝ → ℝ} {c Q : ℝ}
    (hcQ : 0 < c * Q)
    (hFpos : ∀ᶠ x in atTop, 0 < F x)
    (hderiv : ∀ᶠ x in atTop, HasDerivAt F (F' x) x)
    (hδ : IsLogErrorFunction δ)
    (hode : ∀ᶠ x in atTop, F' x = (1 - δ x) * 4 * F x / x + c * Q * x ^ (4 : ℝ) / x) :
    Tendsto (fun r => F r / (r ^ (4 : ℝ) * Real.log r)) atTop (𝓝 (c * Q)) := by
  have hhA : Tendsto (fun r : ℝ => c * Q * r ^ (4 : ℝ) / (c * Q * r ^ (4 : ℝ))) atTop (𝓝 1) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    exact (div_self (mul_pos hcQ (Real.rpow_pos_of_pos hr _)).ne').symm
  have hmain := (tendsto_div_mul_rpow_mul_log_of_critical_log_error_ode (by norm_num) hcQ
    (measurable_const.mul (measurable_id.pow_const _)) hFpos hderiv hδ hode hhA).mul_const (c * Q)
  rw [one_mul] at hmain
  refine hmain.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with r hr
  have := (Real.rpow_pos_of_pos (zero_lt_one.trans hr) (4 : ℝ)).ne'
  have := (Real.log_pos hr).ne'
  have := hcQ.ne'
  field_simp
  rw [mul_assoc, mul_div_cancel_right₀ _ hcQ.ne']

/-! ### Asymptotics of `F / G` -/

/-- If `F r / r ^ p → a` and `G r / r ^ q → b ≠ 0`, then `F r / (r ^ (p - q) G r) → a / b`. -/
theorem tendsto_div_rpow_sub_mul_of_tendsto_div_rpow {F G : ℝ → ℝ} {p q a b : ℝ}
    (hF : Tendsto (fun r => F r / r ^ p) atTop (𝓝 a))
    (hG : Tendsto (fun r => G r / r ^ q) atTop (𝓝 b)) (hb : b ≠ 0) :
    Tendsto (fun r => F r / (r ^ (p - q) * G r)) atTop (𝓝 (a / b)) := by
  refine (hF.div hG hb).congr' ?_
  filter_upwards [hG.eventually (eventually_ne_nhds hb), eventually_gt_atTop (0 : ℝ)] with r hG0
    hr0
  have hGr : G r ≠ 0 := fun h => hG0 (by rw [h, zero_div])
  simp only [Pi.div_apply]
  have h1 : r ^ p = r ^ (p - q) * r ^ q := by
    rw [← Real.rpow_add hr0, sub_add_cancel]
  have := (Real.rpow_pos_of_pos hr0 q).ne'
  have := (Real.rpow_pos_of_pos hr0 (p - q)).ne'
  rw [h1]
  field_simp

/-- **Proposition I.5.2 (1) for `F / G`**: if `F r / r ^ (2 + α) → (α² / β) Q / (2 - α)` and
`G r / r ^ α → α / β` with `α, β > 0`, then `F r / (r ^ 2 G r) → (α / (2 - α)) Q`. -/
theorem tendsto_div_rpow_two_mul_of_lt {F G : ℝ → ℝ} {α β Q : ℝ}
    (hβ : 0 < β) (hα : 0 < α)
    (hF : Tendsto (fun r => F r / r ^ (2 + α)) atTop (𝓝 (α ^ 2 / β * Q / (2 - α))))
    (hG : Tendsto (fun r => G r / r ^ α) atTop (𝓝 (α / β))) :
    Tendsto (fun r => F r / (r ^ (2 : ℝ) * G r)) atTop (𝓝 (α / (2 - α) * Q)) := by
  have h := tendsto_div_rpow_sub_mul_of_tendsto_div_rpow hF hG
    (div_ne_zero hα.ne' hβ.ne')
  rw [add_sub_cancel_right] at h
  convert h using 2
  field_simp

/-- **Proposition I.5.2 (2) for `F / G`**: if `F r / (r ^ 4 log r) → (4 / β) Q` and
`G r / r ^ 2 → 2 / β` with `β > 0`, then `F r / (r ^ 2 log r G r) → 2 Q`. -/
theorem tendsto_div_rpow_two_mul_log_mul_of_two {F G : ℝ → ℝ} {β Q : ℝ} (hβ : 0 < β)
    (hF : Tendsto (fun r => F r / (r ^ (4 : ℝ) * Real.log r)) atTop (𝓝 (4 / β * Q)))
    (hG : Tendsto (fun r => G r / r ^ (2 : ℝ)) atTop (𝓝 (2 / β))) :
    Tendsto (fun r => F r / (r ^ (2 : ℝ) * Real.log r * G r)) atTop (𝓝 (2 * Q)) := by
  have h := hF.div hG (div_ne_zero two_ne_zero hβ.ne')
  have hval : 4 / β * Q / (2 / β) = 2 * Q := by
    field_simp
    ring
  rw [hval] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with r hr
  have hr0 : 0 < r := zero_lt_one.trans hr
  have := (Real.log_pos hr).ne'
  have := (Real.rpow_pos_of_pos hr0 (2 : ℝ)).ne'
  simp only [Pi.div_apply]
  have h4 : r ^ (4 : ℝ) = r ^ (2 : ℝ) * r ^ (2 : ℝ) := by
    rw [← Real.rpow_add hr0]
    norm_num
  rw [h4]
  field_simp

/-- **Proposition I.5.2 (3) for `F / G`**: if `F r / r ^ (2 α) → A` and `G r / r ^ α → α / β`
with `α, β > 0`, then `F r / (r ^ α G r) → A β / α`. -/
theorem tendsto_div_rpow_mul_of_two_lt {F G : ℝ → ℝ} {α β A : ℝ}
    (hβ : 0 < β) (hα : 0 < α)
    (hF : Tendsto (fun r => F r / r ^ (2 * α)) atTop (𝓝 A))
    (hG : Tendsto (fun r => G r / r ^ α) atTop (𝓝 (α / β))) :
    Tendsto (fun r => F r / (r ^ α * G r)) atTop (𝓝 (A * β / α)) := by
  have h := tendsto_div_rpow_sub_mul_of_tendsto_div_rpow hF hG
    (div_ne_zero hα.ne' hβ.ne')
  rw [show 2 * α - α = α by ring] at h
  convert h using 2
  field_simp

/-! ### Positivity of the `α > 2` constant -/

/-- For `α > 2` and the exact gyration ODE `F' = 2 α F / r + c r ^ (α + 1) Q` on `(0, ∞)` with
`F ≥ 0`, the limit `F 1 + c Q / (α - 2)` of `F r / r ^ (2 α)` is nonnegative. -/
theorem gyration_limit_nonneg_of_two_lt {F : ℝ → ℝ} {α c Q : ℝ} (hα : 2 < α)
    (hF : ∀ r : ℝ, 0 < r → HasDerivAt F ((2 * α / r) * F r + c * r ^ (α + 1) * Q) r)
    (hnonneg : ∀ r : ℝ, 0 < r → 0 ≤ F r) :
    0 ≤ F 1 + c * Q / (α - 2) := by
  refine le_of_tendsto_of_tendsto tendsto_const_nhds (tendsto_div_rpow_of_gt hα hF) ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  exact div_nonneg (hnonneg r hr) (Real.rpow_pos_of_pos hr _).le

/-- For `α > 2`, `c Q > 0` and the exact gyration ODE on `(0, ∞)` with `F ≥ 0`, the limit
`F 1 + c Q / (α - 2)` of `F r / r ^ (2 α)` is positive: if it vanished, the solution would be
`-(c Q / (α - 2)) r ^ (2 + α) < 0`. -/
theorem gyration_limit_pos_of_two_lt {F : ℝ → ℝ} {α c Q : ℝ} (hα : 2 < α) (hcQ : 0 < c * Q)
    (hF : ∀ r : ℝ, 0 < r → HasDerivAt F ((2 * α / r) * F r + c * r ^ (α + 1) * Q) r)
    (hnonneg : ∀ r : ℝ, 0 < r → 0 ≤ F r) :
    0 < F 1 + c * Q / (α - 2) := by
  refine (gyration_limit_nonneg_of_two_lt hα hF hnonneg).lt_of_ne fun hzero => ?_
  have hden : 0 < α - 2 := by linarith
  have hM : 0 < c * Q / (α - 2) := div_pos hcQ hden
  have hF1 : F 1 = -(c * Q / (α - 2)) := by linarith
  have hsign : c * Q / (2 - α) = -(c * Q / (α - 2)) := by
    rw [← neg_sub, div_neg]
  have hex := gyration_exact (ne_of_gt hα) hF 2 two_pos
  rw [hF1, hsign] at hex
  have hpow : 0 < (2 : ℝ) ^ (2 + α) := Real.rpow_pos_of_pos two_pos _
  have hneg : F 2 < 0 := by
    rw [hex]
    nlinarith [mul_pos hM hpow]
  exact (hnonneg 2 two_pos).not_gt hneg

end PercLib.Analysis

/-! ### Limits of positive semidefinite forms -/

/-- A pointwise limit, along a nontrivial filter, of positive semidefinite real bilinear forms is
positive semidefinite. -/
theorem LinearMap.BilinForm.isPosSemidef_of_tendsto {E ι : Type*} [AddCommGroup E] [Module ℝ E]
    {l : Filter ι} [l.NeBot] {B : ι → LinearMap.BilinForm ℝ E} {B' : LinearMap.BilinForm ℝ E}
    (hconv : ∀ u v : E, Tendsto (fun i => B i u v) l (𝓝 (B' u v)))
    (hpsd : ∀ i, (B i).IsPosSemidef) : B'.IsPosSemidef := by
  refine ⟨⟨fun u v => ?_⟩, ⟨fun u => ?_⟩⟩
  · have h := hconv u v
    rw [show (fun i => B i u v) = fun i => B i v u from
      funext fun i => (hpsd i).isSymm.eq u v] at h
    exact tendsto_nhds_unique h (hconv v u)
  · exact ge_of_tendsto (hconv u u) (Eventually.of_forall fun i => (hpsd i).isNonneg.nonneg u)
