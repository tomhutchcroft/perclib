/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
A signed linear differential equation with a regularly varying forcing term: Lemma I.5.26 of
T. Hutchcroft, *Critical long-range percolation I: High effective dimension*, arXiv:2508.18807v1,
§I.5, proved here by variation of constants.

Adapted from the repository `yujinhkim/lrp`, branch `critical-lrp-1`, commit
`d382e4c28d92dd4e698ebf4f2aaf0bc932ae73fc`, file
`PercLib/CriticalLRP/Analysis/Lemma_I_5_26.lean`; licence Apache-2.0 as declared in that commit's
file headers and `third_party/critical-lrp/NOTICE.md`; upstream
`yujinhkim/Critical-Long-range-percolation` at `3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf`.
Modified: `RegularlyVaryingAtTop h b` becomes `RegularlyVarying b h` of
`PercLib/Analysis/RegularVariation/Defs.lean`; the structure `RVPosData` is unbundled, and the
hypotheses that the proofs below do not need (positivity of `a`, of `b` and of `h` above a
threshold, global measurability of `h`, local boundedness of `h`, the bound `|f| = O(h)`, and
measurability and boundedness of the error terms in the folded forms) are removed; the asymptotic
statements are proved by the variation-of-constants argument with the integrating factor
`r ^ a * exp (∫ ε s / s ds)` in place of the source's single-error core; the source's numerical
example is replaced by a witness for the hypotheses of the main theorem; declarations are
renamed; `autoImplicit`, disabled linters and `#print` lines are removed.
-/
module

public import PercLib.Analysis.DrivenODE
public import PercLib.Analysis.RegularVariation.KaramataPrimitive

/-! # Signed linear ODEs with a regularly varying forcing term

Let `h` be regularly varying of index `b`, let `a < b` and `A` be real, and let `f` be locally
absolutely continuous with, almost everywhere on a tail,
`r f'(r) = (a + ε r) f r + (A + δ r) h r` for measurable `ε, δ → 0`. Then `f / h → A / (b - a)`.
No sign condition on `a`, `b`, `A` or `f` and no prior bound `|f| = O(h)` is used.

The proof is variation of constants. The integrating factor is written out as
`G r = r ^ a * exp (∫ s in r₀..r, (Ioi r₀).indicator ε s / s)`; it is regularly varying of
index `a`, and `f / G` is absolutely continuous with
`(f / G) R - (f / G) r₀ = ∫ s in r₀..R, (A + δ s) * (h s / (s * G s))`. The quotient `q = h / G`
is regularly varying of index `b - a > 0`, so Karamata's theorem gives
`∫ s in r₀..r, q s / s ∼ q r / (b - a)`, the `δ`-part is `o(q r)`, and `G / h = 1 / q → 0`.
Only `f` is differentiated, and only almost everywhere: no primitive of `h s / s` is
differentiated.

## Main results

* `mul_rpow_neg_sub_eq_integral_of_signed_ode`: the exact increment of `f r ^ (-a)` for the
  single-error equation `f' = (a f + (A + ε) h) / r` with `f` differentiable everywhere.
* `RegularlyVarying.exists_forall_abs_le`: a measurable regularly varying function of any index
  is bounded on the compact intervals of a tail.
* `regularlyVarying_rpow_mul_exp_integral`: the integrating factor is regularly varying of
  index `a`.
* `div_sub_div_eq_integral_of_ae_mul_deriv_eq`: variation of constants for the a.e. equation.
* `tendsto_div_of_ae_mul_deriv_eq`: the main theorem, `f / h → A / (b - a)`.
* `tendsto_div_of_two_error_ode`, `isLittleO_sub_const_mul_of_two_error_ode`: Lemma I.5.26 in the
  two-error form `f' = ((a + ε₁) f + (A + ε₂) h) / r` with arbitrary errors `ε₁, ε₂ → 0`.
* `tendsto_div_of_tendsto_mul_deriv_sub_div`,
  `isLittleO_sub_const_mul_of_tendsto_mul_deriv_sub_div`: the folded form
  `(r f' - a f) / h → A`.
* `tendsto_div_of_signed_ode`: the single-error form on a tail `[r₀, ∞)`.
-/

@[expose] public section

open Filter Set MeasureTheory
open scoped Topology

namespace PercLib.Analysis

/-! ### The exact increment for the weight `r ^ (-a)` -/

/-- **The exact increment of `f r ^ (-a)`.** If `f` is differentiable on `[r₀, R]` with
`f' = (a f + (A + ε) h) / x` there, `|ε| ≤ 1`, and `f`, `h` are bounded on `[r₀, R]`, then
`f R R ^ (-a) - f r₀ r₀ ^ (-a) = ∫ s in r₀..R, (A + ε s) (h s s ^ (-(a + 1)))`. Only `f` and the
explicit power are differentiated. -/
theorem mul_rpow_neg_sub_eq_integral_of_signed_ode {h f f' ε : ℝ → ℝ} {a A r₀ R Cf Ch : ℝ}
    (hr₀ : 0 < r₀) (hR : r₀ ≤ R)
    (hderiv : ∀ x, r₀ ≤ x → HasDerivAt f (f' x) x)
    (hε1 : ∀ x, r₀ ≤ x → |ε x| ≤ 1)
    (hode : ∀ x, r₀ ≤ x → f' x = (a * f x + (A + ε x) * h x) / x)
    (hCf : ∀ x ∈ uIcc r₀ R, |f x| ≤ Cf)
    (hCh : ∀ x ∈ uIcc r₀ R, |h x| ≤ Ch) :
    f R * R ^ (-a) - f r₀ * r₀ ^ (-a) =
      ∫ s in r₀..R, (A + ε s) * (h s * s ^ (-(a + 1))) := by
  have hr₀mem : r₀ ∈ uIcc r₀ R := left_mem_uIcc
  have hCf0 : 0 ≤ Cf := (abs_nonneg (f r₀)).trans (hCf r₀ hr₀mem)
  have hCh0 : 0 ≤ Ch := (abs_nonneg (h r₀)).trans (hCh r₀ hr₀mem)
  have hK0 : 0 ≤ |a| * Cf + (|A| + 1) * Ch :=
    add_nonneg (mul_nonneg (abs_nonneg a) hCf0) (mul_nonneg (by positivity) hCh0)
  have hf'bound : ∀ x ∈ uIcc r₀ R, ‖f' x‖ ≤ (|a| * Cf + (|A| + 1) * Ch) / r₀ := by
    intro x hx
    have hfx : |f x| ≤ Cf := hCf x hx
    have hhx : |h x| ≤ Ch := hCh x hx
    rw [uIcc_of_le hR] at hx
    have hx0 : 0 < x := lt_of_lt_of_le hr₀ hx.1
    have h2 : |A + ε x| ≤ |A| + 1 := by
      have := abs_add_le A (ε x)
      linarith [hε1 x hx.1]
    have hsum : |a * f x + (A + ε x) * h x| ≤ |a| * Cf + (|A| + 1) * Ch := by
      calc |a * f x + (A + ε x) * h x| ≤ |a| * |f x| + |A + ε x| * |h x| := by
            rw [← abs_mul, ← abs_mul]
            exact abs_add_le _ _
        _ ≤ |a| * Cf + (|A| + 1) * Ch :=
            add_le_add (mul_le_mul_of_nonneg_left hfx (abs_nonneg a))
              (mul_le_mul h2 hhx (abs_nonneg _) (by positivity))
    rw [hode x hx.1, Real.norm_eq_abs, abs_div, abs_of_pos hx0]
    calc |a * f x + (A + ε x) * h x| / x
        ≤ (|a| * Cf + (|A| + 1) * Ch) / x := div_le_div_of_nonneg_right hsum hx0.le
      _ ≤ (|a| * Cf + (|A| + 1) * Ch) / r₀ := div_le_div_of_nonneg_left hK0 hr₀ hx.1
  have hfAC : AbsolutelyContinuousOnInterval f r₀ R :=
    absolutelyContinuousOnInterval_of_hasDerivAt_of_norm_le
      (fun x hx => hderiv x (by rw [uIcc_of_le hR] at hx; exact hx.1)) hf'bound
  have hpowAC : AbsolutelyContinuousOnInterval (fun x : ℝ => x ^ (-a)) r₀ R :=
    absolutelyContinuousOnInterval_rpow (-a) fun x hx => by
      rw [uIcc_of_le hR] at hx
      exact (lt_of_lt_of_le hr₀ hx.1).ne'
  have hqAC : AbsolutelyContinuousOnInterval (fun x => f x * x ^ (-a)) r₀ R :=
    hfAC.fun_mul hpowAC
  have hqderiv : ∀ᵐ x ∂volume, x ∈ uIoc r₀ R →
      deriv (fun x => f x * x ^ (-a)) x = (A + ε x) * (h x * x ^ (-(a + 1))) := by
    filter_upwards with x hxmem
    rw [uIoc_of_le hR] at hxmem
    have hx0 : 0 < x := lt_of_lt_of_le hr₀ hxmem.1.le
    have hxd := (hderiv x hxmem.1.le).fun_mul
      (Real.hasDerivAt_rpow_const (x := x) (p := -a) (Or.inl hx0.ne'))
    have h1 : x ^ (-a) = x * x ^ (-(a + 1)) := by
      have h := Real.rpow_add hx0 (1 : ℝ) (-(a + 1))
      rw [Real.rpow_one] at h
      rw [← h]
      congr 1
      ring
    have h2 : x ^ (-a - 1) = x ^ (-(a + 1)) := by
      congr 1
      ring
    rw [hxd.deriv, hode x hxmem.1.le, h1, h2]
    field_simp
    ring
  calc f R * R ^ (-a) - f r₀ * r₀ ^ (-a)
      = ∫ s in r₀..R, deriv (fun x => f x * x ^ (-a)) s := hqAC.integral_deriv_eq_sub.symm
    _ = ∫ s in r₀..R, (A + ε s) * (h s * s ^ (-(a + 1))) :=
        intervalIntegral.integral_congr_ae hqderiv

/-! ### Local boundedness of regularly varying functions -/

/-- **Local boundedness on a tail.** A measurable regularly varying function, of any index, is
bounded on every compact interval of some tail `[X, ∞)` with `X ≥ 1` (Potter's upper bound). -/
theorem RegularlyVarying.exists_forall_abs_le {f : ℝ → ℝ} {ρ : ℝ} (hf : RegularlyVarying ρ f)
    (hmeas : Measurable f) :
    ∃ X : ℝ, 1 ≤ X ∧ ∀ M, ∃ C, ∀ x, X ≤ x → x ≤ M → |f x| ≤ C := by
  obtain ⟨X, hX1, hpot⟩ := potterBounds_of_regularlyVarying hmeas hf 1 one_pos
  refine ⟨X, hX1, fun M => ⟨2 * max 1 ((max M X / X) ^ (ρ + 1)) * |f X|, fun x hx hxM => ?_⟩⟩
  have hX0 : 0 < X := by linarith
  have hp := (hpot x X le_rfl hx).2
  have hbase : 1 ≤ x / X := (one_le_div hX0).2 hx
  have hpow : (x / X) ^ (ρ + 1) ≤ max 1 ((max M X / X) ^ (ρ + 1)) := by
    rcases le_total 0 (ρ + 1) with hp0 | hp0
    · refine le_max_of_le_right (Real.rpow_le_rpow (by linarith) ?_ hp0)
      exact div_le_div_of_nonneg_right (le_trans hxM (le_max_left _ _)) hX0.le
    · exact le_max_of_le_left (Real.rpow_le_one_of_one_le_of_nonpos hbase hp0)
  calc |f x| ≤ (1 + 1) * (x / X) ^ (ρ + 1) * |f X| := hp
    _ ≤ 2 * max 1 ((max M X / X) ^ (ρ + 1)) * |f X| := by
        rw [one_add_one_eq_two]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by norm_num))
          (abs_nonneg _)

/-! ### The integrating factor -/

/-- **The integrating factor is regularly varying of index `a`**, for every real `a`:
`r ↦ r ^ a * exp (∫ s in r₀..r, (Ioi r₀).indicator ε s / s)` with `ε` measurable, `ε → 0` and
`|ε| ≤ 1` on `[r₀, ∞)`. -/
theorem regularlyVarying_rpow_mul_exp_integral {ε : ℝ → ℝ} {r₀ : ℝ} (a : ℝ) (hr₀ : 0 < r₀)
    (hεm : Measurable ε) (hε0 : Tendsto ε atTop (𝓝 0)) (hε1 : ∀ x, r₀ ≤ x → |ε x| ≤ 1) :
    RegularlyVarying a
      (fun r : ℝ => r ^ a * Real.exp (∫ s in r₀..r, (Ioi r₀).indicator ε s / s)) := by
  have hw := regularlyVarying_rpow_mul_exp_neg_integral (δ := fun x => -ε x) one_pos hr₀
    hεm.neg (by simpa using hε0.neg) (fun x hx => by rw [abs_neg]; exact hε1 x hx)
  have hm := (regularlyVarying_rpow (a - 1)).mul hw
  rw [sub_add_cancel] at hm
  refine hm.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with r hr
  have hint : (∫ s in r₀..r, (Ioi r₀).indicator (fun x => -ε x) s / s) =
      -∫ s in r₀..r, (Ioi r₀).indicator ε s / s := by
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun s _ => ?_
    by_cases hs : s ∈ Ioi r₀ <;> simp [hs, neg_div]
  rw [hint, one_mul, neg_neg, ← mul_assoc, ← Real.rpow_add hr, sub_add_cancel]

/-- **Variation of constants.** Let `f` be absolutely continuous on `[r₀, R]`, `0 < r₀`, with
`r f'(r) = (a + ε r) f r + (A + δ r) h r` almost everywhere on `[r₀, ∞)`, where `ε` is measurable
and bounded on `[r₀, ∞)`. With `G r = r ^ a * exp (∫ s in r₀..r, (Ioi r₀).indicator ε s / s)`,
`f R / G R - f r₀ / r₀ ^ a = ∫ s in r₀..R, (A + δ s) * (h s / (s * G s))`. -/
theorem div_sub_div_eq_integral_of_ae_mul_deriv_eq {f h ε δ : ℝ → ℝ} {a A r₀ R C : ℝ}
    (hr₀ : 0 < r₀) (hR : r₀ ≤ R) (hεm : Measurable ε) (hεC : ∀ x, r₀ ≤ x → |ε x| ≤ C)
    (hf : AbsolutelyContinuousOnInterval f r₀ R)
    (hode : ∀ᵐ r, r₀ ≤ r → r * deriv f r = (a + ε r) * f r + (A + δ r) * h r) :
    f R / (R ^ a * Real.exp (∫ s in r₀..R, (Ioi r₀).indicator ε s / s)) - f r₀ / r₀ ^ a =
      ∫ s in r₀..R, (A + δ s) *
        (h s / (s * (s ^ a * Real.exp (∫ t in r₀..s, (Ioi r₀).indicator ε t / t)))) := by
  set E : ℝ → ℝ := fun r => ∫ s in r₀..r, (Ioi r₀).indicator ε s / s with hE
  set G : ℝ → ℝ := fun r => r ^ a * Real.exp (E r) with hG
  have hGpos : ∀ r, 0 < r → 0 < G r := fun r hr =>
    mul_pos (Real.rpow_pos_of_pos hr a) (Real.exp_pos _)
  have hEint := intervalIntegrable_indicator_Ioi_div hr₀ hεm hεC r₀ R
  have hEac : AbsolutelyContinuousOnInterval E r₀ R :=
    hEint.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc
  have hGac : AbsolutelyContinuousOnInterval G r₀ R :=
    (absolutelyContinuousOnInterval_rpow a fun x hx => by
      rw [uIcc_of_le hR] at hx
      exact (lt_of_lt_of_le hr₀ hx.1).ne').fun_mul (AbsolutelyContinuousOnInterval.exp hEac)
  have hGinv : AbsolutelyContinuousOnInterval (fun r => (G r)⁻¹) r₀ R :=
    absolutelyContinuousOnInterval_inv hR hGac fun r hr => hGpos r (lt_of_lt_of_le hr₀ hr.1)
  have hu : AbsolutelyContinuousOnInterval (fun r => f r / G r) r₀ R := by
    simpa only [div_eq_mul_inv] using hf.fun_mul hGinv
  have hderiv : ∀ᵐ x, x ∈ uIoc r₀ R → deriv (fun r => f r / G r) x =
      (A + δ x) * (h x / (x * G x)) := by
    filter_upwards [hEint.ae_hasDerivAt_integral, hf.ae_differentiableAt, hode]
      with x hxE hxf hxo hx
    rw [uIoc_of_le hR] at hx
    have hxI : x ∈ uIcc r₀ R := by
      rw [uIcc_of_le hR]
      exact Ioc_subset_Icc_self hx
    have hx0 : 0 < x := lt_of_lt_of_le hr₀ hx.1.le
    have hdE : HasDerivAt E (ε x / x) x := by
      have h1 := hxE hxI r₀ left_mem_uIcc
      rw [Set.indicator_of_mem (show x ∈ Ioi r₀ from hx.1)] at h1
      exact h1
    have hdG : HasDerivAt G
        (a * x ^ (a - 1) * Real.exp (E x) + x ^ a * (Real.exp (E x) * (ε x / x))) x :=
      (Real.hasDerivAt_rpow_const (p := a) (Or.inl hx0.ne')).fun_mul hdE.exp
    have hdu := (hxf hxI).hasDerivAt.fun_div hdG (hGpos x hx0).ne'
    rw [hdu.deriv]
    have hpow : x ^ a = x ^ (a - 1) * x := by
      rw [← Real.rpow_add_one hx0.ne', sub_add_cancel]
    have hGx : G x = x ^ (a - 1) * x * Real.exp (E x) := by
      simp only [hG, hpow]
    have hdf : deriv f x = ((a + ε x) * f x + (A + δ x) * h x) / x := by
      rw [← hxo hx.1.le]
      field_simp
    have hP : 0 < x ^ (a - 1) := Real.rpow_pos_of_pos hx0 _
    have hX : 0 < Real.exp (E x) := Real.exp_pos _
    rw [hGx, hdf, hpow]
    field_simp
    ring
  have hG0 : G r₀ = r₀ ^ a := by simp [hG, hE]
  have key := hu.integral_deriv_eq_sub
  rw [intervalIntegral.integral_congr_ae hderiv] at key
  simp only [hG0] at key
  exact key.symm

/-! ### The asymptotic theorem -/

/-- **The asymptotic theorem on a normalized tail.** Let `1 ≤ r₀`, `a < b`, `h` measurable,
regularly varying of index `b` and interval integrable on `[r₀, ∞)`, `ε, δ` measurable with
`ε, δ → 0` and `|ε|, |δ| ≤ 1` on `[r₀, ∞)`, and `f` absolutely continuous on every `[r₀, R]` with
`r f'(r) = (a + ε r) f r + (A + δ r) h r` almost everywhere on `[r₀, ∞)`. Then
`f / h → A / (b - a)`. -/
theorem tendsto_div_of_ae_mul_deriv_eq_of_abs_le {f h ε δ : ℝ → ℝ} {a b A r₀ : ℝ}
    (hab : a < b) (hr₀ : 1 ≤ r₀) (hhm : Measurable h) (hrv : RegularlyVarying b h)
    (hhi : ∀ x y, r₀ ≤ x → x ≤ y → IntervalIntegrable h volume x y)
    (hεm : Measurable ε) (hε0 : Tendsto ε atTop (𝓝 0)) (hε1 : ∀ x, r₀ ≤ x → |ε x| ≤ 1)
    (hδm : Measurable δ) (hδ0 : Tendsto δ atTop (𝓝 0)) (hδ1 : ∀ x, r₀ ≤ x → |δ x| ≤ 1)
    (hf : ∀ R, r₀ ≤ R → AbsolutelyContinuousOnInterval f r₀ R)
    (hode : ∀ᵐ r, r₀ ≤ r → r * deriv f r = (a + ε r) * f r + (A + δ r) * h r) :
    Tendsto (fun r => f r / h r) atTop (𝓝 (A / (b - a))) := by
  have hr₀0 : 0 < r₀ := by linarith
  have hba : 0 < b - a := sub_pos.2 hab
  set E : ℝ → ℝ := fun r => ∫ s in r₀..r, (Ioi r₀).indicator ε s / s with hE
  set G : ℝ → ℝ := fun r => r ^ a * Real.exp (E r) with hG
  set q : ℝ → ℝ := fun r => h r / G r with hq
  have hGpos : ∀ r, 0 < r → 0 < G r := fun r hr =>
    mul_pos (Real.rpow_pos_of_pos hr a) (Real.exp_pos _)
  have hEc : Continuous E := continuous_intervalIntegral_indicator_Ioi_div hr₀0 hεm hε1
  have hGm : Measurable G :=
    (measurable_id.pow_const a).mul (Real.measurable_exp.comp hEc.measurable)
  have hGrv : RegularlyVarying a G := regularlyVarying_rpow_mul_exp_integral a hr₀0 hεm hε0 hε1
  have hqm : Measurable q := hhm.div hGm
  have hqrv : RegularlyVarying (b - a) q := by
    have h1 := hrv.mul hGrv.inv
    rw [← sub_eq_add_neg] at h1
    exact h1.congr' (Eventually.of_forall fun r => (div_eq_mul_inv _ _).symm)
  -- interval integrability of `q s / s` on the tail
  have hgi : ∀ x y, r₀ ≤ x → x ≤ y → IntervalIntegrable (fun s => q s / s) volume x y := by
    intro x y hx hxy
    have hc : ContinuousOn (fun s : ℝ => (s * G s)⁻¹) (uIcc x y) := by
      intro s hs
      rw [uIcc_of_le hxy] at hs
      have hs0 : 0 < s := by linarith [hs.1]
      exact ((continuousAt_id.mul ((Real.continuousAt_rpow_const s a (Or.inl hs0.ne')).mul
        (Real.continuous_exp.comp hEc).continuousAt)).inv₀
          (mul_pos hs0 (hGpos s hs0)).ne').continuousWithinAt
    have hfun : (fun s => q s / s) = fun s => h s * (s * G s)⁻¹ := by
      funext s
      simp only [hq]
      rw [div_div, div_eq_mul_inv, mul_comm (G s)]
    rw [hfun]
    exact (hhi x y hx hxy).mul_continuousOn hc
  have hδg : ∀ r, r₀ ≤ r → IntervalIntegrable (fun s => δ s * (q s / s)) volume r₀ r := by
    intro r hr
    refine (hgi r₀ r le_rfl hr).mono_fun (hδm.mul (hqm.div measurable_id)).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
    rw [uIoc_of_le hr] at hs
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg _) (hδ1 s hs.1.le)
  -- Karamata's theorem for `q`, and the `δ`-part
  have hK : Tendsto (fun r => (∫ s in r₀..r, q s / s) / q r) atTop (𝓝 (1 / (b - a))) :=
    tendsto_karamataPrimitive_tail hba hqm hqrv hgi
  have hK1 := tendsto_mul_one_sub_karamata_integral_tail (g := fun s => q s / s) (δ := δ)
    (c := b - a - 1) (by linarith) hr₀0 hr₀ (hqm.div measurable_id) hqrv.div_id hgi hδm hδ0 hδ1
  rw [show b - a - 1 + 1 = b - a by ring] at hK1
  have hK1' : Tendsto (fun r => (∫ s in r₀..r, (1 - δ s) * (q s / s)) / q r) atTop
      (𝓝 (1 / (b - a))) := by
    refine hK1.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with r hr
    rw [mul_div_cancel₀ _ hr.ne']
  have hKδ : Tendsto (fun r => (∫ s in r₀..r, δ s * (q s / s)) / q r) atTop (𝓝 0) := by
    have h1 := hK.sub hK1'
    rw [sub_self] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_ge_atTop r₀] with r hr
    have h2 : (∫ s in r₀..r, (1 - δ s) * (q s / s)) =
        (∫ s in r₀..r, q s / s) - ∫ s in r₀..r, δ s * (q s / s) := by
      rw [← intervalIntegral.integral_sub (hgi r₀ r le_rfl hr) (hδg r hr)]
      exact intervalIntegral.integral_congr fun s _ => by ring
    rw [h2]
    ring
  -- `q → ∞` removes the initial value
  have hq0 : Tendsto (fun r => (f r₀ / r₀ ^ a) / q r) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (hqrv.tendsto_atTop hba hqm)
  have hlim := (hq0.add (hK.const_mul A)).add hKδ
  rw [zero_add, add_zero, mul_one_div] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop r₀, hrv.eventually_pos] with r hr hhr
  have hr0 : 0 < r := by linarith
  have hGr := hGpos r hr0
  have hsplit : (∫ s in r₀..r, (A + δ s) * (h s / (s * G s))) =
      A * (∫ s in r₀..r, q s / s) + ∫ s in r₀..r, δ s * (q s / s) := by
    rw [← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add ((hgi r₀ r le_rfl hr).const_mul A) (hδg r hr)]
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [hq]
    ring
  have hinc : f r / G r - f r₀ / r₀ ^ a = ∫ s in r₀..r, (A + δ s) * (h s / (s * G s)) :=
    div_sub_div_eq_integral_of_ae_mul_deriv_eq hr₀0 hr hεm hε1 (hf r hr) hode
  have hfr : f r / h r = (f r / G r) / q r := by
    simp only [hq]
    field_simp
  rw [hfr, show f r / G r = f r₀ / r₀ ^ a + (f r / G r - f r₀ / r₀ ^ a) by ring, hinc, hsplit]
  ring

/-- **A signed linear equation with regularly varying forcing.** Let `a < b` and `A` be real,
`h` regularly varying of index `b`, `ε, δ` measurable on `[r₀, ∞)` with `ε, δ → 0`, and `f`
absolutely continuous on every `[r₀, R]` with, almost everywhere on `[r₀, ∞)`,
`r f'(r) = (a + ε r) f r + (A + δ r) h r`. Then `f / h → A / (b - a)`.

No sign condition on `a`, `b`, `A` or `f`, no bound `|f| = O(h)`, no positivity or local
integrability of `h` on `[r₀, ∞)` and no local boundedness of `ε, δ` is assumed: all of these
hold, or are irrelevant, on a later tail. -/
theorem tendsto_div_of_ae_mul_deriv_eq {f h ε δ : ℝ → ℝ} {a b A r₀ : ℝ}
    (hab : a < b) (hrv : RegularlyVarying b h)
    (hεm : Measurable ((Ici r₀).domRestrict ε)) (hε0 : Tendsto ε atTop (𝓝 0))
    (hδm : Measurable ((Ici r₀).domRestrict δ)) (hδ0 : Tendsto δ atTop (𝓝 0))
    (hf : ∀ R, r₀ ≤ R → AbsolutelyContinuousOnInterval f r₀ R)
    (hode : ∀ᵐ r, r₀ ≤ r → r * deriv f r = (a + ε r) * f r + (A + δ r) * h r) :
    Tendsto (fun r => f r / h r) atTop (𝓝 (A / (b - a))) := by
  obtain ⟨c, hc⟩ := hrv.measurable_tail
  obtain ⟨H, hHm, hHeq⟩ := exists_measurable_eqOn_Ici hc
  obtain ⟨E, hEm, hEeq⟩ := exists_measurable_eqOn_Ici hεm
  obtain ⟨D, hDm, hDeq⟩ := exists_measurable_eqOn_Ici hδm
  have hHev : h =ᶠ[atTop] H := by
    filter_upwards [eventually_ge_atTop c] with x hx
    exact (hHeq x hx).symm
  have hEev : ε =ᶠ[atTop] E := by
    filter_upwards [eventually_ge_atTop r₀] with x hx
    exact (hEeq x hx).symm
  have hDev : δ =ᶠ[atTop] D := by
    filter_upwards [eventually_ge_atTop r₀] with x hx
    exact (hDeq x hx).symm
  have hHrv := hrv.congr' hHev
  have hE0 := hε0.congr' hEev
  have hD0 := hδ0.congr' hDev
  obtain ⟨X, hX1, hXb⟩ := hHrv.exists_forall_abs_le hHm
  obtain ⟨B₁, hB₁⟩ := eventually_atTop.1 (hE0.eventually (Metric.closedBall_mem_nhds (0 : ℝ)
    one_pos))
  obtain ⟨B₂, hB₂⟩ := eventually_atTop.1 (hD0.eventually (Metric.closedBall_mem_nhds (0 : ℝ)
    one_pos))
  set T := max (max r₀ c) (max X (max B₁ B₂)) with hT
  have hrT : r₀ ≤ T := le_trans (le_max_left _ _) (le_max_left _ _)
  have hcT : c ≤ T := le_trans (le_max_right _ _) (le_max_left _ _)
  have hXT : X ≤ T := le_trans (le_max_left _ _) (le_max_right _ _)
  have hB₁T : B₁ ≤ T :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
  have hB₂T : B₂ ≤ T :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)
  have hT1 : 1 ≤ T := le_trans hX1 hXT
  have habs : ∀ {u : ℝ → ℝ} {B : ℝ}, (∀ x, B ≤ x → u x ∈ Metric.closedBall (0 : ℝ) 1) →
      B ≤ T → ∀ x, T ≤ x → |u x| ≤ 1 := by
    intro u B hu hBT x hx
    have h1 := hu x (le_trans hBT hx)
    rwa [Metric.mem_closedBall, Real.dist_eq, sub_zero] at h1
  have hHi : ∀ x y, T ≤ x → x ≤ y → IntervalIntegrable H volume x y := by
    intro x y hx hxy
    obtain ⟨C, hC⟩ := hXb y
    refine IntegrableOn.intervalIntegrable (IntegrableOn.of_bound
      (isCompact_uIcc (a := x) (b := y)).measure_lt_top hHm.aestronglyMeasurable C ?_)
    filter_upwards [ae_restrict_mem measurableSet_uIcc] with s hs
    rw [uIcc_of_le hxy] at hs
    rw [Real.norm_eq_abs]
    exact hC s (le_trans hXT (le_trans hx hs.1)) hs.2
  have hfT : ∀ R, T ≤ R → AbsolutelyContinuousOnInterval f T R := fun R hR =>
    (hf R (le_trans hrT hR)).mono (by
      rw [uIcc_of_le hR, uIcc_of_le (le_trans hrT hR)]
      exact Icc_subset_Icc_left hrT)
  have hodeT : ∀ᵐ r, T ≤ r → r * deriv f r = (a + E r) * f r + (A + D r) * H r := by
    filter_upwards [hode] with r hr hTr
    rw [hHeq r (le_trans hcT hTr), hEeq r (le_trans hrT hTr), hDeq r (le_trans hrT hTr)]
    exact hr (le_trans hrT hTr)
  have hlim := tendsto_div_of_ae_mul_deriv_eq_of_abs_le hab hT1 hHm hHrv hHi hEm hE0
    (habs hB₁ hB₁T) hDm hD0 (habs hB₂ hB₂T) hfT hodeT
  refine hlim.congr' ?_
  filter_upwards [hHev] with r hr
  rw [hr]

/-! ### Lemma I.5.26 with differentiable `f` -/

/-- **Lemma I.5.26, two-error form.** Let `a < b`, `h` regularly varying of index `b`, `f`
eventually differentiable with derivative `f'`, and
`f' x = ((a + ε₁ x) f x + (A + ε₂ x) h x) / x` eventually, where `ε₁, ε₂ → 0` are arbitrary (not
assumed measurable). Then `f / h → A / (b - a)`. No bound `|f| = O(h)` is assumed.

The errors are replaced by measurable ones: with `Φ = r f' - a f - A h` and
`s = Φ / (|f| + h)`, the pair `(s f / |f|, s)` solves the same equation and `|s| ≤ |ε₁| + |ε₂|`. -/
theorem tendsto_div_of_two_error_ode {f f' h ε₁ ε₂ : ℝ → ℝ} {a b A : ℝ}
    (hab : a < b) (hrv : RegularlyVarying b h)
    (hderiv : ∀ᶠ x in atTop, HasDerivAt f (f' x) x)
    (hε₁ : Tendsto ε₁ atTop (𝓝 0)) (hε₂ : Tendsto ε₂ atTop (𝓝 0))
    (hode : ∀ᶠ x in atTop, f' x = ((a + ε₁ x) * f x + (A + ε₂ x) * h x) / x) :
    Tendsto (fun r => f r / h r) atTop (𝓝 (A / (b - a))) := by
  obtain ⟨c, hc⟩ := hrv.measurable_tail
  obtain ⟨H, hHm, hHeq⟩ := exists_measurable_eqOn_Ici hc
  have hHev : h =ᶠ[atTop] H := by
    filter_upwards [eventually_ge_atTop c] with x hx
    exact (hHeq x hx).symm
  obtain ⟨X, hX1, hXb⟩ := (hrv.congr' hHev).exists_forall_abs_le hHm
  obtain ⟨B₁, hB₁⟩ := eventually_atTop.1 hderiv
  obtain ⟨B₂, hB₂⟩ := eventually_atTop.1 hode
  obtain ⟨B₃, hB₃⟩ := eventually_atTop.1 hrv.eventually_pos
  obtain ⟨B₄, hB₄⟩ := eventually_atTop.1 (hε₁.eventually (Metric.closedBall_mem_nhds (0 : ℝ)
    one_pos))
  obtain ⟨B₅, hB₅⟩ := eventually_atTop.1 (hε₂.eventually (Metric.closedBall_mem_nhds (0 : ℝ)
    one_pos))
  set T := max (max (max c X) (max B₁ B₂)) (max B₃ (max B₄ B₅)) with hT
  have hcT : c ≤ T := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_left _ _))
  have hXT : X ≤ T := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_left _ _))
  have hB₁T : B₁ ≤ T :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_left _ _))
  have hB₂T : B₂ ≤ T :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_left _ _))
  have hB₃T : B₃ ≤ T := le_trans (le_max_left _ _) (le_max_right _ _)
  have hB₄T : B₄ ≤ T :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hB₅T : B₅ ≤ T :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hT1 : 1 ≤ T := le_trans hX1 hXT
  have habs : ∀ {u : ℝ → ℝ} {B : ℝ}, (∀ x, B ≤ x → u x ∈ Metric.closedBall (0 : ℝ) 1) →
      B ≤ T → ∀ x, T ≤ x → |u x| ≤ 1 := by
    intro u B hu hBT x hx
    have h1 := hu x (le_trans hBT hx)
    rwa [Metric.mem_closedBall, Real.dist_eq, sub_zero] at h1
  have hfc : ContinuousOn f (Ici T) := fun x hx =>
    (hB₁ x (le_trans hB₁T hx)).continuousAt.continuousWithinAt
  -- the measurable errors
  set s : ℝ → ℝ := fun r => (r * deriv f r - a * f r - A * h r) / (|f r| + h r) with hs
  have hhpos : ∀ x, T ≤ x → 0 < h x := fun x hx => hB₃ x (le_trans hB₃T hx)
  have hnum : ∀ x, T ≤ x → x * deriv f x - a * f x - A * h x = ε₁ x * f x + ε₂ x * h x := by
    intro x hx
    have hx0 : 0 < x := by linarith
    rw [(hB₁ x (le_trans hB₁T hx)).deriv, hB₂ x (le_trans hB₂T hx)]
    field_simp
    ring
  have hkey : ∀ x, T ≤ x → s x * (|f x| + h x) = x * deriv f x - a * f x - A * h x := by
    intro x hx
    have hden : 0 < |f x| + h x := add_pos_of_nonneg_of_pos (abs_nonneg _) (hhpos x hx)
    simp only [hs]
    field_simp
  have hs_bound : ∀ x, T ≤ x → |s x| ≤ |ε₁ x| + |ε₂ x| := by
    intro x hx
    have hhx := hhpos x hx
    have hden : 0 < |f x| + h x := add_pos_of_nonneg_of_pos (abs_nonneg _) hhx
    have h1 : |s x| * (|f x| + h x) ≤ (|ε₁ x| + |ε₂ x|) * (|f x| + h x) := by
      rw [← abs_of_pos hden, ← abs_mul, hkey x hx, hnum x hx, abs_of_pos hden]
      calc |ε₁ x * f x + ε₂ x * h x| ≤ |ε₁ x * f x| + |ε₂ x * h x| := abs_add_le _ _
        _ = |ε₁ x| * |f x| + |ε₂ x| * h x := by rw [abs_mul, abs_mul, abs_of_pos hhx]
        _ ≤ (|ε₁ x| + |ε₂ x|) * (|f x| + h x) := by
            nlinarith [abs_nonneg (ε₁ x), abs_nonneg (ε₂ x), abs_nonneg (f x)]
    exact le_of_mul_le_mul_right h1 hden
  have hs0 : Tendsto s atTop (𝓝 0) := by
    have hup : Tendsto (fun x => |ε₁ x| + |ε₂ x|) atTop (𝓝 0) := by
      simpa using hε₁.abs.add hε₂.abs
    refine squeeze_zero_norm' ?_ hup
    filter_upwards [eventually_ge_atTop T] with x hx
    rw [Real.norm_eq_abs]
    exact hs_bound x hx
  have hsgn : ∀ x, |(f x / |f x|)| ≤ 1 := by
    intro x
    rcases eq_or_ne (f x) 0 with h0 | h0
    · simp [h0]
    · rw [abs_div, abs_abs, div_self (abs_ne_zero.2 h0)]
  have hεs0 : Tendsto (fun r => s r * (f r / |f r|)) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun x => ?_) (by simpa using hs0.abs)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (hsgn x)
  -- measurability on the tail
  have hfm : Measurable ((Ici T).domRestrict f) :=
    (continuousOn_iff_continuous_domRestrict.1 hfc).measurable
  have hhm : Measurable ((Ici T).domRestrict h) := measurable_restrict_Ici_mono hc hcT
  have hdm : Measurable ((Ici T).domRestrict (deriv f)) :=
    (measurable_deriv f).comp measurable_subtype_coe
  have hid : Measurable (fun x : Ici T => (x : ℝ)) := measurable_subtype_coe
  have hfabs : Measurable (fun x : Ici T => |f x|) := continuous_abs.measurable.comp hfm
  have hsm : Measurable ((Ici T).domRestrict s) :=
    (((hid.mul hdm).sub (hfm.const_mul a)).sub (hhm.const_mul A)).div (hfabs.add hhm)
  have hεm : Measurable ((Ici T).domRestrict fun r => s r * (f r / |f r|)) :=
    hsm.mul (hfm.div hfabs)
  -- local absolute continuity
  have hfac : ∀ R, T ≤ R → AbsolutelyContinuousOnInterval f T R := by
    intro R hR
    obtain ⟨Cf, hCf⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (hfc.mono (Icc_subset_Ici_self : Icc T R ⊆ Ici T))
    obtain ⟨Ch, hCh⟩ := hXb R
    refine absolutelyContinuousOnInterval_of_hasDerivAt_of_norm_le (f' := f')
      (C := ((|a| + 1) * Cf + (|A| + 1) * Ch) / T) (fun x hx => ?_) (fun x hx => ?_)
    · rw [uIcc_of_le hR] at hx
      exact hB₁ x (le_trans hB₁T hx.1)
    · rw [uIcc_of_le hR] at hx
      have hx0 : 0 < x := by linarith [hx.1]
      have hfx : |f x| ≤ Cf := by simpa [Real.norm_eq_abs] using hCf x hx
      have hhx : |h x| ≤ Ch := by
        rw [← hHeq x (le_trans hcT hx.1)]
        exact hCh x (le_trans hXT hx.1) hx.2
      have h1 : |a + ε₁ x| ≤ |a| + 1 :=
        (abs_add_le _ _).trans (by linarith [habs hB₄ hB₄T x hx.1])
      have h2 : |A + ε₂ x| ≤ |A| + 1 :=
        (abs_add_le _ _).trans (by linarith [habs hB₅ hB₅T x hx.1])
      have hsum : |(a + ε₁ x) * f x + (A + ε₂ x) * h x| ≤ (|a| + 1) * Cf + (|A| + 1) * Ch := by
        calc |(a + ε₁ x) * f x + (A + ε₂ x) * h x|
            ≤ |a + ε₁ x| * |f x| + |A + ε₂ x| * |h x| := by
              rw [← abs_mul, ← abs_mul]
              exact abs_add_le _ _
          _ ≤ (|a| + 1) * Cf + (|A| + 1) * Ch :=
              add_le_add (mul_le_mul h1 hfx (abs_nonneg _) (by positivity))
                (mul_le_mul h2 hhx (abs_nonneg _) (by positivity))
      have hK0 : 0 ≤ (|a| + 1) * Cf + (|A| + 1) * Ch := le_trans (abs_nonneg _) hsum
      rw [hB₂ x (le_trans hB₂T hx.1), Real.norm_eq_abs, abs_div, abs_of_pos hx0]
      calc |(a + ε₁ x) * f x + (A + ε₂ x) * h x| / x
          ≤ ((|a| + 1) * Cf + (|A| + 1) * Ch) / x := div_le_div_of_nonneg_right hsum hx0.le
        _ ≤ ((|a| + 1) * Cf + (|A| + 1) * Ch) / T :=
            div_le_div_of_nonneg_left hK0 (by linarith) hx.1
  -- the equation with the measurable errors
  have hodeT : ∀ᵐ r, T ≤ r →
      r * deriv f r = (a + s r * (f r / |f r|)) * f r + (A + s r) * h r := by
    refine ae_of_all _ fun x hx => ?_
    have hff : f x / |f x| * f x = |f x| := by
      rw [div_mul_eq_mul_div, ← abs_mul_abs_self (f x), mul_self_div_self]
    linear_combination (-1 : ℝ) * hkey x hx + (-s x) * hff
  exact tendsto_div_of_ae_mul_deriv_eq hab hrv hεm hεs0 hsm hs0 hfac hodeT

/-- **Lemma I.5.26, two-error form, little-`o` conclusion**:
`f r = (A / (b - a) ± o(1)) h r`. -/
theorem isLittleO_sub_const_mul_of_two_error_ode {f f' h ε₁ ε₂ : ℝ → ℝ} {a b A : ℝ}
    (hab : a < b) (hrv : RegularlyVarying b h)
    (hderiv : ∀ᶠ x in atTop, HasDerivAt f (f' x) x)
    (hε₁ : Tendsto ε₁ atTop (𝓝 0)) (hε₂ : Tendsto ε₂ atTop (𝓝 0))
    (hode : ∀ᶠ x in atTop, f' x = ((a + ε₁ x) * f x + (A + ε₂ x) * h x) / x) :
    (fun r => f r - (A / (b - a)) * h r) =o[atTop] h :=
  isLittleO_sub_const_mul_of_tendsto_div (hrv.eventually_pos.mono fun _ hx => hx.ne')
    (tendsto_div_of_two_error_ode hab hrv hderiv hε₁ hε₂ hode)

/-- **Lemma I.5.26, folded form.** If `h` is regularly varying of index `b > a`, `f` is eventually
differentiable with derivative `f'`, and `(r f' r - a f r) / h r → A`, then
`f / h → A / (b - a)`. -/
theorem tendsto_div_of_tendsto_mul_deriv_sub_div {f f' h : ℝ → ℝ} {a b A : ℝ} (hab : a < b)
    (hrv : RegularlyVarying b h) (hderiv : ∀ᶠ x in atTop, HasDerivAt f (f' x) x)
    (hode : Tendsto (fun r => (r * f' r - a * f r) / h r) atTop (𝓝 A)) :
    Tendsto (fun r => f r / h r) atTop (𝓝 (A / (b - a))) := by
  refine tendsto_div_of_two_error_ode (ε₁ := fun _ => 0)
    (ε₂ := fun r => (r * f' r - a * f r) / h r - A) hab hrv hderiv tendsto_const_nhds
    (by simpa using hode.sub_const A) ?_
  filter_upwards [hrv.eventually_pos, eventually_gt_atTop 0] with x hx hx0
  field_simp
  ring

/-- **Lemma I.5.26, folded form, little-`o` conclusion**. -/
theorem isLittleO_sub_const_mul_of_tendsto_mul_deriv_sub_div {f f' h : ℝ → ℝ} {a b A : ℝ}
    (hab : a < b) (hrv : RegularlyVarying b h) (hderiv : ∀ᶠ x in atTop, HasDerivAt f (f' x) x)
    (hode : Tendsto (fun r => (r * f' r - a * f r) / h r) atTop (𝓝 A)) :
    (fun r => f r - (A / (b - a)) * h r) =o[atTop] h :=
  isLittleO_sub_const_mul_of_tendsto_div (hrv.eventually_pos.mono fun _ hx => hx.ne')
    (tendsto_div_of_tendsto_mul_deriv_sub_div hab hrv hderiv hode)

/-- **The single-error form on a tail**: if `f' = (a f + (A + ε) h) / x` on `[r₀, ∞)` with
`ε → 0`, `f` differentiable there and `h` regularly varying of index `b > a`, then
`f / h → A / (b - a)`. -/
theorem tendsto_div_of_signed_ode {f f' h ε : ℝ → ℝ} {a b A r₀ : ℝ} (hab : a < b)
    (hrv : RegularlyVarying b h) (hderiv : ∀ x, r₀ ≤ x → HasDerivAt f (f' x) x)
    (hε0 : Tendsto ε atTop (𝓝 0))
    (hode : ∀ x, r₀ ≤ x → f' x = (a * f x + (A + ε x) * h x) / x) :
    Tendsto (fun r => f r / h r) atTop (𝓝 (A / (b - a))) :=
  tendsto_div_of_two_error_ode (ε₁ := fun _ => 0) hab hrv
    ((eventually_ge_atTop r₀).mono hderiv) tendsto_const_nhds hε0
    ((eventually_ge_atTop r₀).mono fun x hx => by simp only [hode x hx, add_zero])

/-! ### The hypotheses of the main theorem are satisfiable -/

/-- A witness for the hypotheses of `tendsto_div_of_ae_mul_deriv_eq` with a negative `a` and a
non-trivial homogeneous part: `a = -1`, `b = 0`, `A = 1`, `h = 1`, `ε = δ = 0`, `r₀ = 1` and
`f r = 1 + r⁻¹`. -/
example : ∃ (f h ε δ : ℝ → ℝ) (a b A r₀ : ℝ), a < b ∧ RegularlyVarying b h ∧
    Measurable ((Ici r₀).domRestrict ε) ∧ Tendsto ε atTop (𝓝 0) ∧
    Measurable ((Ici r₀).domRestrict δ) ∧ Tendsto δ atTop (𝓝 0) ∧
    (∀ R, r₀ ≤ R → AbsolutelyContinuousOnInterval f r₀ R) ∧
    (∀ᵐ r, r₀ ≤ r → r * deriv f r = (a + ε r) * f r + (A + δ r) * h r) := by
  refine ⟨fun r => 1 + r⁻¹, fun _ => 1, fun _ => 0, fun _ => 0, -1, 0, 1, 1, by norm_num,
    slowlyVarying_iff_regularlyVarying_zero.1 (slowlyVarying_const one_pos), measurable_const,
    tendsto_const_nhds, measurable_const, tendsto_const_nhds, fun R hR => ?_,
    ae_of_all _ fun r hr => ?_⟩
  · refine ContDiffOn.absolutelyContinuousOnInterval fun x hx => ?_
    rw [uIcc_of_le hR] at hx
    have hx0 : x ≠ 0 := by linarith [hx.1]
    exact (contDiffAt_const.add (contDiffAt_inv ℝ hx0)).contDiffWithinAt
  · have hr0 : r ≠ 0 := by linarith
    have hd : HasDerivAt (fun r : ℝ => 1 + r⁻¹) (-(r ^ 2)⁻¹) r :=
      (hasDerivAt_inv hr0).const_add 1
    rw [hd.deriv]
    field_simp
    ring

end PercLib.Analysis
