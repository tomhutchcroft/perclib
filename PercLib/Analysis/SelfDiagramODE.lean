/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-22, against pinned mathlib. No upstream proof is copied.
-/
module

public import PercLib.Analysis.LogarithmicCorrections
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Corrected quadratic inequality with a diagram bounded by the solution

Let `y ≥ 1` be locally absolutely continuous on `(a, b)`, `b < ∞`, with `y(t) → ∞` as `t ↑ b`,
and let `D ≥ 1`. Suppose that a.e. near `b`, `y' ≥ k (y - D)₊² / D²` with `k > 0`.

* If `D ≤ C log(e y)` near `b`, then eventually `y(b - ε) ≤ C₁ ε⁻¹ log²(1/ε)` and
  `D(b - ε) ≤ C₂ log(1/ε)`.
* If `D ≤ C y^q` near `b` with `q < 1/2` (the source has `0 ≤ q`), then eventually
  `y(b - ε) ≤ C₃ ε^{-1/(1-2q)}`.

The left endpoint `a` is real; since the statements only concern a neighbourhood of `b`, an
infinite left endpoint reduces to a finite one.

The common step (`mul_sub_le_comp_of_deriv_comp_le`): if `Φ` is Lipschitz on `[1, ∞)`,
differentiable there, `Φ(u) → 0` as `u → ∞`, and `(Φ ∘ y)' ≤ -c` a.e. on `(t₀, b)`, then
`Φ(y(t)) ≥ c (b - t)`. It is applied with `Φ(u) = u^{-(1-2q)}` and with
`Φ(u) = (L² + 2L + 2)/u`, `L = 1 + log u`, whose derivative is `-L²/u²`.

## Main results

* `mul_sub_le_comp_of_deriv_comp_le`
* `eventually_le_inv_mul_log_sq_of_deriv_ge_of_le_log`
* `eventually_le_log_of_deriv_ge_of_le_log`
* `eventually_le_rpow_of_deriv_ge_of_le_rpow`
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Real intervalIntegral
open scoped Topology NNReal

namespace PercLib.Analysis

/-- **Integrating `(Φ ∘ y)' ≤ -c` up to a blow-up point.** Let `y ≥ 1` be absolutely continuous
on every compact subinterval of `(t₀, b)` with `y(t) → ∞` as `t ↑ b`, and let `Φ` be
differentiable and Lipschitz on `[1, ∞)` with `Φ(u) → 0` as `u → ∞`. If
`Φ'(y(t)) y'(t) ≤ -c` for a.e. `t ∈ (t₀, b)`, then `c (b - t) ≤ Φ(y(t))` on `(t₀, b)`. -/
theorem mul_sub_le_comp_of_deriv_comp_le {y Φ Φ' : ℝ → ℝ} {t₀ b c : ℝ} {K : ℝ≥0}
    (hy1 : ∀ t ∈ Ioo t₀ b, 1 ≤ y t)
    (hac : ∀ p q, t₀ < p → p ≤ q → q < b → AbsolutelyContinuousOnInterval y p q)
    (htend : Tendsto y (𝓝[<] b) atTop)
    (hΦ : ∀ u, 1 ≤ u → HasDerivAt Φ (Φ' u) u) (hlip : LipschitzOnWith K Φ (Ici 1))
    (hΦ0 : Tendsto Φ atTop (𝓝 0))
    (hder : ∀ᵐ t, t ∈ Ioo t₀ b → Φ' (y t) * deriv y t ≤ -c) :
    ∀ t ∈ Ioo t₀ b, c * (b - t) ≤ Φ (y t) := by
  intro t ht
  have key : ∀ s ∈ Ioo t b, Φ (y s) + c * (s - t) ≤ Φ (y t) := by
    intro s hs
    have hts : t ≤ s := hs.1.le
    have hsub : ∀ x ∈ Icc t s, x ∈ Ioo t₀ b := fun x hx =>
      ⟨ht.1.trans_le hx.1, hx.2.trans_lt hs.2⟩
    have hacy := hac t s ht.1 hts hs.2
    have hU : AbsolutelyContinuousOnInterval (Φ ∘ y) t s :=
      hlip.comp_absolutelyContinuousOnInterval (fun x hx => by
        rw [uIcc_of_le hts] at hx
        exact hy1 x (hsub x hx)) hacy
    have hderU : ∀ᵐ x, x ∈ Icc t s → deriv (Φ ∘ y) x ≤ -c := by
      filter_upwards [hacy.ae_differentiableAt, hder] with x hd hx hxI
      have hd' := (hd (by rwa [uIcc_of_le hts])).hasDerivAt
      rw [((hΦ (y x) (hy1 x (hsub x hxI))).comp x hd').deriv]
      exact hx (hsub x hxI)
    have := sub_le_integral_of_ae_deriv_le hts hU intervalIntegrable_const hderU
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    simp only [Function.comp] at this
    linarith
  have h2 : Tendsto (fun s : ℝ => c * (s - t)) (𝓝[<] b) (𝓝 (c * (b - t))) :=
    ((continuous_const.mul (continuous_id.sub continuous_const)).tendsto b).mono_left
      nhdsWithin_le_nhds
  have hlim := (hΦ0.comp htend).add h2
  rw [zero_add] at hlim
  exact le_of_tendsto hlim (by
    filter_upwards [Ioo_mem_nhdsLT ht.2] with s hs using key s hs)

/-- If `0 < D ≤ y/2`, then `k (y - D)₊²/D² ≥ (k/4) y²/D²` for `k ≥ 0`. -/
theorem div_four_mul_sq_div_le_mul_max_sub_sq {k y D : ℝ} (hk : 0 ≤ k) (hD : 0 < D)
    (hDy : D ≤ y / 2) : k / 4 * y ^ 2 / D ^ 2 ≤ k * max (y - D) 0 ^ 2 / D ^ 2 := by
  have h0 : 0 ≤ y - D := by linarith
  rw [max_eq_left h0]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  have : y ^ 2 / 4 ≤ (y - D) ^ 2 := by nlinarith
  nlinarith

/-- `1 + log u ≤ 4 u^{1/4}` for `u > 0`, written with `√√u`. -/
theorem one_add_log_le_four_mul_sqrt_sqrt {u : ℝ} (hu : 0 < u) :
    1 + Real.log u ≤ 4 * √(√u) := by
  have hx : 0 < √(√u) := Real.sqrt_pos.2 (Real.sqrt_pos.2 hu)
  have e : √(√u) ^ 4 = u := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt (Real.sqrt_nonneg _),
      Real.sq_sqrt hu.le]
  have hlog : Real.log u = 4 * Real.log (√(√u)) := by
    conv_lhs => rw [← e]
    rw [Real.log_pow]
    norm_num
  have := Real.log_le_sub_one_of_pos hx
  linarith

/-- `1 + log u ≤ u` for `u > 0`. -/
theorem one_add_log_le_self {u : ℝ} (hu : 0 < u) : 1 + Real.log u ≤ u := by
  linarith [Real.log_le_sub_one_of_pos hu]

/-- The function `F(u) = (L² + 2L + 2)/u`, `L = 1 + log u`, has derivative `-L²/u²` at
`u > 0`. -/
theorem hasDerivAt_logSquareTail {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun v => ((1 + Real.log v) ^ 2 + 2 * (1 + Real.log v) + 2) / v)
      (-(1 + Real.log u) ^ 2 / u ^ 2) u := by
  have hL : HasDerivAt (fun v => 1 + Real.log v) (u⁻¹) u := by
    simpa using (Real.hasDerivAt_log hu.ne').const_add 1
  have hN := ((hL.pow 2).add (hL.const_mul 2)).add_const 2
  refine (hN.div (hasDerivAt_id u) hu.ne').congr_deriv ?_
  norm_num [id]
  field_simp
  ring

/-- `((1 + log u)² + 2(1 + log u) + 2)/u ≤ 80/√u` for `u ≥ 1`. -/
theorem logSquareTail_le_div_sqrt {u : ℝ} (hu : 1 ≤ u) :
    ((1 + Real.log u) ^ 2 + 2 * (1 + Real.log u) + 2) / u ≤ 80 / √u := by
  have hu0 : 0 < u := by linarith
  have hL1 : 1 ≤ 1 + Real.log u := by linarith [Real.log_nonneg hu]
  have h4 := one_add_log_le_four_mul_sqrt_sqrt hu0
  have hss : √(√u) ^ 2 = √u := Real.sq_sqrt (Real.sqrt_nonneg _)
  have hsu : √u * √u = u := Real.mul_self_sqrt hu0.le
  have hsu0 : 0 < √u := Real.sqrt_pos.2 hu0
  have hL2 : (1 + Real.log u) ^ 2 ≤ 16 * √u := by
    have := pow_le_pow_left₀ (by linarith) h4 2
    nlinarith
  have h80 : (1 + Real.log u) ^ 2 + 2 * (1 + Real.log u) + 2 ≤ 80 * √u := by nlinarith
  rw [div_le_div_iff₀ hu0 hsu0]
  nlinarith [mul_le_mul_of_nonneg_right h80 hsu0.le]

/-- Logarithmic case, common estimate: under the hypotheses of
`eventually_le_inv_mul_log_sq_of_deriv_ge_of_le_log`, there are `c > 0`, `C' > 0` and
`t₁ < b` such that on `(t₁, b)`, `D ≤ C' (1 + log y)`, `1 ≤ y`, and
`c (b - t) ≤ ((1 + log y)² + 2(1 + log y) + 2)/y`. -/
theorem exists_log_tail_bound_of_deriv_ge_of_le_log {a b k C : ℝ} {y D : ℝ → ℝ}
    (hab : a < b) (hy1 : ∀ t ∈ Ioo a b, 1 ≤ y t)
    (hac : ∀ p q, a < p → p ≤ q → q < b → AbsolutelyContinuousOnInterval y p q)
    (htend : Tendsto y (𝓝[<] b) atTop) (hD1 : ∀ t ∈ Ioo a b, 1 ≤ D t) (hk : 0 < k)
    (hder : ∃ t₀ < b, ∀ᵐ t, t ∈ Ioo t₀ b → k * max (y t - D t) 0 ^ 2 / D t ^ 2 ≤ deriv y t)
    (hDlog : ∀ᶠ t in 𝓝[<] b, D t ≤ C * Real.log (Real.exp 1 * y t)) :
    ∃ c > 0, ∃ C' > 0, ∃ t₁ < b, ∀ t ∈ Ioo t₁ b, 1 ≤ y t ∧ 1 ≤ D t ∧
      D t ≤ C' * (1 + Real.log (y t)) ∧
      c * (b - t) ≤ ((1 + Real.log (y t)) ^ 2 + 2 * (1 + Real.log (y t)) + 2) / y t := by
  obtain ⟨t₀, ht₀, hder⟩ := hder
  set Cp := max C 1 with hCp
  have hCp0 : 0 < Cp := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hev : ∀ᶠ t in 𝓝[<] b, (t ∈ Ioo a b ∧ t₀ < t) ∧
      D t ≤ C * Real.log (Real.exp 1 * y t) ∧ 16 * Cp ^ 2 ≤ y t :=
    by filter_upwards [Ioo_mem_nhdsLT hab, Ioo_mem_nhdsLT ht₀, hDlog,
      tendsto_atTop.1 htend (16 * Cp ^ 2)] with t h1 h2 h3 h4 using ⟨⟨h1, h2.1⟩, h3, h4⟩
  obtain ⟨t₁, ht₁, H⟩ := (nhdsLT_basis b).eventually_iff.1 hev
  -- pointwise consequences on `(t₁, b)`
  have hpt : ∀ t ∈ Ioo t₁ b, 1 ≤ y t ∧ 1 ≤ D t ∧ D t ≤ Cp * (1 + Real.log (y t)) ∧
      1 ≤ 1 + Real.log (y t) ∧ D t ≤ y t / 2 := by
    intro t ht
    obtain ⟨⟨htI, -⟩, hDt, hyt⟩ := H ht
    have hy := hy1 t htI
    have hy0 : 0 < y t := by linarith
    have hL1 : 1 ≤ 1 + Real.log (y t) := by linarith [Real.log_nonneg hy]
    have hlogeq : Real.log (Real.exp 1 * y t) = 1 + Real.log (y t) := by
      rw [Real.log_mul (Real.exp_pos 1).ne' hy0.ne', Real.log_exp]
    rw [hlogeq] at hDt
    have hDC : D t ≤ Cp * (1 + Real.log (y t)) :=
      hDt.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith))
    refine ⟨hy, hD1 t htI, hDC, hL1, hDC.trans ?_⟩
    -- `Cp (1 + log y) ≤ 4 Cp √√y ≤ y/2`
    have h4 := one_add_log_le_four_mul_sqrt_sqrt hy0
    have hs : √(√(y t)) ^ 4 = y t := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt (Real.sqrt_nonneg _),
        Real.sq_sqrt hy0.le]
    have hsq : 4 * Cp ≤ √(√(y t)) ^ 2 := by
      rw [Real.sq_sqrt (Real.sqrt_nonneg _)]
      rw [show 4 * Cp = √((4 * Cp) ^ 2) by rw [Real.sqrt_sq (by positivity)]]
      exact Real.sqrt_le_sqrt (by nlinarith)
    have hx0 : 0 ≤ √(√(y t)) := Real.sqrt_nonneg _
    have hCp1 : 1 ≤ Cp := le_max_right _ _
    have hx2 : 2 ≤ √(√(y t)) := by nlinarith
    have h3 : 8 * Cp ≤ √(√(y t)) ^ 3 := by
      have := mul_le_mul hx2 hsq (by positivity) hx0
      nlinarith
    have h8 : 8 * Cp * √(√(y t)) ≤ √(√(y t)) ^ 4 := by
      have := mul_le_mul_of_nonneg_right h3 hx0
      nlinarith
    have h5 := mul_le_mul_of_nonneg_left h4 hCp0.le
    nlinarith
  set c := k / (4 * Cp ^ 2) with hc
  have hc0 : 0 < c := by positivity
  refine ⟨c, hc0, Cp, hCp0, t₁, ht₁, fun t ht => ⟨(hpt t ht).1, (hpt t ht).2.1,
    (hpt t ht).2.2.1, ?_⟩⟩
  -- the tail function
  set F : ℝ → ℝ := fun v => ((1 + Real.log v) ^ 2 + 2 * (1 + Real.log v) + 2) / v with hF
  set F' : ℝ → ℝ := fun v => -(1 + Real.log v) ^ 2 / v ^ 2 with hF'
  have hFd : ∀ u, 1 ≤ u → HasDerivAt F (F' u) u := fun u hu =>
    hasDerivAt_logSquareTail (by linarith)
  have hFbound : ∀ u, 1 ≤ u → |F' u| ≤ 1 := by
    intro u hu
    have hu0 : 0 < u := by linarith
    have hL0 : 0 ≤ 1 + Real.log u := by linarith [Real.log_nonneg hu]
    have hLu := one_add_log_le_self hu0
    simp only [hF', neg_div, abs_neg]
    rw [abs_of_nonneg (by positivity), div_le_one (by positivity)]
    exact pow_le_pow_left₀ hL0 hLu 2
  have hlip : LipschitzOnWith 1 F (Ici 1) := by
    refine (convex_Ici (1 : ℝ)).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun u hu => (hFd u hu).hasDerivWithinAt) fun u hu => ?_
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs, NNReal.coe_one]
    exact hFbound u hu
  have hF0 : Tendsto F atTop (𝓝 0) := by
    -- `0 ≤ F u ≤ 80/√u`
    have hup : Tendsto (fun u : ℝ => 80 / √u) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop Real.tendsto_sqrt_atTop
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with u hu
      have hL0 : 0 ≤ 1 + Real.log u := by linarith [Real.log_nonneg hu]
      simp only [hF]
      exact div_nonneg (by positivity) (by linarith)
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with u hu
      exact logSquareTail_le_div_sqrt hu
  have hderF : ∀ᵐ s, s ∈ Ioo t₁ b → F' (y s) * deriv y s ≤ -c := by
    filter_upwards [hder] with s hs hsI
    obtain ⟨hy, hDs1, hDC, hL1, hDy⟩ := hpt s hsI
    have hy0 : 0 < y s := by linarith
    have hds := hs ⟨(H hsI).1.2, hsI.2⟩
    have hlow := (div_four_mul_sq_div_le_mul_max_sub_sq hk.le (by linarith) hDy).trans hds
    -- `(k/4) y²/D² ≥ c y²/L²`
    set L := 1 + Real.log (y s)
    have hlow2 : c * y s ^ 2 / L ^ 2 ≤ deriv y s := by
      refine le_trans ?_ hlow
      rw [hc, div_mul_eq_mul_div, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
      have hD2 : D s ^ 2 ≤ Cp ^ 2 * L ^ 2 := by
        rw [← mul_pow]; exact pow_le_pow_left₀ (by linarith) hDC 2
      have : 0 ≤ k * y s ^ 2 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hD2 this]
    simp only [hF']
    have hF'nonpos : -L ^ 2 / y s ^ 2 ≤ 0 := div_nonpos_of_nonpos_of_nonneg
      (by nlinarith) (by positivity)
    calc -L ^ 2 / y s ^ 2 * deriv y s ≤ -L ^ 2 / y s ^ 2 * (c * y s ^ 2 / L ^ 2) :=
          mul_le_mul_of_nonpos_left hlow2 hF'nonpos
      _ = -c := by field_simp
  exact mul_sub_le_comp_of_deriv_comp_le (fun s hs => (hpt s hs).1)
    (fun p q hp hpq hq => hac p q ((H ⟨hp, hpq.trans_lt hq⟩).1.1.1) hpq hq) htend hFd hlip hF0
    hderF t ht

/-- Logarithmic case: eventual bounds `y(b - ε) ≤ C₁ ε⁻¹ log²(1/ε)` and
`D(b - ε) ≤ C₂ log(1/ε)` together. -/
theorem exists_eventually_le_of_deriv_ge_of_le_log {a b k C : ℝ} {y D : ℝ → ℝ}
    (hab : a < b) (hy1 : ∀ t ∈ Ioo a b, 1 ≤ y t)
    (hac : ∀ p q, a < p → p ≤ q → q < b → AbsolutelyContinuousOnInterval y p q)
    (htend : Tendsto y (𝓝[<] b) atTop) (hD1 : ∀ t ∈ Ioo a b, 1 ≤ D t) (hk : 0 < k)
    (hder : ∃ t₀ < b, ∀ᵐ t, t ∈ Ioo t₀ b → k * max (y t - D t) 0 ^ 2 / D t ^ 2 ≤ deriv y t)
    (hDlog : ∀ᶠ t in 𝓝[<] b, D t ≤ C * Real.log (Real.exp 1 * y t)) :
    ∃ C₁ C₂, ∀ᶠ ε in 𝓝[>] 0, y (b - ε) ≤ C₁ * (ε⁻¹ * Real.log (1 / ε) ^ 2) ∧
      D (b - ε) ≤ C₂ * Real.log (1 / ε) := by
  obtain ⟨c, hc, Cp, hCp, t₁, ht₁, H⟩ :=
    exists_log_tail_bound_of_deriv_ge_of_le_log hab hy1 hac htend hD1 hk hder hDlog
  set A := 1 + 2 * Real.log (80 / c) with hA
  refine ⟨45 / c, 3 * Cp, ?_⟩
  have hpos : (0 : ℝ) < min (b - t₁) (Real.exp (-|A|)) :=
    lt_min (by linarith) (Real.exp_pos _)
  filter_upwards [Ioo_mem_nhdsGT hpos] with ε hε
  obtain ⟨hε0, hε1⟩ := hε
  have hεt : ε < b - t₁ := hε1.trans_le (min_le_left _ _)
  have hεA : ε < Real.exp (-|A|) := hε1.trans_le (min_le_right _ _)
  obtain ⟨hy, -, hDC, hF⟩ := H (b - ε) ⟨by linarith, by linarith⟩
  rw [sub_sub_cancel] at hF
  set Y := y (b - ε)
  set L := 1 + Real.log Y with hL
  have hY0 : 0 < Y := by linarith
  have hL1 : 1 ≤ L := by linarith [Real.log_nonneg hy]
  have hl : |A| ≤ Real.log (1 / ε) := by
    rw [one_div, Real.log_inv, le_neg, ← Real.log_exp (-|A|)]
    exact Real.log_le_log hε0 hεA.le
  -- `√Y ≤ 80/(cε)`
  have hsY : √Y ≤ 80 / (c * ε) := by
    have h1 := hF.trans (logSquareTail_le_div_sqrt hy)
    have hs0 : 0 < √Y := Real.sqrt_pos.2 hY0
    rw [le_div_iff₀ hs0] at h1
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hlogY : Real.log Y ≤ 2 * Real.log (80 / c) + 2 * Real.log (1 / ε) := by
    have hs0 : 0 < √Y := Real.sqrt_pos.2 hY0
    have e : Real.log Y = 2 * Real.log √Y := by
      rw [Real.log_sqrt hY0.le]; ring
    have e2 : Real.log (80 / (c * ε)) = Real.log (80 / c) + Real.log (1 / ε) := by
      rw [← Real.log_mul (by positivity) (by positivity)]
      congr 1
      field_simp
    have := Real.log_le_log hs0 hsY
    rw [e2] at this
    linarith
  have hL3 : L ≤ 3 * Real.log (1 / ε) := by
    have := le_abs_self A
    linarith
  refine ⟨?_, hDC.trans (by nlinarith)⟩
  -- `Y ≤ 5L²/(cε) ≤ 45 log²(1/ε)/(cε)`
  have hF5 : (L ^ 2 + 2 * L + 2) / Y ≤ 5 * L ^ 2 / Y :=
    div_le_div_of_nonneg_right (by nlinarith) hY0.le
  have h2 := hF.trans hF5
  rw [le_div_iff₀ hY0] at h2
  have hl0 : 0 ≤ Real.log (1 / ε) := (abs_nonneg A).trans hl
  have hL9 : L ^ 2 ≤ 9 * Real.log (1 / ε) ^ 2 := by nlinarith
  rw [show 45 / c * (ε⁻¹ * Real.log (1 / ε) ^ 2) = 45 * Real.log (1 / ε) ^ 2 / (c * ε) by
    field_simp, le_div_iff₀ (by positivity)]
  nlinarith

/-- **Logarithmic diagram bound, susceptibility.** Let `y ≥ 1` be locally absolutely continuous
on `(a, b)` with `y(t) → ∞` as `t ↑ b`, `D ≥ 1`, and `y' ≥ k (y - D)₊²/D²` a.e. near `b`, with
`k > 0`. If `D(t) ≤ C log(e y(t))` near `b`, then `y(b - ε) ≤ C₁ ε⁻¹ log²(1/ε)` for all small
`ε > 0`. -/
theorem eventually_le_inv_mul_log_sq_of_deriv_ge_of_le_log {a b k C : ℝ} {y D : ℝ → ℝ}
    (hab : a < b) (hy1 : ∀ t ∈ Ioo a b, 1 ≤ y t)
    (hac : ∀ p q, a < p → p ≤ q → q < b → AbsolutelyContinuousOnInterval y p q)
    (htend : Tendsto y (𝓝[<] b) atTop) (hD1 : ∀ t ∈ Ioo a b, 1 ≤ D t) (hk : 0 < k)
    (hder : ∃ t₀ < b, ∀ᵐ t, t ∈ Ioo t₀ b → k * max (y t - D t) 0 ^ 2 / D t ^ 2 ≤ deriv y t)
    (hDlog : ∀ᶠ t in 𝓝[<] b, D t ≤ C * Real.log (Real.exp 1 * y t)) :
    ∃ C₁, ∀ᶠ ε in 𝓝[>] 0, y (b - ε) ≤ C₁ * (ε⁻¹ * Real.log (1 / ε) ^ 2) := by
  obtain ⟨C₁, _, h⟩ :=
    exists_eventually_le_of_deriv_ge_of_le_log hab hy1 hac htend hD1 hk hder hDlog
  exact ⟨C₁, Filter.Eventually.mono h fun _ hh => hh.1⟩

/-- **Logarithmic diagram bound, diagram.** Under the hypotheses of
`eventually_le_inv_mul_log_sq_of_deriv_ge_of_le_log`, `D(b - ε) ≤ C₂ log(1/ε)` for all small
`ε > 0`. -/
theorem eventually_le_log_of_deriv_ge_of_le_log {a b k C : ℝ} {y D : ℝ → ℝ}
    (hab : a < b) (hy1 : ∀ t ∈ Ioo a b, 1 ≤ y t)
    (hac : ∀ p q, a < p → p ≤ q → q < b → AbsolutelyContinuousOnInterval y p q)
    (htend : Tendsto y (𝓝[<] b) atTop) (hD1 : ∀ t ∈ Ioo a b, 1 ≤ D t) (hk : 0 < k)
    (hder : ∃ t₀ < b, ∀ᵐ t, t ∈ Ioo t₀ b → k * max (y t - D t) 0 ^ 2 / D t ^ 2 ≤ deriv y t)
    (hDlog : ∀ᶠ t in 𝓝[<] b, D t ≤ C * Real.log (Real.exp 1 * y t)) :
    ∃ C₂, ∀ᶠ ε in 𝓝[>] 0, D (b - ε) ≤ C₂ * Real.log (1 / ε) := by
  obtain ⟨_, C₂, h⟩ :=
    exists_eventually_le_of_deriv_ge_of_le_log hab hy1 hac htend hD1 hk hder hDlog
  exact ⟨C₂, Filter.Eventually.mono h fun _ hh => hh.2⟩

/-- **Power diagram bound.** Let `y ≥ 1` be locally absolutely continuous on `(a, b)` with
`y(t) → ∞` as `t ↑ b`, `D ≥ 1`, and `y' ≥ k (y - D)₊²/D²` a.e. near `b`, with `k > 0`. If
`D(t) ≤ C y(t)^q` near `b`, with `q < 1/2`, then `y(b - ε) ≤ C₃ ε^{-1/(1-2q)}` for all small
`ε > 0`. -/
theorem eventually_le_rpow_of_deriv_ge_of_le_rpow {a b k C q : ℝ} {y D : ℝ → ℝ}
    (hab : a < b) (hy1 : ∀ t ∈ Ioo a b, 1 ≤ y t)
    (hac : ∀ p r, a < p → p ≤ r → r < b → AbsolutelyContinuousOnInterval y p r)
    (htend : Tendsto y (𝓝[<] b) atTop) (hD1 : ∀ t ∈ Ioo a b, 1 ≤ D t) (hk : 0 < k)
    (hder : ∃ t₀ < b, ∀ᵐ t, t ∈ Ioo t₀ b → k * max (y t - D t) 0 ^ 2 / D t ^ 2 ≤ deriv y t)
    (hq : q < 1 / 2) (hDq : ∀ᶠ t in 𝓝[<] b, D t ≤ C * y t ^ q) :
    ∃ C₃, ∀ᶠ ε in 𝓝[>] 0, y (b - ε) ≤ C₃ * ε ^ (-(1 / (1 - 2 * q))) := by
  obtain ⟨t₀, ht₀, hder⟩ := hder
  set r := 1 - 2 * q with hr
  have hr0 : 0 < r := by linarith
  set Cp := max C 1 with hCp
  have hCp0 : 0 < Cp := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hev : ∀ᶠ t in 𝓝[<] b, (t ∈ Ioo a b ∧ t₀ < t) ∧ D t ≤ C * y t ^ q ∧
      2 * Cp ≤ y t ^ (1 - q) := by
    filter_upwards [Ioo_mem_nhdsLT hab, Ioo_mem_nhdsLT ht₀, hDq,
      (tendsto_atTop.1 ((tendsto_rpow_atTop (by linarith : (0 : ℝ) < 1 - q)).comp htend))
        (2 * Cp)] with t h1 h2 h3 h4 using ⟨⟨h1, h2.1⟩, h3, h4⟩
  obtain ⟨t₁, ht₁, H⟩ := (nhdsLT_basis b).eventually_iff.1 hev
  have hpt : ∀ t ∈ Ioo t₁ b, 1 ≤ y t ∧ 1 ≤ D t ∧ D t ≤ Cp * y t ^ q ∧ D t ≤ y t / 2 := by
    intro t ht
    obtain ⟨⟨htI, -⟩, hDt, hyt⟩ := H ht
    have hy := hy1 t htI
    have hy0 : 0 < y t := by linarith
    have hDC : D t ≤ Cp * y t ^ q :=
      hDt.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hy0.le _))
    refine ⟨hy, hD1 t htI, hDC, hDC.trans ?_⟩
    have e : y t = y t ^ q * y t ^ (1 - q) := by
      rw [← Real.rpow_add hy0]; simp
    have hq' : 0 ≤ y t ^ q := Real.rpow_nonneg hy0.le _
    nlinarith [mul_le_mul_of_nonneg_left hyt hq']
  set c := r * (k / (4 * Cp ^ 2)) with hc
  have hc0 : 0 < c := by positivity
  set Φ' : ℝ → ℝ := fun u => -r * u ^ (-r - 1) with hΦ'
  have hΦd : ∀ u, 1 ≤ u → HasDerivAt (fun u : ℝ => u ^ (-r)) (Φ' u) u := fun u hu =>
    Real.hasDerivAt_rpow_const (Or.inl (by linarith))
  have hlip : LipschitzOnWith (Real.toNNReal r) (fun u : ℝ => u ^ (-r)) (Ici 1) := by
    refine (convex_Ici (1 : ℝ)).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun u hu => (hΦd u hu).hasDerivWithinAt) fun u hu => ?_
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs, Real.coe_toNNReal _ hr0.le]
    have hu1 : 1 ≤ u := hu
    have h1 : u ^ (-r - 1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hu1 (by linarith)
    have h0 : 0 ≤ u ^ (-r - 1) := Real.rpow_nonneg (by linarith) _
    simp only [hΦ', neg_mul, abs_neg]
    rw [abs_of_nonneg (by positivity)]
    nlinarith
  have hderΦ : ∀ᵐ s, s ∈ Ioo t₁ b → Φ' (y s) * deriv y s ≤ -c := by
    filter_upwards [hder] with s hs hsI
    obtain ⟨hy, hDs1, hDC, hDy⟩ := hpt s hsI
    have hy0 : 0 < y s := by linarith
    have hds := hs ⟨(H hsI).1.2, hsI.2⟩
    have hlow := (div_four_mul_sq_div_le_mul_max_sub_sq hk.le (by linarith) hDy).trans hds
    set P := y s ^ q
    have hP : 0 < P := Real.rpow_pos_of_pos hy0 _
    have hlow2 : k / (4 * Cp ^ 2) * y s ^ 2 / P ^ 2 ≤ deriv y s := by
      refine le_trans ?_ hlow
      rw [div_mul_eq_mul_div, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
      have hD2 : D s ^ 2 ≤ Cp ^ 2 * P ^ 2 := by
        rw [← mul_pow]; exact pow_le_pow_left₀ (by linarith) hDC 2
      have : 0 ≤ k * y s ^ 2 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hD2 this]
    have hneg : Φ' (y s) ≤ 0 := by
      simp only [hΦ', neg_mul]
      exact neg_nonpos.2 (mul_nonneg hr0.le (Real.rpow_nonneg hy0.le _))
    have e : y s ^ (-r - 1) * y s ^ 2 = P ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_add hy0, ← Real.rpow_mul hy0.le]
      congr 1
      rw [hr]
      push_cast
      ring
    calc Φ' (y s) * deriv y s ≤ Φ' (y s) * (k / (4 * Cp ^ 2) * y s ^ 2 / P ^ 2) :=
          mul_le_mul_of_nonpos_left hlow2 hneg
      _ = -c * ((y s ^ (-r - 1) * y s ^ 2) / P ^ 2) := by
          simp only [hΦ', hc]
          ring
      _ = -c := by rw [e, div_self (by positivity), mul_one]
  have hmain := mul_sub_le_comp_of_deriv_comp_le (fun s hs => (hpt s hs).1)
    (fun p q hp hpq hq => hac p q ((H ⟨hp, hpq.trans_lt hq⟩).1.1.1) hpq hq) htend hΦd hlip
    (tendsto_rpow_neg_atTop hr0) hderΦ
  refine ⟨c ^ (-(1 / r)), ?_⟩
  have hpos : (0 : ℝ) < b - t₁ := by linarith
  filter_upwards [Ioo_mem_nhdsGT hpos] with ε hε
  obtain ⟨hε0, hεt⟩ := hε
  have h := hmain (b - ε) ⟨by linarith, by linarith⟩
  rw [sub_sub_cancel] at h
  have hy0 : 0 < y (b - ε) := by linarith [(hpt (b - ε) ⟨by linarith, by linarith⟩).1]
  have h2 := Real.rpow_le_rpow_of_nonpos (by positivity) h
    (by have : 0 < 1 / r := by positivity
        linarith : -(1 / r) ≤ 0)
  rwa [← Real.rpow_mul hy0.le, show -r * -(1 / r) = 1 by field_simp, Real.rpow_one,
    Real.mul_rpow hc0.le hε0.le] at h2

end PercLib.Analysis
