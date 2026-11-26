/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-16, against pinned mathlib. No upstream proof is copied.
-/
module

public import PercLib.Analysis.Elementary
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import PercLib.Meta.Tag

/-!
# Logarithmic corrections from a quadratic differential inequality (6PGV)

Absolute continuity is mathlib's `AbsolutelyContinuousOnInterval`; "locally absolutely
continuous on `(β₀, β_c)`" means absolutely continuous on every `[p, q] ⊂ (β₀, β_c)` with
`p ≤ q`.
Derivatives are `deriv` almost everywhere.

**6PGV** (`le_of_deriv_ge_sq_div`). Let `0 ≤ β₀ < β_c`, `χ > 0` nondecreasing and locally
absolutely continuous on `(β₀, β_c)`, `D ≥ 1` measurable, and
`χ' ≥ (χ - D)₊² / (3 β² D²)` a.e. Then for `β ∈ (β₀, β_c)`,
`χ(β) ≤ (1 + 2(β_c - β)/(3 β β_c)) · (∫_β^{β_c} ds/(3 s² D(s)²))⁻¹`.
No divergence at the endpoint is assumed.

**Logarithmic form** (`isBigO_of_deriv_ge_sq_div`). If moreover
`D(β_c - u) ≤ C (log(1/u))^a` for small `u > 0`, with `C > 0`, `a ≥ 0`, then
`χ(β_c - ε) = O(ε⁻¹ (log(1/ε))^{2a})` as `ε ↓ 0`.

Both are corollaries of the forms with a general linear term
`χ' ≥ (χ² - κχD)/(3β²D²)`, `κ ≥ 0` (`le_of_deriv_ge_sq_sub_mul_div`,
`isBigO_of_deriv_ge_sq_sub_mul_div`), with prefactor `1 + κ(β_c - β)/(3ββ_c)`. The case
`κ = 1`, i.e. `χ' ≥ χ(χ - D)/(3β²D²)`, is `le_of_deriv_ge_mul_sub_div`, with the explicit
eventual bounds `exists_le_inv_mul_log_rpow_of_deriv_ge_mul_sub_div` and
`exists_le_inv_of_deriv_ge_mul_sub_div`.

The proof bounds `(1/χ)' ≤ -1/(3s²D²) + κ/(3s²χ(β))` on `[β, s₁]` and integrates. It uses
`(χ - D)₊² ≥ χ² - 2χD`, `D ≥ 1` and the monotonicity of `χ`.

**OP8F** (`op8f_asymptotics`). Suppose `m' = a m² (1 - e₁)`, `f' = 3 a m f (1 - e₂)` and
`e₂ - e₁ = (K + ε) f²/(b m³)` a.e., with `m ~ c r^α`, `a ~ a₀ r^{-α-1}`, `b ~ ν r^{3α}` and
`ε → 0`. Then `f/m³ ~ (6 K a₀ c⁴ log r/ν)^{-1/2}`. The function `h = m⁶/f²` satisfies
`h' = 6 a (K + ε) m⁴/b ~ L/r` with `L = 6 K a₀ c⁴/ν`, so `h(r)/log r → L`
(`tendsto_div_log_of_mul_deriv`).

No definition is introduced.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Real intervalIntegral Asymptotics
open scoped Topology

namespace PercLib.Analysis

/-- If `f` is absolutely continuous on `[a, b]` and `f' ≤ g` a.e. there, with `g` integrable,
then `f b - f a ≤ ∫_a^b g`. -/
theorem sub_le_integral_of_ae_deriv_le {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : AbsolutelyContinuousOnInterval f a b) (hg : IntervalIntegrable g volume a b)
    (h : ∀ᵐ x, x ∈ Icc a b → deriv f x ≤ g x) :
    f b - f a ≤ ∫ x in a..b, g x := by
  rw [← hf.integral_deriv_eq_sub]
  exact integral_mono_ae_restrict hab hf.intervalIntegrable_deriv hg
    ((ae_restrict_iff' measurableSet_Icc).2 h)

/-- A measurable function bounded on `(p, q)` is interval integrable on `[p, q]`. -/
theorem intervalIntegrable_of_bound_Ioo {f : ℝ → ℝ} {p q M : ℝ} (hpq : p ≤ q)
    (hf : Measurable f) (hb : ∀ s ∈ Ioo p q, |f s| ≤ M) : IntervalIntegrable f volume p q := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hpq, integrableOn_Ioc_iff_integrableOn_Ioo]
  exact Measure.integrableOn_of_bounded (by simp) hf.aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall fun s hs => by
      simpa using hb s hs))

/-- The integrand `1/(3 s² D(s)²)` is measurable. -/
theorem measurable_inv_three_sq_mul_sq {D : ℝ → ℝ} (hD : Measurable D) :
    Measurable fun s => 1 / (3 * s ^ 2 * D s ^ 2) :=
  measurable_const.div ((measurable_const.mul (measurable_id.pow_const 2)).mul
    (hD.pow_const 2))

variable {β₀ βc : ℝ} {χ D : ℝ → ℝ}

/-- **Integrated susceptibility bound, general linear term.** Let `0 ≤ β₀ < β_c`, `κ ≥ 0`,
`χ > 0` nondecreasing and locally absolutely continuous on `(β₀, β_c)`, `D ≥ 1` measurable and
`χ' ≥ (χ² - κχD)/(3β²D²)` a.e. on `(β₀, β_c)`. Then
`χ(β) ≤ (1 + κ(β_c - β)/(3ββ_c)) (∫_β^{β_c} ds/(3s²D(s)²))⁻¹` for every `β ∈ (β₀, β_c)`. -/
theorem le_of_deriv_ge_sq_sub_mul_div {κ : ℝ} (hβ₀ : 0 ≤ β₀) (hκ : 0 ≤ κ)
    (hpos : ∀ β ∈ Ioo β₀ βc, 0 < χ β)
    (hmono : MonotoneOn χ (Ioo β₀ βc))
    (hac : ∀ p q, β₀ < p → p ≤ q → q < βc → AbsolutelyContinuousOnInterval χ p q)
    (hD : Measurable D) (hD1 : ∀ β ∈ Ioo β₀ βc, 1 ≤ D β)
    (hder : ∀ᵐ β, β ∈ Ioo β₀ βc →
      (χ β ^ 2 - κ * χ β * D β) / (3 * β ^ 2 * D β ^ 2) ≤ deriv χ β)
    {β : ℝ} (hβ : β ∈ Ioo β₀ βc) :
    χ β ≤ (1 + κ * (βc - β) / (3 * β * βc)) * (∫ s in β..βc, 1 / (3 * s ^ 2 * D s ^ 2))⁻¹ := by
  have hβ0 : 0 < β := lt_of_le_of_lt hβ₀ hβ.1
  have hβc0 : 0 < βc := hβ0.trans hβ.2
  have hχβ := hpos β hβ
  set I := ∫ s in β..βc, 1 / (3 * s ^ 2 * D s ^ 2) with hI
  set J := κ * (βc - β) / (3 * β * βc) with hJ
  have hJ0 : 0 ≤ J := by
    have := hβ.2
    rw [hJ]
    exact div_nonneg (mul_nonneg hκ (by linarith)) (by positivity)
  -- integrability of `1/(3s²D²)` on subintervals of `[β, β_c]`
  have hfint : ∀ p q, β ≤ p → p ≤ q → q ≤ βc →
      IntervalIntegrable (fun s => 1 / (3 * s ^ 2 * D s ^ 2)) volume p q := by
    intro p q hp hpq hq
    refine intervalIntegrable_of_bound_Ioo (M := 1 / (3 * β ^ 2)) hpq
      (measurable_inv_three_sq_mul_sq hD) fun s hs => ?_
    have hs0 : 0 < s := hβ0.trans_le (hp.trans hs.1.le)
    have hsI : s ∈ Ioo β₀ βc := ⟨hβ.1.trans_le (hp.trans hs.1.le), hs.2.trans_le hq⟩
    have hDs := hD1 s hsI
    rw [abs_of_nonneg (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
    have : β ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ hβ0.le (hp.trans hs.1.le) 2
    nlinarith [mul_le_mul this (one_le_pow₀ hDs (n := 2)) zero_le_one (by positivity)]
  -- the main estimate on `[β, s₁]`
  have hmain : ∀ s₁ ∈ Ioo β βc,
      ∫ s in β..s₁, 1 / (3 * s ^ 2 * D s ^ 2) ≤ (1 + J) / χ β := by
    intro s₁ hs₁
    have hs₁I : s₁ ∈ Ioo β₀ βc := ⟨hβ.1.trans hs₁.1, hs₁.2⟩
    have hsub : ∀ s ∈ Icc β s₁, s ∈ Ioo β₀ βc := fun s hs =>
      ⟨hβ.1.trans_le hs.1, hs.2.trans_lt hs₁.2⟩
    have hχge : ∀ s ∈ Icc β s₁, χ β ≤ χ s := fun s hs => hmono hβ (hsub s hs) hs.1
    have hacχ : AbsolutelyContinuousOnInterval χ β s₁ := hac β s₁ hβ.1 hs₁.1.le hs₁.2
    -- `1/χ` is absolutely continuous on `[β, s₁]`
    have hlip : LipschitzOnWith (Real.toNNReal (1 / χ β ^ 2)) (fun x : ℝ => x⁻¹) (Ici (χ β)) := by
      refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
      have hx0 : 0 < x := lt_of_lt_of_le hχβ hx
      have hy0 : 0 < y := lt_of_lt_of_le hχβ hy
      rw [Real.coe_toNNReal _ (by positivity), Real.dist_eq, Real.dist_eq,
        inv_sub_inv hx0.ne' hy0.ne', abs_div, abs_of_pos (mul_pos hx0 hy0), abs_sub_comm,
        div_le_iff₀ (mul_pos hx0 hy0)]
      have hxy : χ β ^ 2 ≤ x * y := by nlinarith [mem_Ici.1 hx, mem_Ici.1 hy]
      have e : 1 / χ β ^ 2 * |x - y| * (x * y) = |x - y| * ((x * y) / χ β ^ 2) := by ring
      rw [e]
      have : 1 ≤ (x * y) / χ β ^ 2 := by rw [le_div_iff₀ (by positivity)]; linarith
      nlinarith [abs_nonneg (x - y)]
    have hU : AbsolutelyContinuousOnInterval (fun s => (χ s)⁻¹) β s₁ :=
      hlip.comp_absolutelyContinuousOnInterval (fun s hs => by
        rw [uIcc_of_le hs₁.1.le] at hs
        exact hχge s hs) hacχ
    -- the derivative bound
    set g : ℝ → ℝ := fun s => -(1 / (3 * s ^ 2 * D s ^ 2)) + κ / (3 * χ β) * (1 / s ^ 2) with hg
    have hgint : IntervalIntegrable g volume β s₁ := by
      refine (hfint β s₁ le_rfl hs₁.1.le hs₁.2.le).neg.add ?_
      refine (ContinuousOn.intervalIntegrable ?_).const_mul _
      refine ContinuousOn.div continuousOn_const (continuousOn_id.pow 2) fun s hs => ?_
      rw [uIcc_of_le hs₁.1.le] at hs
      exact pow_ne_zero 2 (hβ0.trans_le hs.1).ne'
    have hderU : ∀ᵐ s, s ∈ Icc β s₁ → deriv (fun s => (χ s)⁻¹) s ≤ g s := by
      filter_upwards [hacχ.ae_differentiableAt, hder] with s hd hs hsI
      have hsI' := hsub s hsI
      have hs0 : 0 < s := hβ0.trans_le hsI.1
      have hχs := hpos s hsI'
      have hDs := hD1 s hsI'
      have hd' := (hd (by rwa [uIcc_of_le hs₁.1.le])).hasDerivAt
      have h2 : HasDerivAt (fun s => (χ s)⁻¹) (-(deriv χ s) / (χ s) ^ 2) s := hd'.inv hχs.ne'
      rw [h2.deriv]
      have hlow := hs hsI'
      have e1 : (χ s ^ 2 - κ * χ s * D s) / (3 * s ^ 2 * D s ^ 2) / χ s ^ 2 =
          1 / (3 * s ^ 2 * D s ^ 2) - κ / (3 * χ s) * (1 / (s ^ 2 * D s)) := by
        field_simp
      have hstep : -(deriv χ s) / χ s ^ 2 ≤
          -(1 / (3 * s ^ 2 * D s ^ 2)) + κ / (3 * χ s) * (1 / (s ^ 2 * D s)) := by
        have := div_le_div_of_nonneg_right hlow (by positivity : (0 : ℝ) ≤ χ s ^ 2)
        rw [e1] at this
        rw [neg_div]
        linarith
      refine hstep.trans ?_
      simp only [hg]
      have h3 : κ / (3 * χ s) ≤ κ / (3 * χ β) :=
        div_le_div_of_nonneg_left hκ (by positivity) (by linarith [hχge s hsI])
      have h4 : 1 / (s ^ 2 * D s) ≤ 1 / s ^ 2 :=
        div_le_div_of_nonneg_left zero_le_one (by positivity) (by nlinarith [sq_nonneg s])
      have h5 : 0 ≤ 1 / (s ^ 2 * D s) := by positivity
      nlinarith [mul_le_mul h3 h4 h5 (by positivity : 0 ≤ κ / (3 * χ β))]
    have hFTC := sub_le_integral_of_ae_deriv_le hs₁.1.le hU hgint hderU
    -- evaluate `∫ g`
    have hinv2 : ∫ s in β..s₁, 1 / s ^ 2 = 1 / β - 1 / s₁ := by
      have h := integral_eq_sub_of_hasDerivAt (f := fun s : ℝ => -s⁻¹) (f' := fun s => 1 / s ^ 2)
        (a := β) (b := s₁) (fun s hs => by
          rw [uIcc_of_le hs₁.1.le] at hs
          have hs0 : s ≠ 0 := (hβ0.trans_le hs.1).ne'
          have := (hasDerivAt_inv hs0).neg
          convert this using 1
          field_simp) ?_
      · rw [h]
        field_simp
        ring
      · refine ContinuousOn.intervalIntegrable ?_
        refine ContinuousOn.div continuousOn_const (continuousOn_id.pow 2) fun s hs => ?_
        rw [uIcc_of_le hs₁.1.le] at hs
        exact pow_ne_zero 2 (hβ0.trans_le hs.1).ne'
    have hgval : ∫ s in β..s₁, g s =
        -(∫ s in β..s₁, 1 / (3 * s ^ 2 * D s ^ 2)) + κ / (3 * χ β) * (1 / β - 1 / s₁) := by
      simp only [hg]
      rw [integral_add (f := fun s => -(1 / (3 * s ^ 2 * D s ^ 2)))
        (g := fun s => κ / (3 * χ β) * (1 / s ^ 2)) (hfint β s₁ le_rfl hs₁.1.le hs₁.2.le).neg,
        intervalIntegral.integral_neg,
        intervalIntegral.integral_const_mul, hinv2]
      refine (ContinuousOn.intervalIntegrable ?_).const_mul _
      refine ContinuousOn.div continuousOn_const (continuousOn_id.pow 2) fun s hs => ?_
      rw [uIcc_of_le hs₁.1.le] at hs
      exact pow_ne_zero 2 (hβ0.trans_le hs.1).ne'
    rw [hgval] at hFTC
    have hχs₁ := hpos s₁ hs₁I
    have hbound : κ / (3 * χ β) * (1 / β - 1 / s₁) ≤ J / χ β := by
      have h1 : 1 / β - 1 / s₁ ≤ 1 / β - 1 / βc := by
        have := one_div_le_one_div_of_le (hβ0.trans hs₁.1) hs₁.2.le
        linarith
      have e : J / χ β = κ / (3 * χ β) * (1 / β - 1 / βc) := by
        rw [hJ]
        field_simp
      rw [e]
      exact mul_le_mul_of_nonneg_left h1 (by positivity)
    have : 0 < (χ s₁)⁻¹ := inv_pos.2 hχs₁
    have e2 : (1 + J) / χ β = (χ β)⁻¹ + J / χ β := by field_simp
    rw [e2]
    linarith
  -- letting `s₁ ↑ β_c`
  have hIle : I ≤ (1 + J) / χ β := by
    refine le_of_forall_pos_lt_add fun ε hε => ?_
    set s₁ := max ((β + βc) / 2) (βc - ε * (3 * β ^ 2) / 2) with hs₁
    have hs₁mem : s₁ ∈ Ioo β βc := by
      refine ⟨lt_max_of_lt_left (by linarith [hβ.2]), max_lt (by linarith [hβ.2]) ?_⟩
      have : 0 < ε * (3 * β ^ 2) / 2 := by positivity
      linarith
    have hsplit : I = (∫ s in β..s₁, 1 / (3 * s ^ 2 * D s ^ 2)) +
        ∫ s in s₁..βc, 1 / (3 * s ^ 2 * D s ^ 2) :=
      (integral_add_adjacent_intervals (hfint β s₁ le_rfl hs₁mem.1.le hs₁mem.2.le)
        (hfint s₁ βc hs₁mem.1.le hs₁mem.2.le le_rfl)).symm
    have htail : ∫ s in s₁..βc, 1 / (3 * s ^ 2 * D s ^ 2) ≤ (βc - s₁) * (1 / (3 * β ^ 2)) := by
      have := integral_mono_on_of_le_Ioo hs₁mem.2.le (hfint s₁ βc hs₁mem.1.le hs₁mem.2.le le_rfl)
        (intervalIntegrable_const (c := 1 / (3 * β ^ 2))) fun s hs => by
          have hs0 : 0 < s := hβ0.trans (hs₁mem.1.trans hs.1)
          have hsI : s ∈ Ioo β₀ βc := ⟨hβ.1.trans (hs₁mem.1.trans hs.1), hs.2⟩
          have hDs := hD1 s hsI
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          have : β ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ hβ0.le (hs₁mem.1.trans hs.1).le 2
          nlinarith [mul_le_mul this (one_le_pow₀ hDs (n := 2)) zero_le_one (by positivity)]
      rwa [intervalIntegral.integral_const, smul_eq_mul] at this
    have hmain' := hmain s₁ hs₁mem
    have hs₁ge : βc - ε * (3 * β ^ 2) / 2 ≤ s₁ := le_max_right _ _
    have : (βc - s₁) * (1 / (3 * β ^ 2)) ≤ ε / 2 := by
      rw [mul_one_div, div_le_iff₀ (by positivity)]
      linarith
    linarith
  -- conclusion
  have hIpos : 0 < I := by
    refine intervalIntegral_pos_of_pos_on (hfint β βc le_rfl hβ.2.le le_rfl) (fun s hs => ?_) hβ.2
    have hs0 : 0 < s := hβ0.trans hs.1
    have hDs := hD1 s ⟨hβ.1.trans hs.1, hs.2⟩
    positivity
  rw [← div_eq_mul_inv, le_div_iff₀ hIpos, mul_comm, ← le_div_iff₀ hχβ]
  exact hIle

/-- For `0 ≤ β₀ < β < β_c` and `D ≥ 1` measurable on `(β₀, β_c)`, the function
`1/(3s²D(s)²)` is integrable on `[β, β_c]` and its integral there is strictly positive. -/
theorem intervalIntegrable_and_integral_pos_inv_three_sq_mul_sq (hβ₀ : 0 ≤ β₀)
    (hD : Measurable D) (hD1 : ∀ β ∈ Ioo β₀ βc, 1 ≤ D β) {β : ℝ} (hβ : β ∈ Ioo β₀ βc) :
    IntervalIntegrable (fun s => 1 / (3 * s ^ 2 * D s ^ 2)) volume β βc ∧
      0 < ∫ s in β..βc, 1 / (3 * s ^ 2 * D s ^ 2) := by
  have hβ0 : 0 < β := lt_of_le_of_lt hβ₀ hβ.1
  have hint : IntervalIntegrable (fun s => 1 / (3 * s ^ 2 * D s ^ 2)) volume β βc := by
    refine intervalIntegrable_of_bound_Ioo (M := 1 / (3 * β ^ 2)) hβ.2.le
      (measurable_inv_three_sq_mul_sq hD) fun s hs => ?_
    have hs0 : 0 < s := hβ0.trans hs.1
    have hDs := hD1 s ⟨hβ.1.trans hs.1, hs.2⟩
    rw [abs_of_nonneg (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
    have : β ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ hβ0.le hs.1.le 2
    nlinarith [mul_le_mul this (one_le_pow₀ hDs (n := 2)) zero_le_one (by positivity)]
  refine ⟨hint, intervalIntegral_pos_of_pos_on hint (fun s hs => ?_) hβ.2⟩
  have hs0 : 0 < s := hβ0.trans hs.1
  have hDs := hD1 s ⟨hβ.1.trans hs.1, hs.2⟩
  positivity

/-- `(x - d)₊² ≥ x² - 2xd` for `x, d ≥ 0`. -/
theorem sq_sub_two_mul_mul_le_max_sub_sq {x d : ℝ} (hx : 0 ≤ x) (hd : 0 ≤ d) :
    x ^ 2 - 2 * x * d ≤ max (x - d) 0 ^ 2 := by
  rcases le_total (x - d) 0 with h | h
  · rw [max_eq_right h]
    nlinarith
  · rw [max_eq_left h]
    nlinarith [sq_nonneg d]

/-- The squared positive-part inequality `χ' ≥ (χ - D)₊²/(3β²D²)` implies the linear form
`χ' ≥ (χ² - 2χD)/(3β²D²)`. -/
theorem ae_sq_sub_two_mul_div_le_deriv (hpos : ∀ β ∈ Ioo β₀ βc, 0 < χ β)
    (hD1 : ∀ β ∈ Ioo β₀ βc, 1 ≤ D β)
    (hder : ∀ᵐ β, β ∈ Ioo β₀ βc →
      max (χ β - D β) 0 ^ 2 / (3 * β ^ 2 * D β ^ 2) ≤ deriv χ β) :
    ∀ᵐ β, β ∈ Ioo β₀ βc → (χ β ^ 2 - 2 * χ β * D β) / (3 * β ^ 2 * D β ^ 2) ≤ deriv χ β :=
  hder.mono fun s h hs => (div_le_div_of_nonneg_right
    (sq_sub_two_mul_mul_le_max_sub_sq (hpos s hs).le (zero_le_one.trans (hD1 s hs)))
    (by positivity)).trans (h hs)

/-- **Integrated susceptibility bound.** Let `0 ≤ β₀ < β_c`, `χ > 0` nondecreasing and locally
absolutely continuous on `(β₀, β_c)`, `D ≥ 1` measurable and `χ' ≥ (χ - D)₊²/(3β²D²)` a.e. on
`(β₀, β_c)`. Then `χ(β) ≤ (1 + 2(β_c - β)/(3ββ_c)) (∫_β^{β_c} ds/(3s²D(s)²))⁻¹` for every
`β ∈ (β₀, β_c)`. -/
theorem le_of_deriv_ge_sq_div (hβ₀ : 0 ≤ β₀) (hpos : ∀ β ∈ Ioo β₀ βc, 0 < χ β)
    (hmono : MonotoneOn χ (Ioo β₀ βc))
    (hac : ∀ p q, β₀ < p → p ≤ q → q < βc → AbsolutelyContinuousOnInterval χ p q)
    (hD : Measurable D) (hD1 : ∀ β ∈ Ioo β₀ βc, 1 ≤ D β)
    (hder : ∀ᵐ β, β ∈ Ioo β₀ βc →
      max (χ β - D β) 0 ^ 2 / (3 * β ^ 2 * D β ^ 2) ≤ deriv χ β)
    {β : ℝ} (hβ : β ∈ Ioo β₀ βc) :
    χ β ≤ (1 + 2 * (βc - β) / (3 * β * βc)) * (∫ s in β..βc, 1 / (3 * s ^ 2 * D s ^ 2))⁻¹ :=
  le_of_deriv_ge_sq_sub_mul_div hβ₀ zero_le_two hpos hmono hac hD hD1
    (ae_sq_sub_two_mul_div_le_deriv hpos hD1 hder) hβ

/-- **Integrated susceptibility bound with the linear term `χ(χ - D)`.** Let `0 ≤ β₀ < β_c`,
`χ > 0` nondecreasing and locally absolutely continuous on `(β₀, β_c)`, `D ≥ 1` measurable and
`χ' ≥ χ(χ - D)/(3β²D²)` a.e. on `(β₀, β_c)`. Then
`χ(β) ≤ (1 + (β_c - β)/(3ββ_c)) (∫_β^{β_c} ds/(3s²D(s)²))⁻¹` for every `β ∈ (β₀, β_c)`. -/
theorem le_of_deriv_ge_mul_sub_div (hβ₀ : 0 ≤ β₀) (hpos : ∀ β ∈ Ioo β₀ βc, 0 < χ β)
    (hmono : MonotoneOn χ (Ioo β₀ βc))
    (hac : ∀ p q, β₀ < p → p ≤ q → q < βc → AbsolutelyContinuousOnInterval χ p q)
    (hD : Measurable D) (hD1 : ∀ β ∈ Ioo β₀ βc, 1 ≤ D β)
    (hder : ∀ᵐ β, β ∈ Ioo β₀ βc →
      χ β * (χ β - D β) / (3 * β ^ 2 * D β ^ 2) ≤ deriv χ β)
    {β : ℝ} (hβ : β ∈ Ioo β₀ βc) :
    χ β ≤ (1 + (βc - β) / (3 * β * βc)) * (∫ s in β..βc, 1 / (3 * s ^ 2 * D s ^ 2))⁻¹ := by
  have := le_of_deriv_ge_sq_sub_mul_div hβ₀ zero_le_one hpos hmono hac hD hD1
    (hder.mono fun s h hs => le_of_eq_of_le (by ring) (h hs)) hβ
  rwa [one_mul] at this

/-- **Logarithmic form, general linear term.** Under the hypotheses of
`le_of_deriv_ge_sq_sub_mul_div`, if moreover
`D(β_c - u) ≤ C (log(1/u))^a` for all small `u > 0`, with `C > 0` and `a ≥ 0`, then
`χ(β_c - ε) = O(ε⁻¹ (log(1/ε))^{2a})` as `ε ↓ 0`. -/
theorem isBigO_of_deriv_ge_sq_sub_mul_div {κ : ℝ} (hβ₀ : 0 ≤ β₀) (hκ : 0 ≤ κ) (hlt : β₀ < βc)
    (hpos : ∀ β ∈ Ioo β₀ βc, 0 < χ β) (hmono : MonotoneOn χ (Ioo β₀ βc))
    (hac : ∀ p q, β₀ < p → p ≤ q → q < βc → AbsolutelyContinuousOnInterval χ p q)
    (hD : Measurable D) (hD1 : ∀ β ∈ Ioo β₀ βc, 1 ≤ D β)
    (hder : ∀ᵐ β, β ∈ Ioo β₀ βc →
      (χ β ^ 2 - κ * χ β * D β) / (3 * β ^ 2 * D β ^ 2) ≤ deriv χ β)
    {C a : ℝ} (hC : 0 < C) (ha : 0 ≤ a)
    (hDlog : ∀ᶠ u in 𝓝[>] 0, D (βc - u) ≤ C * Real.log (1 / u) ^ a) :
    (fun ε => χ (βc - ε)) =O[𝓝[>] 0] fun ε => ε⁻¹ * Real.log (1 / ε) ^ (2 * a) := by
  have hβc0 : 0 < βc := lt_of_le_of_lt hβ₀ hlt
  obtain ⟨δ, hδ, hδD⟩ : ∃ δ > 0, ∀ u, 0 < u → u < δ → D (βc - u) ≤ C * Real.log (1 / u) ^ a := by
    obtain ⟨δ, hδ, h⟩ := Metric.eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 hDlog)
    exact ⟨δ, hδ, fun u hu hu' => h (by rwa [Real.dist_eq, sub_zero, abs_of_pos hu]) hu⟩
  set K₁ := 1 + 2 * κ / (3 * βc ^ 2)
  set K := K₁ * (6 * βc ^ 2 * C ^ 2 * 4 ^ a)
  refine IsBigO.of_bound K ?_
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ∈ Ioo 0 (min δ (min (1 / 2) (min (βc / 2) (βc - β₀)))) :=
    Ioo_mem_nhdsGT (lt_min hδ (lt_min (by norm_num) (lt_min (by positivity) (by linarith))))
  filter_upwards [hev] with ε hε
  obtain ⟨hε0, hε1⟩ := hε
  have hεδ : ε < δ := hε1.trans_le (min_le_left _ _)
  have hεh : ε < 1 / 2 := hε1.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hεc : ε < βc / 2 :=
    hε1.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hεb : ε < βc - β₀ :=
    hε1.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  set β := βc - ε with hβeq
  have hβ : β ∈ Ioo β₀ βc := ⟨by linarith, by linarith⟩
  have hβ0 : 0 < β := by linarith
  have hmain := le_of_deriv_ge_sq_sub_mul_div hβ₀ hκ hpos hmono hac hD hD1 hder hβ
  -- `1 + J ≤ K₁`
  have hJ : 1 + κ * (βc - β) / (3 * β * βc) ≤ K₁ := by
    have : κ * (βc - β) / (3 * β * βc) ≤ 2 * κ / (3 * βc ^ 2) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : βc - β = ε := by rw [hβeq]; ring
      rw [this]
      have h1 : ε * βc ≤ 2 * β := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left h1 hκ]
    linarith
  -- the logarithm
  have hL : 0 < Real.log (1 / ε) :=
    Real.log_pos (by rw [one_div]; exact one_lt_inv_iff₀.2 ⟨hε0, by linarith⟩)
  have hL2 : Real.log (2 / ε) ≤ 2 * Real.log (1 / ε) := by
    rw [show 2 / ε = 2 * (1 / ε) by ring, Real.log_mul (by norm_num) (by positivity)]
    have : Real.log 2 ≤ Real.log (1 / ε) :=
      Real.log_le_log (by norm_num) (by rw [le_div_iff₀ hε0]; linarith)
    linarith
  set m := 1 / (3 * βc ^ 2 * (C * (2 * Real.log (1 / ε)) ^ a) ^ 2)
  have hm : 0 < m := by positivity
  -- `I ≥ (ε/2) m`
  have hfint : IntervalIntegrable (fun s => 1 / (3 * s ^ 2 * D s ^ 2)) volume β βc := by
    refine intervalIntegrable_of_bound_Ioo (M := 1 / (3 * β ^ 2)) hβ.2.le
      (measurable_inv_three_sq_mul_sq hD) fun s hs => ?_
    have hs0 : 0 < s := hβ0.trans hs.1
    have hDs := hD1 s ⟨hβ.1.trans hs.1, hs.2⟩
    rw [abs_of_nonneg (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
    have : β ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ hβ0.le hs.1.le 2
    nlinarith [mul_le_mul this (one_le_pow₀ hDs (n := 2)) zero_le_one (by positivity)]
  have hI : ε / 2 * m ≤ ∫ s in β..βc, 1 / (3 * s ^ 2 * D s ^ 2) := by
    have hmid : β ≤ βc - ε / 2 := by linarith
    have h1 : ∫ s in β..βc - ε / 2, 1 / (3 * s ^ 2 * D s ^ 2) ≤
        ∫ s in β..βc, 1 / (3 * s ^ 2 * D s ^ 2) :=
      integral_mono_interval le_rfl hmid (by linarith)
        (Eventually.of_forall fun s => by
          simp only [Pi.zero_apply]
          positivity) hfint
    have h2 : ∫ s in β..βc - ε / 2, m ≤ ∫ s in β..βc - ε / 2, 1 / (3 * s ^ 2 * D s ^ 2) := by
      refine integral_mono_on_of_le_Ioo hmid intervalIntegrable_const
        (hfint.mono_set (by
          rw [uIcc_of_le hmid, uIcc_of_le hβ.2.le]
          exact Icc_subset_Icc le_rfl (by linarith))) fun s hs => ?_
      have hs0 : 0 < s := hβ0.trans hs.1
      have hsI : s ∈ Ioo β₀ βc := ⟨hβ.1.trans hs.1, by linarith [hs.2]⟩
      have hDs := hD1 s hsI
      set u := βc - s with hu
      have hu0 : 0 < u := by linarith [hs.2]
      have huε : ε / 2 < u := by linarith [hs.2]
      have hDu : D s ≤ C * Real.log (1 / u) ^ a := by
        have := hδD u hu0 (by linarith [hs.1])
        rwa [hu, sub_sub_cancel] at this
      have hlogu : Real.log (1 / u) ≤ 2 * Real.log (1 / ε) := by
        refine le_trans ?_ hL2
        refine Real.log_le_log (by positivity) ?_
        rw [div_le_div_iff₀ hu0 hε0]
        linarith
      have hlogu0 : 0 ≤ Real.log (1 / u) := by
        refine Real.log_nonneg ?_
        rw [le_div_iff₀ hu0]
        linarith [hs.1]
      have hDle : D s ≤ C * (2 * Real.log (1 / ε)) ^ a :=
        hDu.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hlogu0 hlogu ha) hC.le)
      have hD0 : 0 < D s := by linarith
      rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul, one_mul]
      have hs2 : s ^ 2 ≤ βc ^ 2 := pow_le_pow_left₀ hs0.le (by linarith [hs.2]) 2
      have hD2 : D s ^ 2 ≤ (C * (2 * Real.log (1 / ε)) ^ a) ^ 2 :=
        pow_le_pow_left₀ hD0.le hDle 2
      nlinarith [mul_le_mul hs2 hD2 (by positivity) (by positivity)]
    rw [intervalIntegral.integral_const, smul_eq_mul] at h2
    have : βc - ε / 2 - β = ε / 2 := by rw [hβeq]; ring
    rw [this] at h2
    linarith
  have hIpos : 0 < ε / 2 * m := by positivity
  -- assembling
  have hχ := hpos β hβ
  rw [Real.norm_of_nonneg hχ.le,
    Real.norm_of_nonneg (mul_nonneg (inv_nonneg.2 hε0.le) (Real.rpow_nonneg hL.le _))]
  calc χ β ≤ (1 + κ * (βc - β) / (3 * β * βc)) *
        (∫ s in β..βc, 1 / (3 * s ^ 2 * D s ^ 2))⁻¹ := hmain
    _ ≤ K₁ * (ε / 2 * m)⁻¹ :=
        mul_le_mul hJ (inv_anti₀ hIpos hI) (inv_nonneg.2 (hIpos.le.trans hI)) (by positivity)
    _ = K * (ε⁻¹ * Real.log (1 / ε) ^ (2 * a)) := by
        have h4 : ((2 : ℝ) ^ a) ^ 2 = 4 ^ a := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm,
            Real.rpow_mul (by norm_num)]
          norm_num
        have hL' : (Real.log (1 / ε) ^ a) ^ 2 = Real.log (1 / ε) ^ (2 * a) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hL.le]
          congr 1
          push_cast
          ring
        have e1 : (C * (2 * Real.log (1 / ε)) ^ a) ^ 2 =
            C ^ 2 * 4 ^ a * Real.log (1 / ε) ^ (2 * a) := by
          rw [Real.mul_rpow (by norm_num) hL.le, mul_pow, mul_pow, h4, hL']
          ring
        simp only [m, K, e1]
        field_simp
        ring

/-- **Logarithmic form.** Under the hypotheses of `le_of_deriv_ge_sq_div`, if moreover
`D(β_c - u) ≤ C (log(1/u))^a` for all small `u > 0`, with `C > 0` and `a ≥ 0`, then
`χ(β_c - ε) = O(ε⁻¹ (log(1/ε))^{2a})` as `ε ↓ 0`. -/
theorem isBigO_of_deriv_ge_sq_div (hβ₀ : 0 ≤ β₀) (hlt : β₀ < βc)
    (hpos : ∀ β ∈ Ioo β₀ βc, 0 < χ β) (hmono : MonotoneOn χ (Ioo β₀ βc))
    (hac : ∀ p q, β₀ < p → p ≤ q → q < βc → AbsolutelyContinuousOnInterval χ p q)
    (hD : Measurable D) (hD1 : ∀ β ∈ Ioo β₀ βc, 1 ≤ D β)
    (hder : ∀ᵐ β, β ∈ Ioo β₀ βc →
      max (χ β - D β) 0 ^ 2 / (3 * β ^ 2 * D β ^ 2) ≤ deriv χ β)
    {C a : ℝ} (hC : 0 < C) (ha : 0 ≤ a)
    (hDlog : ∀ᶠ u in 𝓝[>] 0, D (βc - u) ≤ C * Real.log (1 / u) ^ a) :
    (fun ε => χ (βc - ε)) =O[𝓝[>] 0] fun ε => ε⁻¹ * Real.log (1 / ε) ^ (2 * a) :=
  isBigO_of_deriv_ge_sq_sub_mul_div hβ₀ zero_le_two hlt hpos hmono hac hD hD1
    (ae_sq_sub_two_mul_div_le_deriv hpos hD1 hder) hC ha hDlog

/-- **Logarithmic form for the linear term `χ(χ - D)`.** Under the hypotheses of
`le_of_deriv_ge_mul_sub_div`, suppose `D(β_c - u) ≤ C (log(1/u))^a` for `0 < u < ε₀`, with
`C > 0`, `a ≥ 0` and `ε₀ > 0`. Then there are `C' > 0` and `ε₁ > 0` with
`χ(β_c - ε) ≤ C' ε⁻¹ (log(1/ε))^{2a}` for `0 < ε < ε₁`. -/
theorem exists_le_inv_mul_log_rpow_of_deriv_ge_mul_sub_div (hβ₀ : 0 ≤ β₀) (hlt : β₀ < βc)
    (hpos : ∀ β ∈ Ioo β₀ βc, 0 < χ β) (hmono : MonotoneOn χ (Ioo β₀ βc))
    (hac : ∀ p q, β₀ < p → p ≤ q → q < βc → AbsolutelyContinuousOnInterval χ p q)
    (hD : Measurable D) (hD1 : ∀ β ∈ Ioo β₀ βc, 1 ≤ D β)
    (hder : ∀ᵐ β, β ∈ Ioo β₀ βc →
      χ β * (χ β - D β) / (3 * β ^ 2 * D β ^ 2) ≤ deriv χ β)
    {C a ε₀ : ℝ} (hC : 0 < C) (ha : 0 ≤ a) (hε₀ : 0 < ε₀)
    (hDlog : ∀ u, 0 < u → u < ε₀ → D (βc - u) ≤ C * Real.log (1 / u) ^ a) :
    ∃ C' > 0, ∃ ε₁ > 0, ∀ ε, 0 < ε → ε < ε₁ →
      χ (βc - ε) ≤ C' * (ε⁻¹ * Real.log (1 / ε) ^ (2 * a)) := by
  have hev : ∀ᶠ u in 𝓝[>] (0 : ℝ), D (βc - u) ≤ C * Real.log (1 / u) ^ a := by
    filter_upwards [Ioo_mem_nhdsGT hε₀] with u hu using hDlog u hu.1 hu.2
  obtain ⟨c, hc⟩ := (isBigO_of_deriv_ge_sq_sub_mul_div hβ₀ zero_le_one hlt hpos hmono hac hD
    hD1 (hder.mono fun s h hs => le_of_eq_of_le (by ring) (h hs)) hC ha hev).bound
  have hlt' : (0 : ℝ) < min 1 (βc - β₀) := lt_min one_pos (by linarith)
  obtain ⟨ε₁, hε₁, h⟩ := (nhdsGT_basis (0 : ℝ)).eventually_iff.1
    (hc.and (Ioo_mem_nhdsGT hlt'))
  refine ⟨max c 1, by positivity, ε₁, hε₁, fun ε hε hε' => ?_⟩
  obtain ⟨h1, h2⟩ := h ⟨hε, hε'⟩
  have hε1 : ε ≤ 1 := h2.2.le.trans (min_le_left _ _)
  have hεb : ε < βc - β₀ := h2.2.trans_le (min_le_right _ _)
  have hL : 0 ≤ Real.log (1 / ε) := Real.log_nonneg (by rw [le_div_iff₀ hε]; linarith)
  rw [Real.norm_of_nonneg (hpos _ ⟨by linarith, by linarith⟩).le,
    Real.norm_of_nonneg (mul_nonneg (inv_nonneg.2 hε.le) (Real.rpow_nonneg hL _))] at h1
  exact h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
    (mul_nonneg (inv_nonneg.2 hε.le) (Real.rpow_nonneg hL _)))

/-- **Bounded diagrams.** Under the hypotheses of `le_of_deriv_ge_mul_sub_div`, if
`D(β_c - u) ≤ C` for `0 < u < ε₀`, then `χ(β_c - ε) ≤ C' ε⁻¹` for `0 < ε < ε₁`, for some
`C', ε₁ > 0`. -/
theorem exists_le_inv_of_deriv_ge_mul_sub_div (hβ₀ : 0 ≤ β₀) (hlt : β₀ < βc)
    (hpos : ∀ β ∈ Ioo β₀ βc, 0 < χ β) (hmono : MonotoneOn χ (Ioo β₀ βc))
    (hac : ∀ p q, β₀ < p → p ≤ q → q < βc → AbsolutelyContinuousOnInterval χ p q)
    (hD : Measurable D) (hD1 : ∀ β ∈ Ioo β₀ βc, 1 ≤ D β)
    (hder : ∀ᵐ β, β ∈ Ioo β₀ βc →
      χ β * (χ β - D β) / (3 * β ^ 2 * D β ^ 2) ≤ deriv χ β)
    {C ε₀ : ℝ} (hC : 0 < C) (hε₀ : 0 < ε₀) (hDb : ∀ u, 0 < u → u < ε₀ → D (βc - u) ≤ C) :
    ∃ C' > 0, ∃ ε₁ > 0, ∀ ε, 0 < ε → ε < ε₁ → χ (βc - ε) ≤ C' * ε⁻¹ := by
  obtain ⟨C', hC', ε₁, hε₁, h⟩ := exists_le_inv_mul_log_rpow_of_deriv_ge_mul_sub_div hβ₀ hlt
    hpos hmono hac hD hD1 hder hC le_rfl hε₀ (a := 0) fun u hu hu' => by
      simpa using hDb u hu hu'
  exact ⟨C', hC', ε₁, hε₁, fun ε hε hε' => by simpa using h ε hε hε'⟩

/-! ### Non-vacuity: `D ≡ 1`, `χ ≡ 1` (the equality case `χ' = (χ - D)₊²/(3β²D²) = 0`) -/

example : (fun _ : ℝ => (1 : ℝ)) (1 / 2) ≤ (1 + 2 * (1 - 1 / 2) / (3 * (1 / 2) * 1)) *
    (∫ s in (1 / 2 : ℝ)..1, 1 / (3 * s ^ 2 * (fun _ : ℝ => (1 : ℝ)) s ^ 2))⁻¹ :=
  le_of_deriv_ge_sq_div (β₀ := 0) (βc := 1) le_rfl (fun _ _ => one_pos)
    (fun _ _ _ _ _ => le_rfl)
    (fun _ _ _ _ _ =>
      (LipschitzWith.const (1 : ℝ)).lipschitzOnWith.absolutelyContinuousOnInterval)
    measurable_const (fun _ _ => le_rfl) (Eventually.of_forall fun _ _ => by simp)
    ⟨by norm_num, by norm_num⟩

example : (fun ε : ℝ => (fun _ : ℝ => (1 : ℝ)) (1 - ε)) =O[𝓝[>] 0]
    fun ε => ε⁻¹ * Real.log (1 / ε) ^ (2 * (0 : ℝ)) :=
  isBigO_of_deriv_ge_sq_div (β₀ := 0) (βc := 1) le_rfl one_pos (fun _ _ => one_pos)
    (fun _ _ _ _ _ => le_rfl)
    (fun _ _ _ _ _ =>
      (LipschitzWith.const (1 : ℝ)).lipschitzOnWith.absolutelyContinuousOnInterval)
    measurable_const (fun _ _ => le_rfl) (Eventually.of_forall fun _ _ => by simp) one_pos le_rfl
    (Eventually.of_forall fun _ => by simp)

/-! ### OP8F: the quadratic deficit ODE -/

/-- **Logarithmic integration.** If `h` is absolutely continuous on every `[r₀, R]`, `r₀ > 0`,
and `r h'(r) → L` in the a.e. sense, then `h(R)/log R → L`. -/
theorem tendsto_div_log_of_mul_deriv {h : ℝ → ℝ} {r₀ L : ℝ} (hr₀ : 0 < r₀)
    (hac : ∀ R, r₀ ≤ R → AbsolutelyContinuousOnInterval h r₀ R)
    (hder : ∀ δ > 0, ∃ R₁, ∀ᵐ r, R₁ ≤ r → |r * deriv h r - L| ≤ δ) :
    Tendsto (fun R => h R / Real.log R) atTop (𝓝 L) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨R₁', hR₁'⟩ := hder (ε / 3) (by positivity)
  set R₁ := max (max R₁' r₀) 2 with hR₁
  have hR₁r₀ : r₀ ≤ R₁ := (le_max_right _ _).trans (le_max_left _ _)
  have hR₁pos : 0 < R₁ := hr₀.trans_le hR₁r₀
  have hR₁1 : 1 < R₁ := by linarith [le_max_right (max R₁' r₀) 2]
  set B := |h R₁ - L * Real.log R₁| + (|L| + ε) * |Real.log R₁| with hB
  -- choose `R₂` with `B / log R₂ < ε/3`
  have hlog : Tendsto Real.log atTop atTop := Real.tendsto_log_atTop
  obtain ⟨R₂, hR₂⟩ := eventually_atTop.1 ((tendsto_atTop.1 hlog) (3 * B / ε + 1))
  refine ⟨max R₁ (max R₂ 3), fun R hR => ?_⟩
  have hRR₁ : R₁ ≤ R := (le_max_left _ _).trans hR
  have hR3 : 3 ≤ R := ((le_max_right _ _).trans (le_max_right _ _)).trans hR
  have hRpos : 0 < R := by linarith
  have hlogR : 0 < Real.log R := Real.log_pos (by linarith)
  have hlogRB : 3 * B / ε + 1 ≤ Real.log R :=
    hR₂ R ((le_max_left _ _).trans ((le_max_right _ _).trans hR))
  have hacR : AbsolutelyContinuousOnInterval h R₁ R := (hac R (hR₁r₀.trans hRR₁)).mono (by
    rw [uIcc_of_le hRR₁, uIcc_of_le (hR₁r₀.trans hRR₁)]
    exact Icc_subset_Icc hR₁r₀ le_rfl)
  have hint : ∀ c : ℝ, ∫ r in R₁..R, c / r = c * (Real.log R - Real.log R₁) := by
    intro c
    simp_rw [div_eq_mul_inv]
    rw [intervalIntegral.integral_const_mul, integral_inv_of_pos hR₁pos hRpos,
      Real.log_div hRpos.ne' hR₁pos.ne']
  have hcont : ∀ c : ℝ, IntervalIntegrable (fun r => c / r) volume R₁ R := fun c =>
    (ContinuousOn.intervalIntegrable (continuousOn_const.div continuousOn_id fun r hr => by
      rw [uIcc_of_le hRR₁] at hr
      exact (hR₁pos.trans_le hr.1).ne'))
  have hae : ∀ᵐ r, r ∈ Icc R₁ R → |r * deriv h r - L| ≤ ε / 3 := by
    filter_upwards [hR₁'] with r hr hrI
    exact hr ((le_max_left _ _).trans ((le_max_left _ _).trans hrI.1))
  -- lower and upper bounds
  have hlow := integral_le_sub_of_ae_le_deriv hRR₁ hacR (hcont (L - ε / 3)) (by
    filter_upwards [hae] with r hr hrI
    have hr0 : 0 < r := hR₁pos.trans_le hrI.1
    have := (abs_le.1 (hr hrI)).1
    rw [div_le_iff₀ hr0]
    linarith)
  have hup := sub_le_integral_of_ae_deriv_le hRR₁ hacR (hcont (L + ε / 3)) (by
    filter_upwards [hae] with r hr hrI
    have hr0 : 0 < r := hR₁pos.trans_le hrI.1
    have := (abs_le.1 (hr hrI)).2
    rw [le_div_iff₀ hr0]
    linarith)
  rw [hint] at hlow hup
  -- conclude
  rw [Real.dist_eq, abs_lt]
  have hB0 : 0 ≤ B := by positivity
  have hBR : B ≤ ε / 3 * Real.log R := by
    have : 3 * B / ε ≤ Real.log R := by linarith
    rw [div_le_iff₀ hε] at this
    linarith
  have hlogR₁ : 0 ≤ Real.log R₁ := (Real.log_pos hR₁1).le
  have hA : |h R₁ - L * Real.log R₁| ≤ B := by
    rw [hB]
    have : 0 ≤ (|L| + ε) * |Real.log R₁| := by positivity
    linarith
  have hA' : (ε / 3) * Real.log R₁ ≤ B := by
    rw [hB, abs_of_nonneg hlogR₁]
    have := abs_nonneg (h R₁ - L * Real.log R₁)
    have : ε / 3 * Real.log R₁ ≤ (|L| + ε) * Real.log R₁ :=
      mul_le_mul_of_nonneg_right (by linarith [abs_nonneg L]) hlogR₁
    linarith
  obtain ⟨hA1, hA2⟩ := abs_le.1 hA
  constructor
  · rw [lt_sub_iff_add_lt, lt_div_iff₀ hlogR]
    nlinarith
  · rw [sub_lt_iff_lt_add, div_lt_iff₀ hlogR]
    nlinarith

/-- A positive function that is absolutely continuous on `[p, q]` has an absolutely continuous
reciprocal there. -/
theorem absolutelyContinuousOnInterval_inv {u : ℝ → ℝ} {p q : ℝ} (hpq : p ≤ q)
    (hu : AbsolutelyContinuousOnInterval u p q) (hpos : ∀ r ∈ Icc p q, 0 < u r) :
    AbsolutelyContinuousOnInterval (fun r => (u r)⁻¹) p q := by
  obtain ⟨x₀, hx₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hpq)
    (by simpa [uIcc_of_le hpq] using hu.continuousOn)
  set μ := u x₀
  have hμ : 0 < μ := hpos x₀ hx₀
  have hlip : LipschitzOnWith (Real.toNNReal (1 / μ ^ 2)) (fun x : ℝ => x⁻¹) (Ici μ) := by
    refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
    have hx0 : 0 < x := lt_of_lt_of_le hμ hx
    have hy0 : 0 < y := lt_of_lt_of_le hμ hy
    rw [Real.coe_toNNReal _ (by positivity), Real.dist_eq, Real.dist_eq,
      inv_sub_inv hx0.ne' hy0.ne', abs_div, abs_of_pos (mul_pos hx0 hy0), abs_sub_comm,
      div_le_iff₀ (mul_pos hx0 hy0)]
    have hxy : μ ^ 2 ≤ x * y := by nlinarith [mem_Ici.1 hx, mem_Ici.1 hy]
    have e : 1 / μ ^ 2 * |x - y| * (x * y) = |x - y| * ((x * y) / μ ^ 2) := by ring
    rw [e]
    have : 1 ≤ (x * y) / μ ^ 2 := by rw [le_div_iff₀ (by positivity)]; linarith
    nlinarith [abs_nonneg (x - y)]
  exact hlip.comp_absolutelyContinuousOnInterval (fun r hr => by
    rw [uIcc_of_le hpq] at hr
    exact hmin hr) hu

/-- **OP8F.** Let `a₀, c, ν, K > 0` and `r₀ > 1`, and let `α` be real. Suppose:
* `m, f > 0` are absolutely continuous on every `[r₀, R]`, and `b > 0`;
* `m ~ c r^α`, `a ~ a₀ r^{-α-1}` and `b ~ ν r^{3α}`;
* `m' = a m² (1 - e₁)`, `f' = 3 a m f (1 - e₂)` and `e₂ - e₁ = (K + ε) f²/(b m³)`
  a.e. on `[r₀, ∞)`, with `ε → 0`.

Then `f/m³ ~ (6 K a₀ c⁴ log r / ν)^{-1/2}` and
`f ~ c √(ν/(6 K a₀)) r^{3α}/√(log r)`. -/
@[tag "OP8F"]
theorem op8f_asymptotics {α a₀ c ν K r₀ : ℝ} (ha₀ : 0 < a₀) (hc : 0 < c)
    (hν : 0 < ν) (hK : 0 < K) (hr₀ : 1 < r₀) {m f a b e₁ e₂ ε : ℝ → ℝ}
    (hm0 : ∀ r, r₀ ≤ r → 0 < m r) (hf0 : ∀ r, r₀ ≤ r → 0 < f r)
    (hmac : ∀ R, r₀ ≤ R → AbsolutelyContinuousOnInterval m r₀ R)
    (hfac : ∀ R, r₀ ≤ R → AbsolutelyContinuousOnInterval f r₀ R)
    (hb0 : ∀ r, r₀ ≤ r → 0 < b r)
    (hm : m ~[atTop] fun r => c * r ^ α) (ha : a ~[atTop] fun r => a₀ * r ^ (-α - 1))
    (hb : b ~[atTop] fun r => ν * r ^ (3 * α))
    (hdm : ∀ᵐ r, r₀ ≤ r → deriv m r = a r * m r ^ 2 * (1 - e₁ r))
    (hdf : ∀ᵐ r, r₀ ≤ r → deriv f r = 3 * a r * m r * f r * (1 - e₂ r))
    (he : ∀ᵐ r, r₀ ≤ r → e₂ r - e₁ r = (K + ε r) * f r ^ 2 / (b r * m r ^ 3))
    (hε : Tendsto ε atTop (𝓝 0)) :
    ((fun r => f r / m r ^ 3) ~[atTop]
        fun r => (6 * K * a₀ * c ^ 4 * Real.log r / ν) ^ (-(1 / 2 : ℝ))) ∧
      f ~[atTop] fun r =>
        c * Real.sqrt (ν / (6 * K * a₀)) * r ^ (3 * α) / Real.sqrt (Real.log r) := by
  set L := 6 * K * a₀ * c ^ 4 / ν with hL
  have hL0 : 0 < L := by positivity
  have hr₀0 : 0 < r₀ := by linarith
  set h : ℝ → ℝ := fun r => m r ^ 6 * (f r ^ 2)⁻¹ with hh
  -- `h` is absolutely continuous on `[r₀, R]`
  have hhac : ∀ R, r₀ ≤ R → AbsolutelyContinuousOnInterval h r₀ R := by
    intro R hR
    have hmR := hmac R hR
    have hfR := hfac R hR
    have h6 : AbsolutelyContinuousOnInterval (fun r => m r ^ 6) r₀ R := by
      have := (((((hmR.mul hmR).mul hmR).mul hmR).mul hmR).mul hmR)
      convert this using 1
      funext r
      simp only [Pi.mul_apply]
      ring
    have h2 : AbsolutelyContinuousOnInterval (fun r => f r ^ 2) r₀ R := by
      convert hfR.mul hfR using 1
      funext r
      simp only [Pi.mul_apply]
      ring
    have hi := absolutelyContinuousOnInterval_inv hR h2 fun r hr => by
      have := hf0 r hr.1
      positivity
    convert h6.mul hi using 1
  -- a.e. differentiability of `m` and `f` on `[r₀, ∞)`
  have hdiff : ∀ᵐ r, r₀ ≤ r → DifferentiableAt ℝ m r ∧ DifferentiableAt ℝ f r := by
    have hm' := ae_all_iff.2 fun n : ℕ => (hmac (r₀ + n) (by linarith [n.cast_nonneg (α := ℝ)])
      ).ae_differentiableAt
    have hf' := ae_all_iff.2 fun n : ℕ => (hfac (r₀ + n) (by linarith [n.cast_nonneg (α := ℝ)])
      ).ae_differentiableAt
    filter_upwards [hm', hf'] with r hmr hfr hr
    obtain ⟨n, hn⟩ := exists_nat_ge (r - r₀)
    have hmem : r ∈ uIcc r₀ (r₀ + n) := by
      rw [uIcc_of_le (by linarith [n.cast_nonneg (α := ℝ)])]
      exact ⟨hr, by linarith⟩
    exact ⟨hmr n hmem, hfr n hmem⟩
  -- the derivative of `h`
  set φ : ℝ → ℝ := fun r => 6 * a r * (K + ε r) * m r ^ 4 / b r with hφ
  have hderh : ∀ᵐ r, r₀ ≤ r → deriv h r = φ r := by
    filter_upwards [hdiff, hdm, hdf, he] with r hd hdm' hdf' he' hr
    obtain ⟨hmd, hfd⟩ := hd hr
    have hmr := hm0 r hr
    have hfr := hf0 r hr
    have hbr := hb0 r hr
    have hD := (hmd.hasDerivAt.pow 6).mul ((hfd.hasDerivAt.pow 2).inv (pow_ne_zero 2 hfr.ne'))
    have hD' : HasDerivAt h ((6 : ℕ) * m r ^ (6 - 1) * deriv m r * (f r ^ 2)⁻¹ +
        m r ^ 6 * (-((2 : ℕ) * f r ^ (2 - 1) * deriv f r) / (f r ^ 2) ^ 2)) r := hD
    rw [hD'.deriv]
    norm_num
    rw [hdm' hr, hdf' hr]
    have he'' : e₂ r = e₁ r + (K + ε r) * f r ^ 2 / (b r * m r ^ 3) := by
      linarith [he' hr]
    rw [he'']
    simp only [hφ]
    field_simp
    ring
  -- `r φ(r) → L`
  have hrφ : Tendsto (fun r => r * φ r) atTop (𝓝 L) := by
    have hKε : (fun r => K + ε r) ~[atTop] fun _ => K := by
      have : Tendsto (fun r => K + ε r) atTop (𝓝 K) := by
        simpa using (tendsto_const_nhds (x := K)).add hε
      exact (isEquivalent_const_iff_tendsto hK.ne').2 this
    have hequiv : (fun r => r * φ r) ~[atTop] fun r =>
        r * (6 * (a₀ * r ^ (-α - 1)) * K * (c * r ^ α) ^ 4 / (ν * r ^ (3 * α))) := by
      have := (((((IsEquivalent.refl (u := fun r : ℝ => r)).mul
        ((IsEquivalent.refl (u := fun _ : ℝ => (6 : ℝ))).mul ha)).mul hKε).mul (hm.pow 4)).div hb)
      convert this using 1
      · funext r
        simp only [hφ, Pi.mul_apply, Pi.div_apply, Pi.pow_apply]
        ring
      · funext r
        simp only [Pi.mul_apply, Pi.div_apply, Pi.pow_apply]
        ring
    have hconst : (fun r : ℝ =>
        r * (6 * (a₀ * r ^ (-α - 1)) * K * (c * r ^ α) ^ 4 / (ν * r ^ (3 * α)))) =ᶠ[atTop]
        fun _ => L := by
      filter_upwards [eventually_gt_atTop 0] with r hr
      have e1 : r * r ^ (-α - 1) * (r ^ α) ^ 4 = r ^ (3 * α) := by
        rw [← Real.rpow_natCast (r ^ α) 4, ← Real.rpow_mul hr.le,
          show r * r ^ (-α - 1) = r ^ (1 + (-α - 1)) by rw [Real.rpow_add hr, Real.rpow_one],
          ← Real.rpow_add hr]
        congr 1
        push_cast
        ring
      have hr3 : 0 < r ^ (3 * α) := Real.rpow_pos_of_pos hr _
      rw [hL]
      field_simp
      rw [e1]
      ring_nf
    exact (hequiv.congr_right hconst).symm.tendsto_nhds tendsto_const_nhds
  -- `h(R)/log R → L`
  have hlog : Tendsto (fun R => h R / Real.log R) atTop (𝓝 L) := by
    refine tendsto_div_log_of_mul_deriv hr₀0 hhac fun δ hδ => ?_
    obtain ⟨R₁, hR₁⟩ := eventually_atTop.1
      (Metric.tendsto_nhds.1 hrφ δ hδ)
    refine ⟨max R₁ r₀, ?_⟩
    filter_upwards [hderh] with r hr hrR
    rw [hr ((le_max_right _ _).trans hrR)]
    have := hR₁ r ((le_max_left _ _).trans hrR)
    rw [Real.dist_eq] at this
    exact this.le
  -- the ratio `f/m³` against `(L log r)^{-1/2}`
  have hX : ∀ r, (6 * K * a₀ * c ^ 4 * Real.log r / ν) = L * Real.log r := fun r => by
    rw [hL]; ring
  have hev : ∀ᶠ r in atTop, max r₀ 3 ≤ r := eventually_ge_atTop _
  have h1 : (fun r => f r / m r ^ 3) ~[atTop]
      fun r => (6 * K * a₀ * c ^ 4 * Real.log r / ν) ^ (-(1 / 2 : ℝ)) := by
    refine isEquivalent_of_tendsto_one ?_
    have hlim : Tendsto (fun r => Real.sqrt (L / (h r / Real.log r))) atTop (𝓝 1) := by
      have := ((tendsto_const_nhds (x := L)).div hlog hL0.ne').sqrt
      rwa [div_self hL0.ne', Real.sqrt_one] at this
    refine hlim.congr' ?_
    filter_upwards [hev] with r hr
    have hr₀r : r₀ ≤ r := (le_max_left _ _).trans hr
    have hlr : 0 < Real.log r := Real.log_pos (by linarith [le_max_right r₀ 3])
    have hmr := hm0 r hr₀r
    have hfr := hf0 r hr₀r
    have hX0 : 0 < L * Real.log r := mul_pos hL0 hlr
    simp only [Pi.div_apply, hX, hh]
    rw [Real.rpow_neg hX0.le, ← Real.sqrt_eq_rpow, div_inv_eq_mul]
    have e1 : L / (m r ^ 6 * (f r ^ 2)⁻¹ / Real.log r) =
        (L * Real.log r) * (f r / m r ^ 3) ^ 2 := by
      field_simp
    rw [e1, Real.sqrt_mul hX0.le, Real.sqrt_sq (by positivity), mul_comm]
  refine ⟨h1, ?_⟩
  -- `f ~ c √(ν/(6Ka₀)) r^{3α}/√(log r)`
  have h2 := h1.mul (hm.pow 3)
  refine (h2.congr_left ?_).congr_right ?_
  · filter_upwards [hev] with r hr
    have hmr := hm0 r ((le_max_left _ _).trans hr)
    simp only [Pi.mul_apply, Pi.pow_apply]
    field_simp
  · filter_upwards [hev, eventually_gt_atTop 0] with r hr hr0
    have hlr : 0 < Real.log r := Real.log_pos (by linarith [le_max_right r₀ 3])
    simp only [Pi.mul_apply, Pi.pow_apply]
    have hpow : (r ^ α) ^ 3 = r ^ (3 * α) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hr0.le]
      congr 1
      push_cast
      ring
    have hY : 0 < 6 * K * a₀ / ν := by positivity
    have hsq : Real.sqrt (6 * K * a₀ * c ^ 4 * Real.log r / ν) =
        c ^ 2 * Real.sqrt (6 * K * a₀ / ν) * Real.sqrt (Real.log r) := by
      rw [show 6 * K * a₀ * c ^ 4 * Real.log r / ν = (c ^ 2) ^ 2 * ((6 * K * a₀ / ν) *
        Real.log r) by ring, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity),
        Real.sqrt_mul hY.le]
      ring
    have hinv : Real.sqrt (ν / (6 * K * a₀)) = (Real.sqrt (6 * K * a₀ / ν))⁻¹ := by
      rw [← Real.sqrt_inv, inv_div]
    rw [Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow, hsq, mul_pow, hpow, hinv]
    have : 0 < Real.sqrt (6 * K * a₀ / ν) := Real.sqrt_pos.2 hY
    have : 0 < Real.sqrt (Real.log r) := Real.sqrt_pos.2 hlr
    field_simp

/-- **Non-vacuity witness for `op8f_asymptotics`.** Take `α = a₀ = c = ν = K = 1` and `r₀ = 2`, with
`m(r) = r`, `a(r) = r^{-2}`, `b(r) = r³`, `e₁ = 0`, `ε = 0`, `f(r) = r³/√(6 log r)` and
`e₂(r) = 1/(6 log r)`. Every hypothesis holds, and the theorem gives `f/m³ ~ (6 log r)^{-1/2}`,
which is exact. -/
example : ((fun r : ℝ => (r ^ 3 / Real.sqrt (6 * Real.log r)) / r ^ 3) ~[atTop]
      fun r => (6 * 1 * 1 * 1 ^ 4 * Real.log r / 1) ^ (-(1 / 2 : ℝ))) ∧
    (fun r : ℝ => r ^ 3 / Real.sqrt (6 * Real.log r)) ~[atTop]
      fun r => 1 * Real.sqrt (1 / (6 * 1 * 1)) * r ^ (3 * (1 : ℝ)) / Real.sqrt (Real.log r) := by
  have hlog : ∀ r : ℝ, 2 ≤ r → 0 < Real.log r := fun r hr => Real.log_pos (by linarith)
  have hS : ∀ r : ℝ, 2 ≤ r → 0 < Real.sqrt (6 * Real.log r) := fun r hr =>
    Real.sqrt_pos.2 (by have := hlog r hr; positivity)
  have hfd : ∀ r : ℝ, 2 ≤ r → HasDerivAt (fun r : ℝ => r ^ 3 / Real.sqrt (6 * Real.log r))
      (3 * (1 * r ^ (-1 - 1 : ℝ)) * r * (r ^ 3 / Real.sqrt (6 * Real.log r)) *
        (1 - 1 / (6 * Real.log r))) r := by
    intro r hr
    have hr0 : r ≠ 0 := by linarith
    have hl := hlog r hr
    have hs := hS r hr
    have h1 : HasDerivAt (fun r : ℝ => 6 * Real.log r) (6 * r⁻¹) r :=
      (Real.hasDerivAt_log hr0).const_mul 6
    have h2 := h1.sqrt (by positivity)
    have h3 := (hasDerivAt_pow 3 r).div h2 hs.ne'
    convert h3 using 1
    have hsq : Real.sqrt (6 * Real.log r) ^ 2 = 6 * Real.log r := Real.sq_sqrt (by positivity)
    rw [show (-1 - 1 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg (by linarith),
      Real.rpow_natCast]
    field_simp
    rw [hsq]
    ring
  have hf0 : ∀ r : ℝ, 2 ≤ r → 0 < r ^ 3 / Real.sqrt (6 * Real.log r) := fun r hr => by
    have := hS r hr
    have : 0 < r := by linarith
    positivity
  have := op8f_asymptotics (α := 1) (a₀ := 1) (c := 1) (ν := 1) (K := 1) (r₀ := 2)
    (m := fun r => r) (f := fun r => r ^ 3 / Real.sqrt (6 * Real.log r))
    (a := fun r => 1 * r ^ (-1 - 1 : ℝ)) (b := fun r => 1 * r ^ (3 * 1 : ℝ))
    (e₁ := fun _ => 0) (e₂ := fun r => 1 / (6 * Real.log r)) (ε := fun _ => 0)
    one_pos one_pos one_pos one_pos (by norm_num) (fun r hr => by linarith) hf0
    (fun R _ => LipschitzWith.id.lipschitzOnWith.absolutelyContinuousOnInterval)
    (fun R hR => by
      refine ContDiffOn.absolutelyContinuousOnInterval fun r hr => ?_
      rw [uIcc_of_le hR] at hr
      have hr0 : r ≠ 0 := by linarith [hr.1]
      have hl := hlog r hr.1
      refine ContDiffAt.contDiffWithinAt ?_
      refine (contDiffAt_id.pow 3).div ?_ (hS r hr.1).ne'
      exact ((contDiffAt_const.mul (Real.contDiffAt_log.2 hr0))).sqrt (by positivity))
    (fun r hr => by
      have : 0 < r := by linarith
      positivity)
    ((IsEquivalent.refl).congr_right (Eventually.of_forall fun r => by simp))
    IsEquivalent.refl IsEquivalent.refl
    (Eventually.of_forall fun r hr => by
      have hr0 : 0 < r := by linarith
      change deriv (fun r : ℝ => r) r = 1 * r ^ (-1 - 1 : ℝ) * r ^ 2 * (1 - 0)
      rw [deriv_id'', show (-1 - 1 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hr0.le,
        Real.rpow_natCast, sub_zero]
      field_simp)
    (Eventually.of_forall fun r hr => (hfd r hr).deriv)
    (Eventually.of_forall fun r hr => by
      have hr0 : 0 < r := by linarith
      have hl := hlog r hr
      have hsq : Real.sqrt (6 * Real.log r) ^ 2 = 6 * Real.log r := Real.sq_sqrt (by positivity)
      simp only [sub_zero, add_zero, one_mul, mul_one]
      rw [div_pow, hsq, show (3 : ℝ) = (3 : ℕ) by norm_num, Real.rpow_natCast]
      field_simp)
    tendsto_const_nhds
  exact this

end PercLib.Analysis
