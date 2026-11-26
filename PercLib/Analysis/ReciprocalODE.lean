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
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import PercLib.Meta.Tag

/-!
# Reciprocal differential inequalities, truncated means and a logarithmic upgrade

Absolute continuity is mathlib's `AbsolutelyContinuousOnInterval`, and derivatives are
`deriv` almost everywhere. The fundamental theorem of calculus is
`AbsolutelyContinuousOnInterval.integral_deriv_eq_sub`.

1. **OP4X** (`le_of_deriv_le_mul_sq`, `rpow_div_le_of_deriv_le_mul_sq`). If `T > 0` is
   absolutely continuous on `[r₀, R]` and `T' ≤ a T²` a.e. with `a ≥ 0` integrable, then
   `T(ℓ) ≥ (1/T(R) + ∫_ℓ^R a)⁻¹`. The power-law form follows.
2. **Merge inequality** (`mul_min_add_sub_min_le`).
   `a (min (a + b) m - min a m) ≤ min a m · min b m` for `a, b, m ≥ 0`.
3. **J5R6** (`integral_id_twoPoint`, `integral_sq_twoPoint`, `tendsto_truncated_ratio`,
   `truncated_ratio_iterated_limit`). This is the two-point law `X_r = r^κ` with probability
   `p_r = r^{α-κ}`, `X_r = r^α` otherwise.
4. **TJXV** (`exists_pos_le_of_log_deriv`). A locally absolutely continuous `W` with
   `W(r) ≥ c/√(log r)` and `W' ≥ -C/(r (log r)²)` a.e. is eventually bounded below by a
   positive constant.

No definition is introduced.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Real intervalIntegral
open scoped Topology ENNReal

namespace PercLib.Analysis

/-! ### 1. OP4X -/

/-- **Reciprocal ODE lower bound.** Let `T > 0` be absolutely continuous on `[r₀, R]`, `a ≥ 0`
integrable there and `T' ≤ a T²` a.e. Then `T(ℓ) ≥ (1/T(R) + ∫_ℓ^R a)⁻¹` for `r₀ ≤ ℓ ≤ R`. -/
theorem le_of_deriv_le_mul_sq {T a : ℝ → ℝ} {r₀ R : ℝ}
    (hT : AbsolutelyContinuousOnInterval T r₀ R) (hpos : ∀ s ∈ Icc r₀ R, 0 < T s)
    (ha : IntervalIntegrable a volume r₀ R) (ha0 : ∀ s ∈ Icc r₀ R, 0 ≤ a s)
    (hder : ∀ᵐ s, s ∈ Icc r₀ R → deriv T s ≤ a s * T s ^ 2) {ℓ : ℝ} (hℓ : ℓ ∈ Icc r₀ R) :
    (1 / T R + ∫ s in ℓ..R, a s)⁻¹ ≤ T ℓ := by
  have hrR : r₀ ≤ R := hℓ.1.trans hℓ.2
  have hsub : uIcc ℓ R ⊆ uIcc r₀ R := by
    rw [uIcc_of_le hℓ.2, uIcc_of_le hrR]
    exact Icc_subset_Icc hℓ.1 le_rfl
  have hTℓ : AbsolutelyContinuousOnInterval T ℓ R := hT.mono hsub
  -- a positive lower bound for `T`
  obtain ⟨x₀, hx₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hrR)
    (by simpa [uIcc_of_le hrR] using hT.continuousOn)
  set m := T x₀
  have hm : 0 < m := hpos x₀ hx₀
  have hmaps : MapsTo T (uIcc ℓ R) (Ici m) := fun s hs => by
    rw [uIcc_of_le hℓ.2] at hs
    exact hmin ⟨hℓ.1.trans hs.1, hs.2⟩
  have hU : AbsolutelyContinuousOnInterval (fun s => (T s)⁻¹) ℓ R :=
    (lipschitzOnWith_inv_Ici hm).comp_absolutelyContinuousOnInterval hmaps hTℓ
  -- the derivative of `1/T`
  have hderU : ∀ᵐ s, s ∈ Icc ℓ R → -a s ≤ deriv (fun s => (T s)⁻¹) s := by
    filter_upwards [hTℓ.ae_differentiableAt, hder] with s hd hs hsI
    have hsI' : s ∈ Icc r₀ R := ⟨hℓ.1.trans hsI.1, hsI.2⟩
    have hd' := (hd (by rwa [uIcc_of_le hℓ.2])).hasDerivAt
    have hT0 := hpos s hsI'
    have h2 : HasDerivAt (fun s => (T s)⁻¹) (-(deriv T s) / (T s) ^ 2) s := hd'.inv hT0.ne'
    rw [h2.deriv]
    have := hs hsI'
    rw [neg_le, neg_div, neg_neg, div_le_iff₀ (by positivity)]
    exact this
  have hint := integral_le_sub_of_ae_le_deriv hℓ.2 hU (ha.mono_set hsub).neg hderU
  simp only [Pi.neg_apply, intervalIntegral.integral_neg] at hint
  have hTR := hpos R ⟨hrR, le_rfl⟩
  have hTl := hpos ℓ hℓ
  have hia : 0 ≤ ∫ s in ℓ..R, a s :=
    integral_nonneg hℓ.2 fun s hs => ha0 s ⟨hℓ.1.trans hs.1, hs.2⟩
  rw [inv_le_comm₀ (by positivity) hTl, one_div]
  linarith

/-- **Power-law form.** If moreover `0 < r₀`, `α, A, ε > 0`, `a(s) ≤ A s^{-α-1}` on
`[r₀, R]` and `T(R) ≥ ε R^α`, then
`T(ℓ) ≥ ℓ^α / (A/α + (ε⁻¹ - A/α)(ℓ/R)^α)`. -/
theorem rpow_div_le_of_deriv_le_mul_sq {T a : ℝ → ℝ} {r₀ R : ℝ} (hr₀ : 0 < r₀)
    (hT : AbsolutelyContinuousOnInterval T r₀ R) (hpos : ∀ s ∈ Icc r₀ R, 0 < T s)
    (ha : IntervalIntegrable a volume r₀ R) (ha0 : ∀ s ∈ Icc r₀ R, 0 ≤ a s)
    (hder : ∀ᵐ s, s ∈ Icc r₀ R → deriv T s ≤ a s * T s ^ 2) {α A ε : ℝ} (hα : 0 < α)
    (hA : 0 < A) (hε : 0 < ε) (haA : ∀ s ∈ Icc r₀ R, a s ≤ A * s ^ (-α - 1))
    (hTR : ε * R ^ α ≤ T R) {ℓ : ℝ} (hℓ : ℓ ∈ Icc r₀ R) :
    ℓ ^ α / (A / α + (ε⁻¹ - A / α) * (ℓ / R) ^ α) ≤ T ℓ := by
  have hrR : r₀ ≤ R := hℓ.1.trans hℓ.2
  have hℓ0 : 0 < ℓ := hr₀.trans_le hℓ.1
  have hR0 : 0 < R := hℓ0.trans_le hℓ.2
  have hsub : uIcc ℓ R ⊆ uIcc r₀ R := by
    rw [uIcc_of_le hℓ.2, uIcc_of_le hrR]
    exact Icc_subset_Icc hℓ.1 le_rfl
  have hmain := le_of_deriv_le_mul_sq hT hpos ha ha0 hder hℓ
  -- `∫_ℓ^R a ≤ (A/α)(ℓ^{-α} - R^{-α})`
  have h0 : (0 : ℝ) ∉ uIcc ℓ R := by
    rw [uIcc_of_le hℓ.2]
    exact fun h => (lt_irrefl 0) (hℓ0.trans_le h.1)
  have hpow : ∫ s in ℓ..R, A * s ^ (-α - 1) = A / α * (ℓ ^ (-α) - R ^ (-α)) := by
    rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inr ⟨by linarith, h0⟩)]
    have : -α - 1 + 1 = -α := by ring
    rw [this]
    field_simp
    ring
  have hint : ∫ s in ℓ..R, a s ≤ A / α * (ℓ ^ (-α) - R ^ (-α)) := by
    rw [← hpow]
    refine integral_mono_on hℓ.2 (ha.mono_set hsub) ?_ fun s hs =>
      haA s ⟨hℓ.1.trans hs.1, hs.2⟩
    refine (ContinuousOn.intervalIntegrable ?_)
    refine continuousOn_const.mul (ContinuousOn.rpow_const continuousOn_id fun s hs => ?_)
    left
    rw [uIcc_of_le hℓ.2] at hs
    exact (hℓ0.trans_le hs.1).ne'
  -- `1/T(R) ≤ ε⁻¹ R^{-α}`
  have hTR' : 1 / T R ≤ ε⁻¹ * R ^ (-α) := by
    have hTRpos := hpos R ⟨hrR, le_rfl⟩
    rw [rpow_neg hR0.le, div_le_iff₀ hTRpos]
    have : ε⁻¹ * (R ^ α)⁻¹ * (ε * R ^ α) = 1 := by
      field_simp
    nlinarith [mul_le_mul_of_nonneg_left hTR (by positivity : 0 ≤ ε⁻¹ * (R ^ α)⁻¹)]
  -- assembling
  have hq : (ℓ / R) ^ α = ℓ ^ α * R ^ (-α) := by
    rw [div_rpow hℓ0.le hR0.le, rpow_neg hR0.le, div_eq_mul_inv]
  have hD : 0 < A / α + (ε⁻¹ - A / α) * (ℓ / R) ^ α := by
    have hq0 : 0 < (ℓ / R) ^ α := rpow_pos_of_pos (div_pos hℓ0 hR0) _
    have hq1 : (ℓ / R) ^ α ≤ 1 := rpow_le_one (div_pos hℓ0 hR0).le
      ((div_le_one hR0).2 hℓ.2) hα.le
    have : A / α + (ε⁻¹ - A / α) * (ℓ / R) ^ α =
        A / α * (1 - (ℓ / R) ^ α) + ε⁻¹ * (ℓ / R) ^ α := by ring
    rw [this]
    have := div_pos hA hα
    have := inv_pos.2 hε
    nlinarith
  have hS : 1 / T R + ∫ s in ℓ..R, a s ≤
      (A / α + (ε⁻¹ - A / α) * (ℓ / R) ^ α) / ℓ ^ α := by
    have hl : ℓ ^ (-α) = (ℓ ^ α)⁻¹ := rpow_neg hℓ0.le _
    have hlα : 0 < ℓ ^ α := rpow_pos_of_pos hℓ0 _
    have e : (A / α + (ε⁻¹ - A / α) * (ℓ / R) ^ α) / ℓ ^ α =
        ε⁻¹ * R ^ (-α) + A / α * (ℓ ^ (-α) - R ^ (-α)) := by
      rw [hq, hl]
      field_simp
      ring
    rw [e]
    linarith
  have hpos' : 0 < 1 / T R + ∫ s in ℓ..R, a s := by
    have := hpos R ⟨hrR, le_rfl⟩
    have : 0 ≤ ∫ s in ℓ..R, a s :=
      integral_nonneg hℓ.2 fun s hs => ha0 s ⟨hℓ.1.trans hs.1, hs.2⟩
    positivity
  calc ℓ ^ α / (A / α + (ε⁻¹ - A / α) * (ℓ / R) ^ α)
      = ((A / α + (ε⁻¹ - A / α) * (ℓ / R) ^ α) / ℓ ^ α)⁻¹ := by rw [inv_div]
    _ ≤ (1 / T R + ∫ s in ℓ..R, a s)⁻¹ := inv_anti₀ hpos' hS
    _ ≤ T ℓ := hmain

/-! ### 2. The merge inequality -/

/-- **Merge inequality.** `a (min (a + b) m - min a m) ≤ min a m · min b m` for
`a, b, m ≥ 0`. -/
theorem mul_min_add_sub_min_le {a b m : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hm : 0 ≤ m) :
    a * (min (a + b) m - min a m) ≤ min a m * min b m := by
  rcases le_total a m with ham | ham
  · rw [min_eq_left ham]
    rcases le_total (a + b) m with habm | habm
    · rw [min_eq_left habm, min_eq_left (by linarith : b ≤ m)]
      nlinarith
    · rw [min_eq_right habm]
      rcases le_total b m with hbm | hbm
      · rw [min_eq_left hbm]
        nlinarith
      · rw [min_eq_right hbm]
        nlinarith
  · rw [min_eq_right ham, min_eq_right (by linarith : m ≤ a + b), sub_self, mul_zero]
    exact mul_nonneg hm (le_min hb hm)

/-! ### 3. J5R6: a two-point law -/

/-- The integral against `c₁ δ_{x₁} + c₂ δ_{x₂}`. -/
theorem integral_twoPoint_dirac (f : ℝ → ℝ) {c₁ c₂ : ℝ} (h1 : 0 ≤ c₁) (h2 : 0 ≤ c₂) (x₁ x₂ : ℝ) :
    ∫ x, f x ∂(ENNReal.ofReal c₁ • Measure.dirac x₁ + ENNReal.ofReal c₂ • Measure.dirac x₂) =
      c₁ * f x₁ + c₂ * f x₂ := by
  rw [integral_add_measure ((integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top)
      ((integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top),
    MeasureTheory.integral_smul_measure, MeasureTheory.integral_smul_measure, integral_dirac,
    integral_dirac,
    ENNReal.toReal_ofReal h1, ENNReal.toReal_ofReal h2, smul_eq_mul, smul_eq_mul]

variable {α κ : ℝ}

theorem twoPoint_prob_mem {r : ℝ} (hr : 1 ≤ r) (hακ : α < κ) :
    0 < r ^ (α - κ) ∧ r ^ (α - κ) ≤ 1 :=
  ⟨rpow_pos_of_pos (by linarith) _, rpow_le_one_of_one_le_of_nonpos hr (by linarith)⟩

theorem twoPoint_mul {r : ℝ} (hr : 1 ≤ r) : r ^ (α - κ) * r ^ κ = r ^ α := by
  rw [← rpow_add (by linarith)]
  ring_nf

/-- **Mean.** `E X_r = (2 - p_r) r^α`. -/
theorem integral_id_twoPoint {r : ℝ} (hr : 1 ≤ r) (hακ : α < κ) :
    ∫ x, x ∂(ENNReal.ofReal (r ^ (α - κ)) • Measure.dirac (r ^ κ) +
      ENNReal.ofReal (1 - r ^ (α - κ)) • Measure.dirac (r ^ α)) = (2 - r ^ (α - κ)) * r ^ α := by
  obtain ⟨hp0, hp1⟩ := twoPoint_prob_mem hr hακ
  rw [integral_twoPoint_dirac (fun x => x) hp0.le (by linarith), twoPoint_mul hr]
  ring

/-- **Second moment.** `E X_r² = r^{α+κ} + (1 - p_r) r^{2α}`. -/
theorem integral_sq_twoPoint {r : ℝ} (hr : 1 ≤ r) (hακ : α < κ) :
    ∫ x, x ^ 2 ∂(ENNReal.ofReal (r ^ (α - κ)) • Measure.dirac (r ^ κ) +
      ENNReal.ofReal (1 - r ^ (α - κ)) • Measure.dirac (r ^ α)) =
        r ^ (α + κ) + (1 - r ^ (α - κ)) * r ^ (2 * α) := by
  obtain ⟨hp0, hp1⟩ := twoPoint_prob_mem hr hακ
  have hr0 : 0 < r := by linarith
  rw [integral_twoPoint_dirac (fun x => x ^ 2) hp0.le (by linarith)]
  rw [← rpow_natCast, ← rpow_natCast, ← rpow_mul hr0.le, ← rpow_mul hr0.le,
    ← rpow_add hr0, Nat.cast_ofNat]
  congr 1
  · ring_nf
  · ring_nf

/-- **Truncated mean.** For `0 < δ ≤ 1`,
`E min(X_r, δ r^κ) / E X_r → (1 + δ)/2` as `r → ∞`. -/
theorem tendsto_truncated_ratio (hακ : α < κ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    Tendsto (fun r : ℝ => (∫ x, min x (δ * r ^ κ) ∂(ENNReal.ofReal (r ^ (α - κ)) •
        Measure.dirac (r ^ κ) + ENNReal.ofReal (1 - r ^ (α - κ)) • Measure.dirac (r ^ α))) /
      ∫ x, x ∂(ENNReal.ofReal (r ^ (α - κ)) • Measure.dirac (r ^ κ) +
        ENNReal.ofReal (1 - r ^ (α - κ)) • Measure.dirac (r ^ α))) atTop (𝓝 ((1 + δ) / 2)) := by
  have hp : Tendsto (fun r : ℝ => r ^ (α - κ)) atTop (𝓝 0) := by
    have := tendsto_rpow_neg_atTop (y := κ - α) (by linarith)
    simpa [neg_sub] using this
  have hlim : Tendsto (fun r : ℝ => (1 + δ - r ^ (α - κ)) / (2 - r ^ (α - κ))) atTop
      (𝓝 ((1 + δ) / 2)) := by
    have h := ((tendsto_const_nhds (x := 1 + δ)).sub hp).div
      ((tendsto_const_nhds (x := (2 : ℝ))).sub hp) (by norm_num)
    rw [sub_zero, sub_zero] at h
    exact h
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1, hp.eventually (gt_mem_nhds hδ)] with r hr hpδ
  obtain ⟨hp0, hp1⟩ := twoPoint_prob_mem hr hακ
  have hr0 : 0 < r := by linarith
  have hrk : 0 < r ^ κ := rpow_pos_of_pos hr0 _
  have hra : 0 < r ^ α := rpow_pos_of_pos hr0 _
  have hmul := twoPoint_mul (α := α) (κ := κ) hr
  rw [integral_id_twoPoint hr hακ, integral_twoPoint_dirac (fun x => min x (δ * r ^ κ)) hp0.le
    (by linarith)]
  rw [min_eq_right (by nlinarith), min_eq_left (by nlinarith)]
  have h2 : 2 - r ^ (α - κ) ≠ 0 := by linarith
  field_simp
  rw [← hmul]
  ring

/-- **Iterated limit.** `lim_{δ ↓ 0} lim_{r → ∞} E min(X_r, δ r^κ)/E X_r = 1/2`, in the
form: for every `ε > 0` there is `δ₀ > 0` such that for `0 < δ < δ₀`, eventually in `r` the
ratio is within `ε` of `1/2`. -/
theorem truncated_ratio_iterated_limit (hακ : α < κ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ₀ > 0, ∀ δ, 0 < δ → δ < δ₀ → ∀ᶠ r : ℝ in atTop,
      |(∫ x, min x (δ * r ^ κ) ∂(ENNReal.ofReal (r ^ (α - κ)) • Measure.dirac (r ^ κ) +
          ENNReal.ofReal (1 - r ^ (α - κ)) • Measure.dirac (r ^ α))) /
        (∫ x, x ∂(ENNReal.ofReal (r ^ (α - κ)) • Measure.dirac (r ^ κ) +
          ENNReal.ofReal (1 - r ^ (α - κ)) • Measure.dirac (r ^ α))) - 1 / 2| < ε := by
  refine ⟨min ε 1, lt_min hε one_pos, fun δ hδ hδ0 => ?_⟩
  have hδ1 : δ ≤ 1 := (hδ0.trans_le (min_le_right _ _)).le
  have hlim := tendsto_truncated_ratio hακ hδ hδ1
  have hball : |(1 + δ) / 2 - 1 / 2| < ε := by
    rw [abs_lt]
    constructor <;> linarith [min_le_left ε 1]
  have hopen : IsOpen {y : ℝ | |y - 1 / 2| < ε} :=
    isOpen_lt (continuous_abs.comp (continuous_id.sub continuous_const)) continuous_const
  exact hlim.eventually (hopen.mem_nhds hball)

/-! ### 4. TJXV -/

/-- `∫_r^s -C/(t (log t)²) dt = C (1/log s - 1/log r)` for `1 < r ≤ s`. -/
theorem integral_neg_div_mul_log_sq {r s C : ℝ} (hr : 1 < r) (hrs : r ≤ s) :
    ∫ t in r..s, -C / (t * Real.log t ^ 2) = C / Real.log s - C / Real.log r := by
  have hpos : ∀ t ∈ uIcc r s, 1 < t := fun t ht => by
    rw [uIcc_of_le hrs] at ht
    exact hr.trans_le ht.1
  refine integral_eq_sub_of_hasDerivAt (f := fun t => C / Real.log t) (fun t ht => ?_) ?_
  · have ht1 := hpos t ht
    have ht0 : t ≠ 0 := by linarith
    have hl : Real.log t ≠ 0 := (Real.log_pos ht1).ne'
    have := ((Real.hasDerivAt_log ht0).inv hl).const_mul C
    convert this using 1
    · funext x
      simp [div_eq_mul_inv]
    · field_simp
  · refine ContinuousOn.intervalIntegrable fun t ht => ?_
    have ht1 := hpos t ht
    have hl : Real.log t ≠ 0 := (Real.log_pos ht1).ne'
    refine ContinuousAt.continuousWithinAt ?_
    refine continuousAt_const.div (continuousAt_id.mul ((continuousAt_log (by linarith)).pow 2))
      (mul_ne_zero (by linarith) (pow_ne_zero 2 hl))

/-- **TJXV.** Let `R₀ > 1` and `c > 0`. Suppose `W` is absolutely continuous on every
`[R₀, R]`, `W(r) ≥ c/√(log r)` and `W'(r) ≥ -C/(r (log r)²)` for almost every `r ≥ R₀`.
Then `W` is eventually bounded below by a positive constant. -/
@[tag "TJXV"]
theorem exists_pos_le_of_log_deriv {W : ℝ → ℝ} {R₀ c C : ℝ} (hR₀ : 1 < R₀) (hc : 0 < c)
    (hW : ∀ R, R₀ ≤ R → AbsolutelyContinuousOnInterval W R₀ R)
    (hlow : ∀ r, R₀ ≤ r → c / Real.sqrt (Real.log r) ≤ W r)
    (hder : ∀ᵐ r, R₀ ≤ r → -C / (r * Real.log r ^ 2) ≤ deriv W r) :
    ∃ η > 0, ∃ R, ∀ r, R ≤ r → η ≤ W r := by
  set C' := max C 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  -- choose `r*` with `√(log r*) ≥ 2C'/c`
  set rs := max R₀ (Real.exp ((2 * C' / c) ^ 2 + 1)) with hrs
  have hrsR : R₀ ≤ rs := le_max_left _ _
  have hrs1 : 1 < rs := hR₀.trans_le hrsR
  set L := Real.log rs with hL
  have hL0 : 0 < L := Real.log_pos hrs1
  have hLbig : (2 * C' / c) ^ 2 + 1 ≤ L := by
    rw [hL, Real.le_log_iff_exp_le (by linarith)]
    exact le_max_right _ _
  have hsL : 2 * C' / c ≤ Real.sqrt L :=
    calc 2 * C' / c = Real.sqrt ((2 * C' / c) ^ 2) := (Real.sqrt_sq (by positivity)).symm
      _ ≤ Real.sqrt L := Real.sqrt_le_sqrt (by linarith)
  have hsL0 : 0 < Real.sqrt L := Real.sqrt_pos.2 hL0
  refine ⟨c / (2 * Real.sqrt L), by positivity, rs, fun s hs => ?_⟩
  -- `W(s) ≥ W(r*) - C'/log r*`
  have hR₀s : R₀ ≤ s := hrsR.trans hs
  have hac : AbsolutelyContinuousOnInterval W rs s := (hW s hR₀s).mono (by
    rw [uIcc_of_le hR₀s, uIcc_of_le hs]
    exact Icc_subset_Icc hrsR le_rfl)
  have hint := integral_le_sub_of_ae_le_deriv hs hac (g := fun t => -C' / (t * Real.log t ^ 2))
    ?_ ?_
  · rw [integral_neg_div_mul_log_sq hrs1 hs] at hint
    have hls : 0 < Real.log s := Real.log_pos (hrs1.trans_le hs)
    have h1 : 0 ≤ C' / Real.log s := div_nonneg hC'0 hls.le
    have hWr := hlow rs hrsR
    rw [← hL] at hint hWr
    -- `c/√L - C'/L ≥ c/(2√L)`
    have hkey : c / (2 * Real.sqrt L) ≤ c / Real.sqrt L - C' / L := by
      have hLL : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt hL0.le
      have h2C : 2 * C' ≤ c * Real.sqrt L := by
        have := (div_le_iff₀ hc).1 hsL
        linarith
      have h2 : C' / L ≤ c / (2 * Real.sqrt L) := by
        rw [div_le_div_iff₀ hL0 (by positivity)]
        nlinarith [mul_le_mul_of_nonneg_right h2C hsL0.le, hLL]
      have h3 : c / Real.sqrt L = c / (2 * Real.sqrt L) + c / (2 * Real.sqrt L) := by
        field_simp
        ring
      linarith
    linarith
  · refine ContinuousOn.intervalIntegrable fun t ht => ?_
    rw [uIcc_of_le hs] at ht
    have ht1 : 1 < t := hrs1.trans_le ht.1
    have hl : Real.log t ≠ 0 := (Real.log_pos ht1).ne'
    have ht0 : t ≠ 0 := by linarith
    exact (continuousAt_const.div (continuousAt_id.mul ((continuousAt_log ht0).pow 2))
      (mul_ne_zero ht0 (pow_ne_zero 2 hl))).continuousWithinAt
  · filter_upwards [hder] with t ht htI
    have ht1 : 1 < t := hrs1.trans_le htI.1
    refine le_trans ?_ (ht (hrsR.trans htI.1))
    have hden : 0 < t * Real.log t ^ 2 := by
      have := Real.log_pos ht1
      positivity
    exact div_le_div_of_nonneg_right (by linarith [le_max_left C 0]) hden.le

/-! ### Non-vacuity -/

/-- `W ≡ 1` satisfies the hypotheses of `exists_pos_le_of_log_deriv` with `R₀ = e`, `c = 1`,
`C = 0`. -/
example : ∃ η > 0, ∃ R, ∀ r, R ≤ r → η ≤ (fun _ : ℝ => (1 : ℝ)) r := by
  refine exists_pos_le_of_log_deriv (R₀ := Real.exp 1) (c := 1) (C := 0)
    (Real.one_lt_exp_iff.2 one_pos) one_pos
    (fun R _ => (LipschitzWith.const (1 : ℝ)).lipschitzOnWith.absolutelyContinuousOnInterval)
    (fun r hr => ?_) (Eventually.of_forall fun r _ => by simp)
  have hr0 : 0 < r := lt_of_lt_of_le (Real.exp_pos 1) hr
  have h1 : 1 ≤ Real.log r := (Real.le_log_iff_exp_le hr0).2 hr
  rw [div_le_one (Real.sqrt_pos.2 (by linarith))]
  exact Real.one_le_sqrt.2 h1

/-- `T(s) = s^α/(A/α)` and `a(s) = A s^{-α-1}` on `[r₀, R]`, `0 < r₀`, satisfy `T' = a T²` and
`T(R) = (α/A) R^α`. `le_of_deriv_le_mul_sq` then holds with equality, `T(ℓ) ≥ ℓ^α/(A/α)`. -/
example {α A r₀ R : ℝ} (hα : 0 < α) (hA : 0 < A) (hr₀ : 0 < r₀) {ℓ : ℝ}
    (hℓ : ℓ ∈ Icc r₀ R) :
    ℓ ^ α / (A / α + ((α / A)⁻¹ - A / α) * (ℓ / R) ^ α) ≤ ℓ ^ α / (A / α) := by
  have hrR : r₀ ≤ R := hℓ.1.trans hℓ.2
  have hpos' : ∀ s ∈ uIcc r₀ R, 0 < s := fun s hs => by
    rw [uIcc_of_le hrR] at hs
    exact hr₀.trans_le hs.1
  refine rpow_div_le_of_deriv_le_mul_sq (T := fun s => s ^ α / (A / α))
    (a := fun s => A * s ^ (-α - 1)) hr₀ ?_ (fun s hs => by
      have := hr₀.trans_le hs.1
      positivity) ?_ (fun s hs => by
      have := hr₀.trans_le hs.1
      positivity) ?_ hα hA (div_pos hα hA) (fun s _ => le_rfl) ?_ hℓ
  · refine ContDiffOn.absolutelyContinuousOnInterval ?_
    refine ContDiffOn.div_const (fun s hs => ?_) _
    exact (Real.contDiffAt_rpow_const_of_ne (hpos' s hs).ne').contDiffWithinAt
  · refine ContinuousOn.intervalIntegrable ?_
    exact continuousOn_const.mul (ContinuousOn.rpow_const continuousOn_id fun s hs =>
      Or.inl (hpos' s hs).ne')
  · refine Eventually.of_forall fun s hs => le_of_eq ?_
    have hs0 : 0 < s := hr₀.trans_le hs.1
    have hd := ((Real.hasDerivAt_rpow_const (p := α) (Or.inl hs0.ne')).div_const (A / α))
    rw [hd.deriv]
    have e1 : s ^ (-α - 1) * (s ^ α) ^ 2 = s ^ (α - 1) := by
      rw [← rpow_natCast, ← rpow_mul hs0.le, ← rpow_add hs0]
      congr 1
      push_cast
      ring
    field_simp
    exact e1.symm
  · apply le_of_eq
    field_simp

end PercLib.Analysis
