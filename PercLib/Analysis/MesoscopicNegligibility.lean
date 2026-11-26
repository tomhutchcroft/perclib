/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-16: truncated moment inequalities force mesoscopic negligibility
(wiki mesoscopic-tail-transfer, tag KKGL, with the conclusion QMN5 written out). No upstream proof
is copied, no definition is added and no Input is introduced.
-/
module

public import PercLib.Analysis.Elementary
public import PercLib.Analysis.GoodScales
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.Order.LiminfLimsup

/-! # Truncated moment inequalities force mesoscopic negligibility

* `one_div_sub_one_div_le_integral`: if `f > 0` is absolutely continuous on `[s,t]`, `a ≥ 0`
  is integrable there and `f' ≤ a f²` almost everywhere, then `1/f(s) - 1/f(t) ≤ ∫_s^t a`.
* `exists_truncation_lt` (the analytic core of KKGL): under the two differential inequalities,
  for every `ε > 0` there are `δ > 0` and `R₀` with `T_{δ R^κ}(R) < ε R^α` for `R ≥ R₀`.
* `tendsto_limsup_truncatedMean_div_mean` (KKGL, conclusion QMN5): for laws `μ_r` with
  `m₁(r) ≥ c₁ r^α`, `b r^{α+κ} ≤ m₂(r) ≤ B r^{α+κ}` and `T_m(r) = ∫ min x m dμ_r`,
  `lim_{δ↓0} limsup_{r→∞} T_{δ r^κ}(r) / m₁(r) = 0`.

The proof follows the wiki. If `T_m(R) ≥ ε R^α` with `m = δ R^κ`, the reciprocal estimate
gives `T_m(t) ≥ D t^α` on `[qR, λR]`, so `(log m₂)' ≥ μ/t` there with `μ > α + κ`. The
interval bound DISO (`div_le_of_logDeriv_ge`) then bounds `λ/q`, contradicting the choice of
`q`.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set Real Filter Topology Asymptotics

namespace PercLib.Analysis

/-- **Reciprocal integration.** If `f > 0` is absolutely continuous on `[s,t]`, `a ≥ 0` is
integrable there and `f' ≤ a f²` almost everywhere on `[s,t]`, then
`1/f(s) - 1/f(t) ≤ ∫_s^t a`. -/
theorem one_div_sub_one_div_le_integral {f a : ℝ → ℝ} {s t : ℝ} (hst : s ≤ t)
    (hac : AbsolutelyContinuousOnInterval f s t) (hpos : ∀ u ∈ Icc s t, 0 < f u)
    (ha : IntervalIntegrable a volume s t) (ha0 : ∀ u ∈ Icc s t, 0 ≤ a u)
    (hd : ∀ᵐ u, u ∈ Icc s t → deriv f u ≤ a u * f u ^ 2) :
    1 / f s - 1 / f t ≤ ∫ u in s..t, a u := by
  have huIcc : uIcc s t = Icc s t := uIcc_of_le hst
  obtain ⟨u₀, hu₀, hmin⟩ := isCompact_uIcc.exists_isMinOn nonempty_uIcc hac.continuousOn
  have hm : 0 < f u₀ := hpos u₀ (huIcc ▸ hu₀)
  have hg : AbsolutelyContinuousOnInterval (fun u => 1 / f u) s t :=
    (by simpa only [one_div] using lipschitzOnWith_inv_Ici hm :
      LipschitzOnWith _ (fun x : ℝ => 1 / x) (Ici (f u₀))).comp_absolutelyContinuousOnInterval
      (fun u hu => (hmin hu : f u₀ ≤ f u)) hac
  have hftc := hg.integral_deriv_eq_sub
  have hmono : ∫ u in s..t, -a u ≤ ∫ u in s..t, deriv (fun u => 1 / f u) u := by
    refine intervalIntegral.integral_mono_ae_restrict hst ha.neg hg.intervalIntegrable_deriv ?_
    rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hd] with u hu hmem
    have hfu := hpos u hmem
    by_cases hdf : DifferentiableAt ℝ f u
    · have hder : deriv (fun u => 1 / f u) u = -deriv f u / f u ^ 2 := by
        have h1 := (hdf.hasDerivAt.inv hfu.ne').deriv
        have h2 : (fun u => 1 / f u) = fun u => (f u)⁻¹ := funext fun u => one_div _
        rw [h2]
        exact h1
      rw [hder, neg_div, neg_le_neg_iff, div_le_iff₀ (by positivity)]
      exact hu hmem
    · have hndf : ¬ DifferentiableAt ℝ (fun u => 1 / f u) u := by
        intro h
        apply hdf
        have h' := h.inv (by simp [hfu.ne'])
        have h3 : ((fun u => 1 / f u)⁻¹ : ℝ → ℝ) = f := funext fun u => by simp
        rwa [h3] at h'
      rw [deriv_zero_of_not_differentiableAt hndf]
      linarith [ha0 u hmem]
  rw [intervalIntegral.integral_neg, hftc] at hmono
  linarith

/-- Two-sided bounds from `a ~ a₀ r^{-α-1}`: for `0 < θ < 1`, eventually
`a₀ θ t^{-α-1} ≤ a(t) ≤ (a₀/θ) t^{-α-1}`. -/
theorem exists_bounds_of_isEquivalent {a : ℝ → ℝ} {a₀ α θ : ℝ} (ha₀ : 0 < a₀) (hθ : 0 < θ)
    (hθ1 : θ < 1) (h : a ~[atTop] fun r => a₀ * r ^ (-α - 1)) :
    ∃ r₁ > 0, ∀ t, r₁ ≤ t → a₀ * θ * t ^ (-α - 1) ≤ a t ∧ a t ≤ a₀ / θ * t ^ (-α - 1) := by
  have hv : ∀ᶠ r in atTop, (fun r : ℝ => a₀ * r ^ (-α - 1)) r ≠ 0 := by
    filter_upwards [eventually_gt_atTop 0] with r hr
    exact (mul_pos ha₀ (rpow_pos_of_pos hr _)).ne'
  have ht := (isEquivalent_iff_tendsto_one hv).1 h
  have hθ' : 1 < θ⁻¹ := one_lt_inv_iff₀.2 ⟨hθ, hθ1⟩
  have hev := ht.eventually (Ioo_mem_nhds hθ1 hθ')
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hev.and (eventually_gt_atTop 0))
  refine ⟨max N 1, by positivity, fun t ht => ?_⟩
  obtain ⟨⟨h1, h2⟩, ht0⟩ := hN t ((le_max_left _ _).trans ht)
  have hvt : 0 < a₀ * t ^ (-α - 1) := mul_pos ha₀ (rpow_pos_of_pos ht0 _)
  simp only [Pi.div_apply] at h1 h2
  rw [lt_div_iff₀ hvt] at h1
  rw [div_lt_iff₀ hvt] at h2
  constructor
  · nlinarith
  · rw [div_mul_eq_mul_div, le_div_iff₀ hθ]
    have : θ⁻¹ * (a₀ * t ^ (-α - 1)) * θ = a₀ * t ^ (-α - 1) := by field_simp
    nlinarith

/-- **Step 1 of mesoscopic negligibility.** Let `f > 0` be absolutely continuous on `[t, R]` with
`f' ≤ a f²` almost everywhere there, where `0 ≤ a(u) ≤ a₊ u^{-α-1}` on `[t,R]`. If `f(R) ≥ ε R^α`
and `t ≤ λ R`, then `f(t) ≥ D t^α` with `D = (a₊/α + λ^α/ε)⁻¹`. -/
theorem mul_rpow_le_of_reciprocal {f a : ℝ → ℝ} {α ap ε lam t R : ℝ} (hα : 0 < α)
    (hap : 0 < ap) (hε : 0 < ε) (hlam : 0 < lam) (ht0 : 0 < t) (htR : t ≤ R)
    (htlam : t ≤ lam * R) (hac : AbsolutelyContinuousOnInterval f t R)
    (hpos : ∀ u ∈ Icc t R, 0 < f u) (ha : Measurable a)
    (hbnd : ∀ u ∈ Icc t R, 0 ≤ a u ∧ a u ≤ ap * u ^ (-α - 1))
    (hd : ∀ᵐ u, u ∈ Icc t R → deriv f u ≤ a u * f u ^ 2) (hfR : ε * R ^ α ≤ f R) :
    1 / (ap / α + lam ^ α / ε) * t ^ α ≤ f t := by
  have hR0 : 0 < R := ht0.trans_le htR
  have hcont : ContinuousOn (fun u : ℝ => ap * u ^ (-α - 1)) (uIcc t R) := by
    refine continuousOn_const.mul (ContinuousOn.rpow_const continuousOn_id fun u hu => ?_)
    rw [uIcc_of_le htR] at hu
    exact Or.inl (ht0.trans_le hu.1).ne'
  have hint_up : IntervalIntegrable (fun u : ℝ => ap * u ^ (-α - 1)) volume t R :=
    hcont.intervalIntegrable
  have hint_a : IntervalIntegrable a volume t R := by
    refine hint_up.mono_fun ha.aestronglyMeasurable ?_
    rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_uIoc]
    refine Filter.Eventually.of_forall fun u hu => ?_
    rw [uIoc_of_le htR] at hu
    have := hbnd u (Ioc_subset_Icc_self hu)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg this.1,
      abs_of_nonneg (this.1.trans this.2)]
    exact this.2
  have hrec := one_div_sub_one_div_le_integral htR hac hpos hint_a (fun u hu => (hbnd u hu).1) hd
  have hupper : ∫ u in t..R, a u ≤ ∫ u in t..R, ap * u ^ (-α - 1) :=
    intervalIntegral.integral_mono_on htR hint_a hint_up fun u hu => (hbnd u hu).2
  have hcalc : ∫ u in t..R, ap * u ^ (-α - 1) = ap / α * (t ^ (-α) - R ^ (-α)) := by
    rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inr ⟨by linarith, ?_⟩)]
    · have : -α - 1 + 1 = -α := by ring
      rw [this]
      field_simp
      ring
    · rw [uIcc_of_le htR]
      intro h
      linarith [h.1]
  have htα : 0 < t ^ α := rpow_pos_of_pos ht0 α
  have hRα : 0 < R ^ α := rpow_pos_of_pos hR0 α
  have hlamα : 0 < lam ^ α := rpow_pos_of_pos hlam α
  have hTR : 1 / f R ≤ 1 / (ε * R ^ α) := one_div_le_one_div_of_le (by positivity) hfR
  have hRt : 1 / (ε * R ^ α) ≤ lam ^ α / ε / t ^ α := by
    have h2 : t ^ α ≤ (lam * R) ^ α := rpow_le_rpow ht0.le htlam hα.le
    rw [mul_rpow hlam.le hR0.le] at h2
    rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hneg : ap / α * (t ^ (-α) - R ^ (-α)) ≤ ap / α / t ^ α := by
    rw [rpow_neg ht0.le, rpow_neg hR0.le, div_eq_mul_inv (ap / α)]
    have : 0 ≤ (R ^ α)⁻¹ := by positivity
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hT : 1 / f t ≤ 1 / (1 / (ap / α + lam ^ α / ε) * t ^ α) := by
    have : 1 / (1 / (ap / α + lam ^ α / ε) * t ^ α) =
        ap / α / t ^ α + lam ^ α / ε / t ^ α := by
      field_simp
    rw [this]
    linarith
  exact (one_div_le_one_div (hpos t ⟨le_rfl, htR⟩) (by positivity)).1 hT

/-- **Step 2 of mesoscopic negligibility** (arithmetic). If `α ρ ≤ a₋ D`, `a(t) ≥ a₋ t^{-α-1}`,
`T ≥ D t^α` and the collision term is at most `(1 - ρ) T`, then
`3 α ρ² / t ≤ 3 a(t) (T - c)`. -/
theorem div_le_three_mul_of_bounds {α ρ am D t at' T c : ℝ} (hα : 0 < α) (hρ : 0 < ρ)
    (ht : 0 < t)
    (hD : 0 < D) (hamD : α * ρ ≤ am * D) (hat : am * t ^ (-α - 1) ≤ at')
    (hT : D * t ^ α ≤ T) (hc : c ≤ (1 - ρ) * T) :
    3 * α * ρ ^ 2 / t ≤ 3 * at' * (T - c) := by
  have hpow : t ^ (-α - 1) * t ^ α = 1 / t := by
    rw [← rpow_add ht, show -α - 1 + α = -1 by ring, rpow_neg_one, one_div]
  have htα : 0 < t ^ α := rpow_pos_of_pos ht α
  have hpow0 : 0 < t ^ (-α - 1) := rpow_pos_of_pos ht _
  have hbr : ρ * (D * t ^ α) ≤ T - c := by nlinarith
  have hbr0 : 0 ≤ ρ * (D * t ^ α) := by positivity
  have hamD0 : 0 < am * D := lt_of_lt_of_le (mul_pos hα hρ) hamD
  have ham : 0 < am := (pos_iff_pos_of_mul_pos hamD0).2 hD
  have hat0 : 0 ≤ at' := (mul_pos ham hpow0).le.trans hat
  calc 3 * α * ρ ^ 2 / t = 3 * ρ * (α * ρ) * (1 / t) := by ring
    _ ≤ 3 * ρ * (am * D) * (1 / t) := by gcongr
    _ = 3 * (am * t ^ (-α - 1)) * (ρ * (D * t ^ α)) := by rw [← hpow]; ring
    _ ≤ 3 * at' * (T - c) := by gcongr

/-- **Step 2 of mesoscopic negligibility** (the collision term). If `0 ≤ C`,
`δ = η D q^κ / (C + 1)`, `q R ≤ t` and `T ≥ D t^α`, then `C δ R^κ t^{α-κ} ≤ η T`. -/
theorem collision_le {C δ η D q κ α R t T : ℝ} (hC : 0 ≤ C) (hη : 0 ≤ η) (hD : 0 ≤ D)
    (hq : 0 < q)
    (hκ : 0 ≤ κ) (hR : 0 < R) (ht : 0 < t) (hqt : q * R ≤ t)
    (hδ : δ = η * D * q ^ κ / (C + 1)) (hT : D * t ^ α ≤ T) :
    C * (δ * R ^ κ) * t ^ (α - κ) ≤ η * T := by
  have htκ : 0 < t ^ κ := rpow_pos_of_pos ht κ
  have hqκ : 0 < q ^ κ := rpow_pos_of_pos hq κ
  have hqRt : q ^ κ * R ^ κ ≤ t ^ κ := by
    rw [← mul_rpow hq.le hR.le]
    exact rpow_le_rpow (by positivity) hqt hκ
  have e1 : C * (δ * R ^ κ) * t ^ (α - κ) = C * δ * (R ^ κ / t ^ κ) * t ^ α := by
    rw [rpow_sub ht]
    field_simp
  have e2 : R ^ κ / t ^ κ ≤ 1 / q ^ κ := by
    rw [div_le_div_iff₀ htκ hqκ]
    linarith
  have e3 : C * δ * (1 / q ^ κ) = C / (C + 1) * (η * D) := by
    rw [hδ]
    field_simp
  have e4 : C / (C + 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have hδ0 : 0 ≤ δ := by
    rw [hδ]
    exact div_nonneg (mul_nonneg (mul_nonneg hη hD) hqκ.le) (by linarith)
  calc C * (δ * R ^ κ) * t ^ (α - κ) = C * δ * (R ^ κ / t ^ κ) * t ^ α := e1
    _ ≤ C * δ * (1 / q ^ κ) * t ^ α := by gcongr
    _ = C / (C + 1) * (η * D) * t ^ α := by rw [e3]
    _ ≤ 1 * (η * D) * t ^ α := by gcongr
    _ = η * (D * t ^ α) := by ring
    _ ≤ η * T := by gcongr

/-- Choice of the exponents in mesoscopic negligibility: for `0 < α` and `α + κ < 3α` there are
`0 < ρ < θ < 1` with `ρ < θ²` and `α + κ < 3 α ρ²`. -/
theorem exists_exponents {α κ : ℝ} (hα : 0 < α) (hκ0 : 0 < κ) (hκ : κ < 2 * α) :
    ∃ ρ θ : ℝ, 0 < ρ ∧ ρ < 1 ∧ 0 < θ ∧ θ < 1 ∧ ρ < θ ^ 2 ∧ α + κ < 3 * α * ρ ^ 2 := by
  set s := (α + κ) / (3 * α) with hs
  have hs1 : s < 1 := by rw [hs, div_lt_one (by positivity)]; linarith
  have hs0 : 0 < s := by positivity
  have hρs : s < ((1 + s) / 2) ^ 2 := by nlinarith
  refine ⟨(1 + s) / 2, (1 + (1 + s) / 2) / 2, by linarith, by linarith, by linarith, by linarith,
    by nlinarith, ?_⟩
  have : α + κ = 3 * α * s := by rw [hs]; field_simp
  rw [this]
  exact mul_lt_mul_of_pos_left hρs (by positivity)

/-- Choice of `λ` in mesoscopic negligibility: for `x > 0` there is `0 < λ < 1` with `λ^α ≤ x`. -/
theorem exists_lam {α x : ℝ} (hα : 0 < α) (hx : 0 < x) :
    ∃ lam : ℝ, 0 < lam ∧ lam < 1 ∧ lam ^ α ≤ x := by
  refine ⟨min (1 / 2) (x ^ (1 / α)), lt_min (by norm_num) (rpow_pos_of_pos hx _),
    (min_le_left _ _).trans_lt (by norm_num), ?_⟩
  calc min (1 / 2) (x ^ (1 / α)) ^ α ≤ (x ^ (1 / α)) ^ α :=
        rpow_le_rpow (le_min (by norm_num) (rpow_pos_of_pos hx _).le) (min_le_right _ _) hα.le
    _ = x := by rw [← rpow_mul hx.le, one_div_mul_cancel hα.ne', rpow_one]

/-- Choice of `D` in mesoscopic negligibility: if `ρ a₊ < a₋` and `α ρ λ^α ≤ ε (a₋ - ρ a₊)`, then
`D = (a₊/α + λ^α/ε)⁻¹` satisfies `α ρ ≤ a₋ D`. -/
theorem mul_le_mul_one_div {α ρ am ap ε l : ℝ} (hα : 0 < α) (hap : 0 < ap) (hε : 0 < ε)
    (hl : 0 < l) (h : α * ρ * l ≤ ε * (am - ρ * ap)) :
    α * ρ ≤ am * (1 / (ap / α + l / ε)) := by
  have hE : 0 < ap / α + l / ε := by positivity
  rw [mul_one_div, le_div_iff₀ hE]
  have h2 : α * ρ * (ap / α + l / ε) = ρ * ap + α * ρ * l / ε := by
    field_simp
  have h3 : α * ρ * l / ε ≤ am - ρ * ap := by rw [div_le_iff₀ hε]; linarith
  rw [h2]
  linarith

/-- **Analytic core.** Let `0 < α ≤ κ < 2α`, `r₀ > 0`, `0 < b ≤ B`, `a₀ > 0`, `C ≥ 0`
and `ε > 0`. Suppose `b r^{α+κ} ≤ m₂(r) ≤ B r^{α+κ}` for `r ≥ r₀`, `m₂` and every `T_m`
(`m > 0`) are absolutely continuous on each `[r₀, R]`, `T_m > 0` on `[r₀, ∞)`, `a` is measurable
with `a ~ a₀ r^{-α-1}`, and for every `m > 0` and almost every `r ≥ r₀`,
`T_m'(r) ≤ a(r) T_m(r)²` and `(log m₂)'(r) ≥ 3 a(r) (T_m(r) - C m r^{α-κ})`. Then there are
`δ > 0` and `R₀` with `T_{δ R^κ}(R) < ε R^α` for every `R ≥ R₀`. -/
theorem exists_truncation_lt {T : ℝ → ℝ → ℝ} {m₂ a : ℝ → ℝ} {α κ r₀ a₀ b B C ε : ℝ}
    (hα : 0 < α) (hακ : α ≤ κ) (hκ : κ < 2 * α) (hr₀ : 0 < r₀) (hb : 0 < b) (hbB : b ≤ B)
    (hm₂ : ∀ r, r₀ ≤ r → b * r ^ (α + κ) ≤ m₂ r ∧ m₂ r ≤ B * r ^ (α + κ))
    (hm₂ac : ∀ R, r₀ ≤ R → AbsolutelyContinuousOnInterval m₂ r₀ R)
    (hTpos : ∀ m, 0 < m → ∀ r, r₀ ≤ r → 0 < T m r)
    (hTac : ∀ m, 0 < m → ∀ R, r₀ ≤ R → AbsolutelyContinuousOnInterval (T m) r₀ R)
    (ha : Measurable a) (ha₀ : 0 < a₀) (hasymp : a ~[atTop] fun r => a₀ * r ^ (-α - 1))
    (hC : 0 ≤ C)
    (hd : ∀ m, 0 < m → ∀ᵐ r, r₀ ≤ r → deriv (T m) r ≤ a r * T m r ^ 2 ∧
      3 * a r * (T m r - C * m * r ^ (α - κ)) ≤ deriv (fun r => Real.log (m₂ r)) r)
    (hε : 0 < ε) :
    ∃ δ > 0, ∃ R₀, ∀ R, R₀ ≤ R → T (δ * R ^ κ) R < ε * R ^ α := by
  have hκ0 : 0 < κ := hα.trans_le hακ
  obtain ⟨ρ, θ, hρ0, hρ1, hθ0, hθ1, hθρ, hkμ⟩ := exists_exponents hα hκ0 hκ
  obtain ⟨r₁, hr₁, hab⟩ := exists_bounds_of_isEquivalent (α := α) ha₀ hθ0 hθ1 hasymp
  obtain ⟨am, ham⟩ : ∃ am, am = a₀ * θ := ⟨_, rfl⟩
  obtain ⟨ap, hap⟩ : ∃ ap, ap = a₀ / θ := ⟨_, rfl⟩
  rw [← ham, ← hap] at hab
  have hap0 : 0 < ap := hap ▸ div_pos ha₀ hθ0
  have ham0 : 0 < am := ham ▸ mul_pos ha₀ hθ0
  have hgap : 0 < am - ρ * ap := by
    have : am - ρ * ap = a₀ * (θ ^ 2 - ρ) / θ := by rw [ham, hap]; field_simp
    rw [this]
    exact div_pos (mul_pos ha₀ (by linarith)) hθ0
  obtain ⟨lam, hlam0, hlam1, hlamα⟩ :=
    exists_lam hα (show 0 < ε * (am - ρ * ap) / (α * ρ) by positivity)
  have hlamα0 : 0 < lam ^ α := rpow_pos_of_pos hlam0 α
  obtain ⟨D, hD⟩ : ∃ D, D = 1 / (ap / α + lam ^ α / ε) := ⟨_, rfl⟩
  have hD0 : 0 < D := hD ▸ by positivity
  have hamD : α * ρ ≤ am * D := by
    rw [hD]
    refine mul_le_mul_one_div hα hap0 hε hlamα0 ?_
    rw [le_div_iff₀ (by positivity)] at hlamα
    linarith
  obtain ⟨L, hL⟩ : ∃ L, L = (B / b) ^ (1 / (3 * α * ρ ^ 2 - (α + κ))) + 1 := ⟨_, rfl⟩
  have hL1 : 1 < L := by
    have := rpow_pos_of_pos (div_pos (hb.trans_le hbB) hb) (1 / (3 * α * ρ ^ 2 - (α + κ)))
    linarith
  obtain ⟨q, hq⟩ : ∃ q, q = lam / L := ⟨_, rfl⟩
  have hq0 : 0 < q := hq ▸ div_pos hlam0 (by linarith)
  have hqlam : q < lam := hq ▸ div_lt_self hlam0 hL1
  obtain ⟨δ, hδ⟩ : ∃ δ, δ = (1 - ρ) * D * q ^ κ / (C + 1) := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by
    rw [hδ]
    have : 0 < 1 - ρ := by linarith
    have : 0 < q ^ κ := rpow_pos_of_pos hq0 κ
    exact div_pos (by positivity) (by linarith)
  refine ⟨δ, hδ0, max r₀ r₁ / q, fun R hR => ?_⟩
  rw [div_le_iff₀ hq0] at hR
  have hR0 : 0 < R := by
    have : 0 < R * q := (lt_max_of_lt_left hr₀).trans_le hR
    exact pos_of_mul_pos_left this hq0.le
  have hm0 : 0 < δ * R ^ κ := mul_pos hδ0 (rpow_pos_of_pos hR0 κ)
  by_contra hcon'
  have hcon : ε * R ^ α ≤ T (δ * R ^ κ) R := not_lt.1 hcon'
  have hs₀r₀ : r₀ ≤ q * R := by rw [mul_comm]; exact (le_max_left _ _).trans hR
  have hs₀r₁ : r₁ ≤ q * R := by rw [mul_comm]; exact (le_max_right _ _).trans hR
  have hs₀0 : 0 < q * R := hr₀.trans_le hs₀r₀
  have hs₀t₁ : q * R ≤ lam * R := mul_le_mul_of_nonneg_right hqlam.le hR0.le
  have ht₁R : lam * R ≤ R := mul_le_of_le_one_left hR0.le hlam1.le
  -- Step 1: the reciprocal estimate gives `T_m(t) ≥ D t^α` on `[qR, λR]`.
  have hlow : ∀ t ∈ Icc (q * R) (lam * R), D * t ^ α ≤ T (δ * R ^ κ) t := by
    intro t ht
    have ht0 : 0 < t := hs₀0.trans_le ht.1
    have htR : t ≤ R := ht.2.trans ht₁R
    have hr₀t : r₀ ≤ t := hs₀r₀.trans ht.1
    have hr₁t : r₁ ≤ t := hs₀r₁.trans ht.1
    have hac : AbsolutelyContinuousOnInterval (T (δ * R ^ κ)) t R := by
      refine (hTac _ hm0 R (hr₀t.trans htR)).mono ?_
      rw [uIcc_of_le htR, uIcc_of_le (hr₀t.trans htR)]
      exact Icc_subset_Icc_left hr₀t
    rw [hD]
    refine mul_rpow_le_of_reciprocal hα hap0 hε hlam0 ht0 htR ht.2 hac
      (fun u hu => hTpos _ hm0 u (hr₀t.trans hu.1)) ha (fun u hu => ?_) ?_ hcon
    · have h := hab u (hr₁t.trans hu.1)
      exact ⟨(mul_pos ham0 (rpow_pos_of_pos (ht0.trans_le hu.1) _)).le.trans h.1, h.2⟩
    · filter_upwards [hd _ hm0] with u hu hmem using (hu (hr₀t.trans hmem.1)).1
  -- Step 2: `(log m₂)'(t) ≥ 3 α ρ² / t` for almost every `t ∈ [qR, λR]`.
  have hlog : ∀ᵐ t, t ∈ Icc (q * R) (lam * R / 1) →
      3 * α * ρ ^ 2 / t ≤ deriv (fun t => Real.log (m₂ t)) t := by
    filter_upwards [hd _ hm0] with t ht hmem
    rw [div_one] at hmem
    have ht0 : 0 < t := hs₀0.trans_le hmem.1
    have hTt := hlow t hmem
    refine le_trans ?_ (ht (hs₀r₀.trans hmem.1)).2
    have hcol := collision_le hC (by linarith : (0 : ℝ) ≤ 1 - ρ) hD0.le hq0 hκ0.le hR0 ht0
      hmem.1 hδ hTt
    exact div_le_three_mul_of_bounds hα hρ0 ht0 hD0 hamD (hab t (hs₀r₁.trans hmem.1)).1 hTt
      hcol
  -- Step 3: DISO bounds `λR / qR = L`, contradicting the choice of `L`.
  have hpos₂ : ∀ t ∈ Icc (q * R) (lam * R / 1), 0 < m₂ t := fun t ht => by
    have hr₀t : r₀ ≤ t := hs₀r₀.trans ht.1
    exact (mul_pos hb (rpow_pos_of_pos (hr₀.trans_le hr₀t) _)).trans_le (hm₂ t hr₀t).1
  have hac₂ : AbsolutelyContinuousOnInterval m₂ (q * R) (lam * R / 1) := by
    rw [div_one]
    refine (hm₂ac _ (hs₀r₀.trans hs₀t₁)).mono ?_
    rw [uIcc_of_le hs₀t₁, uIcc_of_le (hs₀r₀.trans hs₀t₁)]
    exact Icc_subset_Icc_left hs₀r₀
  have hdiso := div_le_of_logDeriv_ge (C := 1) le_rfl hs₀0 (by rw [one_mul]; exact hs₀t₁) hb
    hbB hkμ hpos₂ hac₂ (hm₂ _ hs₀r₀).1
    (by rw [div_one]; exact (hm₂ _ (hs₀r₀.trans hs₀t₁)).2) hlog
  have hratio : lam * R / (q * R) = L := by
    rw [hq]
    field_simp
  rw [hratio, one_mul, hL] at hdiso
  linarith

/-- **Mesoscopic negligibility** (conclusion written out). Let `0 < α ≤ κ < 2α` and `r₀ > 0`. For
`r ≥ r₀` let `μ_r` be a probability measure on `ℝ` with integrable identity, and write
`m₁(r) = ∫ x dμ_r`, `m₂(r) = ∫ x² dμ_r` and `T_m(r) = ∫ min x m dμ_r`. Suppose
`m₁(r) ≥ c₁ r^α` with `c₁ > 0`, `b r^{α+κ} ≤ m₂(r) ≤ B r^{α+κ}` with `0 < b ≤ B`, `m₂` and
every `T_m` (`m > 0`) are absolutely continuous on each `[r₀, R]` with `T_m > 0`, `a` is
measurable with `a ~ a₀ r^{-α-1}` (`a₀ > 0`), and `C ≥ 0` satisfies, for every `m > 0` and
almost every `r ≥ r₀`, `T_m'(r) ≤ a(r) T_m(r)²` and
`(log m₂)'(r) ≥ 3 a(r) (T_m(r) - C m r^{α-κ})`. Then
`lim_{δ↓0} limsup_{r→∞} T_{δ r^κ}(r) / m₁(r) = 0`. -/
theorem tendsto_limsup_truncatedMean_div_mean {μ : ℝ → Measure ℝ} {a : ℝ → ℝ}
    {α κ r₀ a₀ b B C c₁ : ℝ} (hα : 0 < α) (hακ : α ≤ κ) (hκ : κ < 2 * α) (hr₀ : 0 < r₀)
    (hμ : ∀ r, r₀ ≤ r → IsProbabilityMeasure (μ r))
    (hint : ∀ r, r₀ ≤ r → Integrable (fun x : ℝ => x) (μ r))
    (hc₁ : 0 < c₁) (hm₁ : ∀ r, r₀ ≤ r → c₁ * r ^ α ≤ ∫ x, x ∂μ r)
    (hb : 0 < b) (hbB : b ≤ B)
    (hm₂ : ∀ r, r₀ ≤ r → b * r ^ (α + κ) ≤ ∫ x, x ^ 2 ∂μ r ∧
      ∫ x, x ^ 2 ∂μ r ≤ B * r ^ (α + κ))
    (hm₂ac : ∀ R, r₀ ≤ R → AbsolutelyContinuousOnInterval (fun r => ∫ x, x ^ 2 ∂μ r) r₀ R)
    (hTpos : ∀ m, 0 < m → ∀ r, r₀ ≤ r → 0 < ∫ x, min x m ∂μ r)
    (hTac : ∀ m, 0 < m → ∀ R, r₀ ≤ R →
      AbsolutelyContinuousOnInterval (fun r => ∫ x, min x m ∂μ r) r₀ R)
    (ha : Measurable a) (ha₀ : 0 < a₀) (hasymp : a ~[atTop] fun r => a₀ * r ^ (-α - 1))
    (hC : 0 ≤ C)
    (hd : ∀ m, 0 < m → ∀ᵐ r, r₀ ≤ r →
      deriv (fun r => ∫ x, min x m ∂μ r) r ≤ a r * (∫ x, min x m ∂μ r) ^ 2 ∧
      3 * a r * ((∫ x, min x m ∂μ r) - C * m * r ^ (α - κ)) ≤
        deriv (fun r => Real.log (∫ x, x ^ 2 ∂μ r)) r) :
    Tendsto (fun δ => limsup (fun r => (∫ x, min x (δ * r ^ κ) ∂μ r) / ∫ x, x ∂μ r) atTop)
      (𝓝[>] 0) (𝓝 0) := by
  have hint_min : ∀ r, r₀ ≤ r → ∀ m : ℝ, Integrable (fun x : ℝ => min x m) (μ r) :=
    fun r hr m => by
      have := hμ r hr
      exact (hint r hr).inf (integrable_const m)
  have hm₁pos : ∀ r, r₀ ≤ r → 0 < ∫ x, x ∂μ r := fun r hr =>
    (mul_pos hc₁ (rpow_pos_of_pos (hr₀.trans_le hr) α)).trans_le (hm₁ r hr)
  -- for `δ > 0` the ratio lies in `[0, 1]` beyond `r₀`
  have hrange : ∀ δ, 0 < δ → ∀ r, r₀ ≤ r →
      0 ≤ (∫ x, min x (δ * r ^ κ) ∂μ r) / ∫ x, x ∂μ r ∧
        (∫ x, min x (δ * r ^ κ) ∂μ r) / ∫ x, x ∂μ r ≤ 1 := fun δ hδ r hr => by
    have hr0 : 0 < r := hr₀.trans_le hr
    have hT := hTpos _ (mul_pos hδ (rpow_pos_of_pos hr0 κ)) r hr
    refine ⟨div_nonneg hT.le (hm₁pos r hr).le, (div_le_one (hm₁pos r hr)).2 ?_⟩
    exact integral_mono (hint_min r hr _) (hint r hr) fun x => min_le_left _ _
  refine tendsto_order.2 ⟨fun a' ha' => ?_, fun a' ha' => ?_⟩
  · filter_upwards [self_mem_nhdsWithin] with δ (hδ : 0 < δ)
    refine ha'.trans_le (le_limsup_of_frequently_le ?_ ?_)
    · exact (eventually_ge_atTop r₀).frequently.mono fun r hr => (hrange δ hδ r hr).1
    · exact isBoundedUnder_of_eventually_le
        ((eventually_ge_atTop r₀).mono fun r hr => (hrange δ hδ r hr).2)
  · obtain ⟨δ₀, hδ₀, R₀, hR₀⟩ := exists_truncation_lt
      (T := fun m r => ∫ x, min x m ∂μ r) (m₂ := fun r => ∫ x, x ^ 2 ∂μ r) hα hακ hκ hr₀
      hb hbB hm₂ hm₂ac hTpos hTac ha ha₀ hasymp hC hd
      (show 0 < c₁ * a' / 2 by positivity)
    filter_upwards [Ioc_mem_nhdsGT hδ₀] with δ hδ
    have hle : limsup (fun r => (∫ x, min x (δ * r ^ κ) ∂μ r) / ∫ x, x ∂μ r) atTop ≤
        a' / 2 := by
      refine limsup_le_of_le ?_ ?_
      · exact isCoboundedUnder_le_of_eventually_le atTop
          ((eventually_ge_atTop r₀).mono fun r hr => (hrange δ hδ.1 r hr).1)
      · filter_upwards [eventually_ge_atTop (max r₀ R₀)] with r hr
        have hr₀r : r₀ ≤ r := (le_max_left _ _).trans hr
        have hr0 : 0 < r := hr₀.trans_le hr₀r
        have hmono : (∫ x, min x (δ * r ^ κ) ∂μ r) ≤ ∫ x, min x (δ₀ * r ^ κ) ∂μ r :=
          integral_mono (hint_min r hr₀r _) (hint_min r hr₀r _) fun x =>
            min_le_min_left x (mul_le_mul_of_nonneg_right hδ.2 (rpow_nonneg hr0.le κ))
        have hlt := hR₀ r ((le_max_right _ _).trans hr)
        have hrα : 0 < r ^ α := rpow_pos_of_pos hr0 α
        rw [div_le_iff₀ (hm₁pos r hr₀r)]
        have h1 := hm₁ r hr₀r
        have : c₁ * a' / 2 * r ^ α = a' / 2 * (c₁ * r ^ α) := by ring
        nlinarith
    linarith

/-! ### Non-vacuity: the two-point family

For `r ≥ 1`, `μ_r = r^{α-κ} δ_{r^κ} + (1 - r^{α-κ}) δ_0`, with `a(r) = α r^{-α-1}` and
`C = 1`. Then `m₁ = r^α`, `m₂ = r^{α+κ}` and `T_m(r) = r^{α-κ} min(r^κ, m)`. -/

section Witness

variable {α κ : ℝ} {μ : ℝ → Measure ℝ}

/-- Integrals against the two-point law. -/
theorem integral_twoPoint (hακ : α ≤ κ)
    (hμ : ∀ r, μ r = ENNReal.ofReal (r ^ (α - κ)) • Measure.dirac (r ^ κ) +
      ENNReal.ofReal (1 - r ^ (α - κ)) • Measure.dirac 0)
    (f : ℝ → ℝ) {r : ℝ} (hr : 1 ≤ r) :
    ∫ x, f x ∂μ r = r ^ (α - κ) * f (r ^ κ) + (1 - r ^ (α - κ)) * f 0 := by
  have hp0 : 0 ≤ r ^ (α - κ) := rpow_nonneg (zero_le_one.trans hr) _
  have hp1 : r ^ (α - κ) ≤ 1 := rpow_le_one_of_one_le_of_nonpos hr (by linarith)
  rw [hμ, integral_add_measure, integral_smul_measure, integral_smul_measure, integral_dirac,
    integral_dirac, ENNReal.toReal_ofReal hp0, ENNReal.toReal_ofReal (by linarith),
    smul_eq_mul, smul_eq_mul]
  · exact (integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top
  · exact (integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top

/-- The two-point law is a probability measure for `r ≥ 1`. -/
theorem isProbabilityMeasure_twoPoint (hακ : α ≤ κ)
    (hμ : ∀ r, μ r = ENNReal.ofReal (r ^ (α - κ)) • Measure.dirac (r ^ κ) +
      ENNReal.ofReal (1 - r ^ (α - κ)) • Measure.dirac 0)
    {r : ℝ} (hr : 1 ≤ r) : IsProbabilityMeasure (μ r) := by
  have hp0 : 0 ≤ r ^ (α - κ) := rpow_nonneg (zero_le_one.trans hr) _
  have hp1 : r ^ (α - κ) ≤ 1 := rpow_le_one_of_one_le_of_nonpos hr (by linarith)
  constructor
  rw [hμ, Measure.add_apply, Measure.smul_apply, Measure.smul_apply, measure_univ,
    measure_univ, smul_eq_mul, smul_eq_mul, mul_one, mul_one,
    ← ENNReal.ofReal_add hp0 (by linarith)]
  simp

/-- The truncated mean of the two-point law. -/
theorem truncatedMean_twoPoint (hακ : α ≤ κ)
    (hμ : ∀ r, μ r = ENNReal.ofReal (r ^ (α - κ)) • Measure.dirac (r ^ κ) +
      ENNReal.ofReal (1 - r ^ (α - κ)) • Measure.dirac 0)
    {m r : ℝ} (hm : 0 < m) (hr : 1 ≤ r) :
    ∫ x, min x m ∂μ r = r ^ (α - κ) * min (r ^ κ) m := by
  rw [integral_twoPoint hακ hμ (fun x => min x m) hr, min_eq_left hm.le, mul_zero, add_zero]

/-- The two-point law has `m₁ = r^α`. -/
theorem mean_twoPoint (hακ : α ≤ κ)
    (hμ : ∀ r, μ r = ENNReal.ofReal (r ^ (α - κ)) • Measure.dirac (r ^ κ) +
      ENNReal.ofReal (1 - r ^ (α - κ)) • Measure.dirac 0)
    {r : ℝ} (hr : 1 ≤ r) : ∫ x, x ∂μ r = r ^ α := by
  rw [integral_twoPoint hακ hμ (fun x => x) hr, mul_zero, add_zero,
    ← rpow_add (zero_lt_one.trans_le hr), sub_add_cancel]

/-- The two-point law has `m₂ = r^{α+κ}`. -/
theorem secondMoment_twoPoint (hακ : α ≤ κ)
    (hμ : ∀ r, μ r = ENNReal.ofReal (r ^ (α - κ)) • Measure.dirac (r ^ κ) +
      ENNReal.ofReal (1 - r ^ (α - κ)) • Measure.dirac 0)
    {r : ℝ} (hr : 1 ≤ r) : ∫ x, x ^ 2 ∂μ r = r ^ (α + κ) := by
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  rw [integral_twoPoint hακ hμ (fun x => x ^ 2) hr]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero]
  rw [← rpow_natCast, ← rpow_mul hr0.le, ← rpow_add hr0]
  congr 1
  push_cast
  ring

/-- `r ↦ r^p` is absolutely continuous on `[1, R]`. -/
theorem absolutelyContinuousOnInterval_rpow_one (p : ℝ) {R : ℝ} (hR : 1 ≤ R) :
    AbsolutelyContinuousOnInterval (fun r : ℝ => r ^ p) 1 R := by
  refine ContDiffOn.absolutelyContinuousOnInterval fun x hx => ?_
  rw [uIcc_of_le hR] at hx
  exact (Real.contDiffAt_rpow_const_of_ne (zero_lt_one.trans_le hx.1).ne').contDiffWithinAt

/-- The ratio `T_{δ r^κ}(r) / m₁(r)` of the two-point law is `min 1 δ` for `r ≥ 1`. -/
theorem truncatedMean_div_mean_twoPoint (hακ : α ≤ κ)
    (hμ : ∀ r, μ r = ENNReal.ofReal (r ^ (α - κ)) • Measure.dirac (r ^ κ) +
      ENNReal.ofReal (1 - r ^ (α - κ)) • Measure.dirac 0)
    {δ r : ℝ} (hδ : 0 < δ) (hr : 1 ≤ r) :
    (∫ x, min x (δ * r ^ κ) ∂μ r) / ∫ x, x ∂μ r = min 1 δ := by
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  rw [truncatedMean_twoPoint hακ hμ (mul_pos hδ (rpow_pos_of_pos hr0 κ)) hr,
    mean_twoPoint hακ hμ hr]
  have h1 : min (r ^ κ) (δ * r ^ κ) = min 1 δ * r ^ κ := by
    rw [min_mul_of_nonneg _ _ (rpow_pos_of_pos hr0 κ).le, one_mul]
  rw [h1, show r ^ (α - κ) * (min 1 δ * r ^ κ) = min 1 δ * (r ^ (α - κ) * r ^ κ) by ring,
    ← rpow_add hr0, sub_add_cancel, mul_div_assoc, div_self (rpow_pos_of_pos hr0 α).ne',
    mul_one]

/-- The differential inequalities of `tendsto_limsup_truncatedMean_div_mean` for the two-point law,
with `a(r) = α r^{-α-1}` and `C = 1`. -/
theorem ae_deriv_twoPoint (hα : 0 < α) (hακ : α ≤ κ)
    (hμ : ∀ r, μ r = ENNReal.ofReal (r ^ (α - κ)) • Measure.dirac (r ^ κ) +
      ENNReal.ofReal (1 - r ^ (α - κ)) • Measure.dirac 0)
    {m : ℝ} (hm : 0 < m) :
    ∀ᵐ r, 1 ≤ r →
      deriv (fun r => ∫ x, min x m ∂μ r) r ≤ α * r ^ (-α - 1) * (∫ x, min x m ∂μ r) ^ 2 ∧
      3 * (α * r ^ (-α - 1)) * ((∫ x, min x m ∂μ r) - 1 * m * r ^ (α - κ)) ≤
        deriv (fun r => Real.log (∫ x, x ^ 2 ∂μ r)) r := by
  have hκ0 : 0 < κ := hα.trans_le hακ
  have h1 : ∀ᵐ r : ℝ, r ≠ 1 := by
    rw [ae_iff]
    simp
  have h2 : ∀ᵐ r : ℝ, r ≠ m ^ (1 / κ) := by
    rw [ae_iff]
    simp
  filter_upwards [h1, h2] with r hr1 hr2 hr
  have hr' : 1 < r := lt_of_le_of_ne hr (Ne.symm hr1)
  have hr0 : 0 < r := zero_lt_one.trans hr'
  have hT : (fun s => ∫ x, min x m ∂μ s) =ᶠ[𝓝 r] fun s => s ^ (α - κ) * min (s ^ κ) m := by
    filter_upwards [Ioi_mem_nhds hr'] with s hs
    exact truncatedMean_twoPoint hακ hμ hm (le_of_lt hs)
  have hM : (fun s => Real.log (∫ x, x ^ 2 ∂μ s)) =ᶠ[𝓝 r] fun s => (α + κ) * Real.log s := by
    filter_upwards [Ioi_mem_nhds hr'] with s hs
    rw [secondMoment_twoPoint hακ hμ (le_of_lt hs), Real.log_rpow (zero_lt_one.trans hs)]
  have hc : ContinuousAt (fun s : ℝ => s ^ κ) r := Real.continuousAt_rpow_const r κ
    (Or.inl hr0.ne')
  have hne : r ^ κ ≠ m := by
    intro h
    apply hr2
    rw [← h, ← rpow_mul hr0.le, mul_one_div_cancel hκ0.ne', rpow_one]
  have hapos : 0 < α * r ^ (-α - 1) := mul_pos hα (rpow_pos_of_pos hr0 _)
  constructor
  · rw [hT.deriv_eq, truncatedMean_twoPoint hακ hμ hm hr]
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hev : (fun s => s ^ (α - κ) * min (s ^ κ) m) =ᶠ[𝓝 r] fun s => s ^ α := by
        filter_upwards [hc.eventually (gt_mem_nhds hlt), Ioi_mem_nhds hr0] with s hs hs0
        rw [min_eq_left hs.le, ← rpow_add hs0, sub_add_cancel]
      rw [hev.deriv_eq, Real.deriv_rpow_const, min_eq_left hlt.le, ← rpow_add hr0,
        sub_add_cancel]
      have : r ^ (-α - 1) * (r ^ α) ^ 2 = r ^ (α - 1) := by
        rw [← rpow_natCast, ← rpow_mul hr0.le, ← rpow_add hr0]
        congr 1
        push_cast
        ring
      rw [mul_assoc, this]
    · have hev : (fun s => s ^ (α - κ) * min (s ^ κ) m) =ᶠ[𝓝 r]
          fun s => m * s ^ (α - κ) := by
        filter_upwards [hc.eventually (lt_mem_nhds hgt)] with s hs
        rw [min_eq_right hs.le, mul_comm]
      rw [hev.deriv_eq, deriv_const_mul_field, Real.deriv_rpow_const]
      have : m * ((α - κ) * r ^ (α - κ - 1)) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hm.le
          (mul_nonpos_of_nonpos_of_nonneg (by linarith) (rpow_nonneg hr0.le _))
      exact this.trans (by positivity)
  · rw [hM.deriv_eq, truncatedMean_twoPoint hακ hμ hm hr, deriv_const_mul_field,
      Real.deriv_log]
    have hp : 0 ≤ r ^ (α - κ) := rpow_nonneg hr0.le _
    have hmin := min_le_right (r ^ κ) m
    have hlhs : 3 * (α * r ^ (-α - 1)) * (r ^ (α - κ) * min (r ^ κ) m - 1 * m * r ^ (α - κ)) ≤
        0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) (by nlinarith)
    exact hlhs.trans (mul_nonneg (by linarith) (inv_nonneg.2 hr0.le))

/-- **Non-vacuity witness for `tendsto_limsup_truncatedMean_div_mean`.** For every `0 < α ≤ κ < 2α`,
the two-point family satisfies all hypotheses of `tendsto_limsup_truncatedMean_div_mean` with
`r₀ = 1`, `a(r) = α r^{-α-1}`, `a₀ = α`, `b = B = c₁ = 1` and `C = 1`. Its conclusion also holds
directly, since the ratio is `min 1 δ` (`truncatedMean_div_mean_twoPoint`). -/
theorem tendsto_twoPoint (hα : 0 < α) (hακ : α ≤ κ) (hκ : κ < 2 * α)
    (hμ : ∀ r, μ r = ENNReal.ofReal (r ^ (α - κ)) • Measure.dirac (r ^ κ) +
      ENNReal.ofReal (1 - r ^ (α - κ)) • Measure.dirac 0) :
    Tendsto (fun δ => limsup (fun r => (∫ x, min x (δ * r ^ κ) ∂μ r) / ∫ x, x ∂μ r) atTop)
      (𝓝[>] 0) (𝓝 0) := by
  refine tendsto_limsup_truncatedMean_div_mean (r₀ := 1) (a₀ := α) (b := 1) (B := 1) (C := 1)
    (c₁ := 1) (a := fun r => α * r ^ (-α - 1)) hα hακ hκ one_pos
    (fun r hr => isProbabilityMeasure_twoPoint hακ hμ hr) (fun r hr => ?_) one_pos
    (fun r hr => by rw [mean_twoPoint hακ hμ hr, one_mul]) one_pos le_rfl
    (fun r hr => by
      rw [secondMoment_twoPoint hακ hμ hr]; simp only [one_mul]; exact ⟨le_rfl, le_rfl⟩)
    (fun R hR => (absolutelyContinuousOnInterval_rpow_one (α + κ) hR).congr fun r hr => by
      rw [uIcc_of_le hR] at hr
      exact (secondMoment_twoPoint hακ hμ hr.1).symm)
    (fun m hm r hr => by
      rw [truncatedMean_twoPoint hακ hμ hm hr]
      exact mul_pos (rpow_pos_of_pos (zero_lt_one.trans_le hr) _)
        (lt_min (rpow_pos_of_pos (zero_lt_one.trans_le hr) _) hm))
    (fun m hm R hR => by
      refine ((absolutelyContinuousOnInterval_rpow_one (α - κ) hR).mul
        ((LipschitzWith.id.min_const m).comp_absolutelyContinuousOnInterval
          (absolutelyContinuousOnInterval_rpow_one κ hR))).congr fun r hr => ?_
      rw [uIcc_of_le hR] at hr
      exact (truncatedMean_twoPoint hακ hμ hm hr.1).symm)
    (by fun_prop) hα (IsEquivalent.refl) zero_le_one
    (fun m hm => ae_deriv_twoPoint hα hακ hμ hm)
  rw [hμ]
  exact ((integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top).add_measure
    ((integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top)

end Witness

end PercLib.Analysis
