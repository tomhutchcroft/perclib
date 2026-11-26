/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrappers for the mesoscopic-tail-transfer assertions OP4X, J5R6 and KKGL,
proved from `ReciprocalODE.lean` and `MesoscopicNegligibility.lean`. No new definitions.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Analysis.ReciprocalODE
public import PercLib.Analysis.MesoscopicNegligibility

/-!
# Mesoscopic tail transfer: correspondence

Wiki correspondence for the reciprocal ODE bounds, the two-point example and mesoscopic
negligibility.

## Main results

* `reciprocal_ode_lower_bounds`
* `twoPoint_truncated_ratio_example`
* `tendsto_limsup_truncatedMean_div_mean_of_isTheta`
-/

@[expose] public section
noncomputable section

open MeasureTheory Set Filter Real Asymptotics
open scoped Topology ENNReal

namespace PercLib.Analysis

/-- **OP4X.** Let `T > 0` be absolutely continuous on `[r₀, R]`, `a ≥ 0` integrable there and
`T' ≤ a T²` a.e. Then for `ℓ ∈ [r₀, R]`, `T(ℓ) ≥ (1/T(R) + ∫_ℓ^R a)⁻¹`; and if `r₀ > 0`,
`α, A, ε > 0`, `a(s) ≤ A s^{-α-1}` and `T(R) ≥ ε R^α`, then the denominator
`A/α + (ε⁻¹ - A/α)(ℓ/R)^α` is positive and `T(ℓ) ≥ ℓ^α / (A/α + (ε⁻¹ - A/α)(ℓ/R)^α)`. -/
@[tag "OP4X"]
theorem reciprocal_ode_lower_bounds {T a : ℝ → ℝ} {r₀ R ℓ : ℝ}
    (hT : AbsolutelyContinuousOnInterval T r₀ R)
    (hpos : ∀ s ∈ Icc r₀ R, 0 < T s) (ha : IntervalIntegrable a volume r₀ R)
    (ha0 : ∀ s ∈ Icc r₀ R, 0 ≤ a s)
    (hder : ∀ᵐ s, s ∈ Icc r₀ R → deriv T s ≤ a s * T s ^ 2) (hℓ : ℓ ∈ Icc r₀ R) :
    (1 / T R + ∫ s in ℓ..R, a s)⁻¹ ≤ T ℓ ∧
    ∀ {α A ε : ℝ}, 0 < r₀ → 0 < α → 0 < A → 0 < ε →
      (∀ s ∈ Icc r₀ R, a s ≤ A * s ^ (-α - 1)) → ε * R ^ α ≤ T R →
      0 < A / α + (ε⁻¹ - A / α) * (ℓ / R) ^ α ∧
      ℓ ^ α / (A / α + (ε⁻¹ - A / α) * (ℓ / R) ^ α) ≤ T ℓ := by
  refine ⟨le_of_deriv_le_mul_sq hT hpos ha ha0 hder hℓ, fun {α A ε} hr₀ hα hA hε haA hTR => ?_⟩
  refine ⟨?_, rpow_div_le_of_deriv_le_mul_sq hr₀ hT hpos ha ha0 hder hα hA hε haA hTR hℓ⟩
  have hℓ0 : 0 < ℓ := hr₀.trans_le hℓ.1
  have hR0 : 0 < R := hℓ0.trans_le hℓ.2
  have ht0 : 0 < (ℓ / R) ^ α := rpow_pos_of_pos (div_pos hℓ0 hR0) α
  have ht1 : (ℓ / R) ^ α ≤ 1 :=
    rpow_le_one (div_pos hℓ0 hR0).le ((div_le_one hR0).2 hℓ.2) hα.le
  have hAα : 0 < A / α := div_pos hA hα
  have hεi : 0 < ε⁻¹ := inv_pos.2 hε
  have : A / α + (ε⁻¹ - A / α) * (ℓ / R) ^ α =
      (1 - (ℓ / R) ^ α) * (A / α) + (ℓ / R) ^ α * ε⁻¹ := by ring
  rw [this]
  have h1 : 0 ≤ (1 - (ℓ / R) ^ α) * (A / α) := mul_nonneg (by linarith) hAα.le
  have h2 : 0 < (ℓ / R) ^ α * ε⁻¹ := mul_pos ht0 hεi
  linarith

/-- **J5R6.** Let `0 < α < κ` and let `X_r` take the value `r^κ` with probability
`r^{α-κ}` and `r^α` otherwise (`r ≥ 1`). Then `E X_r = (2 - r^{α-κ}) r^α ~ 2 r^α`,
`E X_r² = r^{α+κ} + (1 - r^{α-κ}) r^{2α} ~ r^{α+κ}`, for `0 < δ ≤ 1`
`E min(X_r, δ r^κ)/E X_r → (1+δ)/2`, and the limit as `δ ↓ 0` of these limits is `1/2`. -/
@[tag "J5R6"]
theorem twoPoint_truncated_ratio_example {α κ : ℝ} (_hα : 0 < α) (hακ : α < κ) :
    (∀ r, 1 ≤ r →
      ∫ x, x ∂(ENNReal.ofReal (r ^ (α - κ)) • Measure.dirac (r ^ κ) +
          ENNReal.ofReal (1 - r ^ (α - κ)) • Measure.dirac (r ^ α)) =
        (2 - r ^ (α - κ)) * r ^ α ∧
      ∫ x, x ^ 2 ∂(ENNReal.ofReal (r ^ (α - κ)) • Measure.dirac (r ^ κ) +
          ENNReal.ofReal (1 - r ^ (α - κ)) • Measure.dirac (r ^ α)) =
        r ^ (α + κ) + (1 - r ^ (α - κ)) * r ^ (2 * α)) ∧
    ((fun r => ∫ x, x ∂(ENNReal.ofReal (r ^ (α - κ)) • Measure.dirac (r ^ κ) +
        ENNReal.ofReal (1 - r ^ (α - κ)) • Measure.dirac (r ^ α))) ~[atTop]
      fun r => 2 * r ^ α) ∧
    ((fun r => ∫ x, x ^ 2 ∂(ENNReal.ofReal (r ^ (α - κ)) • Measure.dirac (r ^ κ) +
        ENNReal.ofReal (1 - r ^ (α - κ)) • Measure.dirac (r ^ α))) ~[atTop]
      fun r => r ^ (α + κ)) ∧
    (∀ δ, 0 < δ → δ ≤ 1 →
      Tendsto (fun r => (∫ x, min x (δ * r ^ κ) ∂(ENNReal.ofReal (r ^ (α - κ)) •
          Measure.dirac (r ^ κ) + ENNReal.ofReal (1 - r ^ (α - κ)) • Measure.dirac (r ^ α))) /
        ∫ x, x ∂(ENNReal.ofReal (r ^ (α - κ)) • Measure.dirac (r ^ κ) +
          ENNReal.ofReal (1 - r ^ (α - κ)) • Measure.dirac (r ^ α))) atTop
        (𝓝 ((1 + δ) / 2))) ∧
    Tendsto (fun δ => limUnder atTop (fun r =>
        (∫ x, min x (δ * r ^ κ) ∂(ENNReal.ofReal (r ^ (α - κ)) •
          Measure.dirac (r ^ κ) + ENNReal.ofReal (1 - r ^ (α - κ)) • Measure.dirac (r ^ α))) /
        ∫ x, x ∂(ENNReal.ofReal (r ^ (α - κ)) • Measure.dirac (r ^ κ) +
          ENNReal.ofReal (1 - r ^ (α - κ)) • Measure.dirac (r ^ α))))
      (𝓝[>] 0) (𝓝 (1 / 2)) := by
  have hp : Tendsto (fun r : ℝ => r ^ (α - κ)) atTop (𝓝 0) := by
    have := tendsto_rpow_neg_atTop (y := κ - α) (by linarith)
    simpa [neg_sub] using this
  refine ⟨fun r hr => ⟨integral_id_twoPoint hr hακ, integral_sq_twoPoint hr hακ⟩, ?_, ?_,
    fun δ hδ hδ1 => tendsto_truncated_ratio hακ hδ hδ1, ?_⟩
  · -- the mean
    have h2 : (fun r : ℝ => 2 - r ^ (α - κ)) ~[atTop] fun _ => (2 : ℝ) := by
      have h := (isEquivalent_const_iff_tendsto (u := fun r : ℝ => 2 - r ^ (α - κ))
        (l := atTop) (c := (2 : ℝ)) two_ne_zero).2
        (by simpa using (tendsto_const_nhds (x := (2 : ℝ))).sub hp)
      exact h
    refine (h2.mul (IsEquivalent.refl (u := fun r : ℝ => r ^ α))).congr_left ?_
    filter_upwards [eventually_ge_atTop 1] with r hr
    exact (integral_id_twoPoint hr hακ).symm
  · -- the second moment
    have hlo : (fun r : ℝ => (1 - r ^ (α - κ)) * r ^ (2 * α)) =o[atTop]
        fun r => r ^ (α + κ) := by
      have h0 : Tendsto (fun r : ℝ => (1 - r ^ (α - κ)) * r ^ (α - κ)) atTop (𝓝 0) := by
        simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub hp).mul hp
      have h := (isBigO_refl (fun r : ℝ => r ^ (α + κ)) atTop).mul_isLittleO
          ((isLittleO_one_iff (F := ℝ)).2 h0)
      simp only [mul_one] at h
      refine h.congr' ?_ EventuallyEq.rfl
      filter_upwards [eventually_gt_atTop 0] with r hr
      rw [show r ^ (α + κ) * ((1 - r ^ (α - κ)) * r ^ (α - κ)) =
          (1 - r ^ (α - κ)) * (r ^ (α + κ) * r ^ (α - κ)) by ring, ← rpow_add hr]
      ring_nf
    refine (IsEquivalent.refl.add_isLittleO hlo).congr_left ?_
    filter_upwards [eventually_ge_atTop 1] with r hr
    exact (integral_sq_twoPoint hr hακ).symm
  · -- the iterated limit
    have hlim : Tendsto (fun δ : ℝ => (1 + δ) / 2) (𝓝[>] 0) (𝓝 (1 / 2)) := by
      have : Tendsto (fun δ : ℝ => (1 + δ) / 2) (𝓝 0) (𝓝 ((1 + 0) / 2)) :=
        ((continuous_const.add continuous_id).div_const 2).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    refine hlim.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with δ hδ
    exact ((tendsto_truncated_ratio hακ hδ.1 hδ.2.le).limUnder_eq).symm

/-- **KKGL** (conclusion written out). Let `0 < α ≤ κ < 2α` and `r₀ > 0`. For `r ≥ r₀`
let `μ_r` be a probability measure on `[0, ∞)` with integrable `x` and `x²`, and write
`m₁(r) = ∫ x dμ_r`, `m₂(r) = ∫ x² dμ_r` and `T_m(r) = ∫ min x m dμ_r`. Suppose `m₁ ≍ r^α`,
`b r^{α+κ} ≤ m₂(r) ≤ B r^{α+κ}` with `0 < b ≤ B`, `m₂` and every `T_m` (`m > 0`) are
absolutely continuous on each `[r₀, R]` with `T_m > 0`, `a > 0` is measurable with
`a ~ a₀ r^{-α-1}` (`a₀ > 0`), and `C ≥ 0` satisfies, for every `m > 0` and almost every
`r ≥ r₀`, `T_m'(r) ≤ a(r) T_m(r)²` and `(log m₂)'(r) ≥ 3 a(r) (T_m(r) - C m r^{α-κ})`. Then
`lim_{δ↓0} limsup_{r→∞} T_{δ r^κ}(r) / m₁(r) = 0`. -/
@[tag "KKGL"]
theorem tendsto_limsup_truncatedMean_div_mean_of_isTheta {μ : ℝ → Measure ℝ} {a : ℝ → ℝ}
    {α κ r₀ a₀ b B C : ℝ} (hα : 0 < α) (hακ : α ≤ κ) (hκ : κ < 2 * α) (hr₀ : 0 < r₀)
    (hμ : ∀ r, r₀ ≤ r → IsProbabilityMeasure (μ r)) (_hnn : ∀ r, r₀ ≤ r → ∀ᵐ x ∂μ r, 0 ≤ x)
    (hint : ∀ r, r₀ ≤ r → Integrable (fun x : ℝ => x) (μ r))
    (_hint2 : ∀ r, r₀ ≤ r → Integrable (fun x : ℝ => x ^ 2) (μ r))
    (hm₁ : (fun r => ∫ x, x ∂μ r) =Θ[atTop] fun r => r ^ α)
    (hb : 0 < b) (hbB : b ≤ B)
    (hm₂ : ∀ r, r₀ ≤ r → b * r ^ (α + κ) ≤ ∫ x, x ^ 2 ∂μ r ∧
      ∫ x, x ^ 2 ∂μ r ≤ B * r ^ (α + κ))
    (hm₂ac : ∀ R, r₀ ≤ R → AbsolutelyContinuousOnInterval (fun r => ∫ x, x ^ 2 ∂μ r) r₀ R)
    (hTpos : ∀ m, 0 < m → ∀ r, r₀ ≤ r → 0 < ∫ x, min x m ∂μ r)
    (hTac : ∀ m, 0 < m → ∀ R, r₀ ≤ R →
      AbsolutelyContinuousOnInterval (fun r => ∫ x, min x m ∂μ r) r₀ R)
    (ha : Measurable a) (_hapos : ∀ r, r₀ ≤ r → 0 < a r) (ha₀ : 0 < a₀)
    (hasymp : a ~[atTop] fun r => a₀ * r ^ (-α - 1))
    (hC : 0 ≤ C)
    (hd : ∀ m, 0 < m → ∀ᵐ r, r₀ ≤ r →
      deriv (fun r => ∫ x, min x m ∂μ r) r ≤ a r * (∫ x, min x m ∂μ r) ^ 2 ∧
      3 * a r * ((∫ x, min x m ∂μ r) - C * m * r ^ (α - κ)) ≤
        deriv (fun r => Real.log (∫ x, x ^ 2 ∂μ r)) r) :
    Tendsto (fun δ => limsup (fun r => (∫ x, min x (δ * r ^ κ) ∂μ r) / ∫ x, x ∂μ r) atTop)
      (𝓝[>] 0) (𝓝 0) := by
  -- `m₁ > 0` on `[r₀, ∞)`, since `m₁ ≥ T_1 > 0`
  have hm₁pos : ∀ r, r₀ ≤ r → 0 < ∫ x, x ∂μ r := fun r hr => by
    have := hμ r hr
    refine (hTpos 1 one_pos r hr).trans_le (integral_mono ((hint r hr).inf
      (integrable_const 1)) (hint r hr) fun x => min_le_left x 1)
  -- a lower bound `r^α ≤ c m₁(r)` from `≍`
  obtain ⟨c, hc⟩ := hm₁.2.bound
  obtain ⟨R₁, hR₁⟩ := eventually_atTop.1 (hc.and (eventually_gt_atTop 0))
  set r₁ := max r₀ (max R₁ 1) with hr₁
  have hr₀r₁ : r₀ ≤ r₁ := le_max_left _ _
  have hlow : ∀ r, r₁ ≤ r → r ^ α ≤ c * ∫ x, x ∂μ r := fun r hr => by
    have h := (hR₁ r ((le_max_left _ _).trans ((le_max_right _ _).trans hr))).1
    rwa [Real.norm_of_nonneg (rpow_pos_of_pos (hr₀.trans_le (hr₀r₁.trans hr)) α).le,
      Real.norm_of_nonneg (hm₁pos r (hr₀r₁.trans hr)).le] at h
  have hc0 : 0 < c := by
    have h1 := hlow r₁ le_rfl
    have h2 := rpow_pos_of_pos (hr₀.trans_le hr₀r₁) α
    have h3 := hm₁pos r₁ hr₀r₁
    by_contra hc0
    nlinarith [mul_nonpos_of_nonpos_of_nonneg (not_lt.1 hc0) h3.le]
  have hm₁' : ∀ r, r₁ ≤ r → c⁻¹ * r ^ α ≤ ∫ x, x ∂μ r := fun r hr => by
    rw [inv_mul_le_iff₀ hc0]
    exact hlow r hr
  have hsub : ∀ R, r₁ ≤ R → uIcc r₁ R ⊆ uIcc r₀ R := fun R hR => by
    rw [uIcc_of_le hR, uIcc_of_le (hr₀r₁.trans hR)]
    exact Icc_subset_Icc hr₀r₁ le_rfl
  exact tendsto_limsup_truncatedMean_div_mean (r₀ := r₁) (c₁ := c⁻¹) hα hακ hκ
    (hr₀.trans_le hr₀r₁) (fun r hr => hμ r (hr₀r₁.trans hr))
    (fun r hr => hint r (hr₀r₁.trans hr)) (inv_pos.2 hc0) hm₁' hb hbB
    (fun r hr => hm₂ r (hr₀r₁.trans hr))
    (fun R hR => (hm₂ac R (hr₀r₁.trans hR)).mono (hsub R hR)) (fun m hm r hr =>
      hTpos m hm r (hr₀r₁.trans hr))
    (fun m hm R hR => (hTac m hm R (hr₀r₁.trans hR)).mono (hsub R hR)) ha ha₀ hasymp hC
    (fun m hm => (hd m hm).mono fun r h hr => h (hr₀r₁.trans hr))

end PercLib.Analysis
