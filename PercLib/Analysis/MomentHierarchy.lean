/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-16, against pinned mathlib. No upstream proof is copied. The
combinatorial identity is `lemma_I_4_23` of `PercLib.Combinatorics.DoubleFactorialConvolution`.
-/
module

public import PercLib.Combinatorics.DoubleFactorialConvolution
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import PercLib.Meta.Tag

/-!
# Double-factorial asymptotics from a closed power-law moment hierarchy (5O1G)

Let `P ≥ 3`, `r₀, α, B, C > 0`, and let `m₁, …, m_P > 0` be absolutely continuous on every
`[r₀, R]`. Suppose `m₁ ~ B r^α`, `m₂ ~ C r^{3α}`, `a ~ (α/B) r^{−α−1}`, and for `3 ≤ p ≤ P`
there are errors `ε_p → 0` with

  `m_p' = (1 + ε_p) a ∑_{ℓ=0}^{p−1} C(p,ℓ) m_{ℓ+1} m_{p−ℓ}`  a.e. on `[r₀, ∞)`.

Then `m_p ~ (2p−3)‼ (m₂/m₁)^{p−1} m₁` for `1 ≤ p ≤ P` (`isEquivalent_moment_hierarchy`).

The analytic step is `tendsto_div_rpow_of_ae_deriv`: if `S ≥ 0` is absolutely continuous,
`S' = u S + g` a.e., `r u(r) → q` and `g(r)/r^{β−1} → c` with `q < β`, then
`S(r)/r^β → c/(β − q)`. No rate is assumed on the errors. It is proved by comparing with the
integrating factors `r^{−(q ± η)}` (`sub_le_of_ae_deriv_sub_le_rpow`,
`le_sub_of_ae_le_deriv_sub_rpow`). The constants close by Lemma I.4.23,
`∑_{k<n} C(n,k) (2k−1)‼ (2n−2k−3)‼ = (2n−1)‼`.

No definition is introduced.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Real intervalIntegral Asymptotics
open scoped Topology Nat

namespace PercLib.Analysis

/-! ### Integrating factors -/

/-- **Integrating-factor bound.** If `S` is absolutely continuous on `[R, X]` with `0 < R`, and
`S' − γ S/x ≤ k x^{β−1}` a.e. on `[R, X]`, where `γ < β`, then
`S(X) X^{−γ} − S(R) R^{−γ} ≤ k (X^{β−γ} − R^{β−γ})/(β − γ)`. -/
theorem sub_le_of_ae_deriv_sub_le_rpow {S : ℝ → ℝ} {R X γ β k : ℝ} (hR : 0 < R) (hRX : R ≤ X)
    (hγβ : γ < β) (hac : AbsolutelyContinuousOnInterval S R X)
    (hder : ∀ᵐ x, x ∈ Icc R X → deriv S x - γ * S x / x ≤ k * x ^ (β - 1)) :
    S X * X ^ (-γ) - S R * R ^ (-γ) ≤ k * (X ^ (β - γ) - R ^ (β - γ)) / (β - γ) := by
  have hpos : ∀ x ∈ uIcc R X, 0 < x := fun x hx => by
    rw [uIcc_of_le hRX] at hx
    exact hR.trans_le hx.1
  have h0 : (0 : ℝ) ∉ uIcc R X := fun h => lt_irrefl _ (hpos 0 h)
  have hw : AbsolutelyContinuousOnInterval (fun x : ℝ => x ^ (-γ)) R X := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    intro x hx
    exact (Real.contDiffAt_rpow_const_of_ne (hpos x hx).ne').contDiffWithinAt
  have hV : AbsolutelyContinuousOnInterval (fun x => S x * x ^ (-γ)) R X := hac.mul hw
  have hFTC := hV.integral_deriv_eq_sub
  have hbound : ∫ x in R..X, deriv (fun x => S x * x ^ (-γ)) x
      ≤ ∫ x in R..X, k * x ^ (β - 1 - γ) := by
    apply intervalIntegral.integral_mono_ae_restrict hRX hV.intervalIntegrable_deriv
      ((intervalIntegral.intervalIntegrable_rpow (Or.inr h0)).const_mul k)
    rw [EventuallyLE, ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hac.ae_differentiableAt, hder] with x hxd hxder hx
    have hx' : x ∈ uIcc R X := by rw [uIcc_of_le hRX]; exact hx
    have x0 := hpos x hx'
    have hdw : HasDerivAt (fun x : ℝ => x ^ (-γ)) (-γ * x ^ (-γ - 1)) x :=
      Real.hasDerivAt_rpow_const (Or.inl x0.ne')
    have hprod : deriv (fun x => S x * x ^ (-γ)) x
        = deriv S x * x ^ (-γ) + S x * (-γ * x ^ (-γ - 1)) :=
      ((hxd hx').hasDerivAt.mul hdw).deriv
    have hw0 : 0 < x ^ (-γ) := Real.rpow_pos_of_pos x0 _
    have hle := mul_le_mul_of_nonneg_left (hxder hx) hw0.le
    rw [hprod, Real.rpow_sub_one x0.ne', show β - 1 - γ = (β - 1) + (-γ) by ring,
      Real.rpow_add x0]
    calc deriv S x * x ^ (-γ) + S x * (-γ * (x ^ (-γ) / x))
        = x ^ (-γ) * (deriv S x - γ * S x / x) := by ring
      _ ≤ x ^ (-γ) * (k * x ^ (β - 1)) := hle
      _ = k * (x ^ (β - 1) * x ^ (-γ)) := by ring
  have hint : ∫ x in R..X, k * x ^ (β - 1 - γ) = k * (X ^ (β - γ) - R ^ (β - γ)) / (β - γ) := by
    rw [intervalIntegral.integral_const_mul,
      integral_rpow (Or.inr ⟨fun h => by linarith, h0⟩), show β - 1 - γ + 1 = β - γ by ring]
    ring
  calc S X * X ^ (-γ) - S R * R ^ (-γ)
      = ∫ x in R..X, deriv (fun x => S x * x ^ (-γ)) x := hFTC.symm
    _ ≤ _ := hbound
    _ = _ := hint

/-- **Integrating-factor bound, lower form.** If `S` is absolutely continuous on `[R, X]` with
`0 < R`, and `k x^{β−1} ≤ S' − γ S/x` a.e. on `[R, X]`, where `γ < β`, then
`k (X^{β−γ} − R^{β−γ})/(β − γ) ≤ S(X) X^{−γ} − S(R) R^{−γ}`. -/
theorem le_sub_of_ae_le_deriv_sub_rpow {S : ℝ → ℝ} {R X γ β k : ℝ} (hR : 0 < R) (hRX : R ≤ X)
    (hγβ : γ < β) (hac : AbsolutelyContinuousOnInterval S R X)
    (hder : ∀ᵐ x, x ∈ Icc R X → k * x ^ (β - 1) ≤ deriv S x - γ * S x / x) :
    k * (X ^ (β - γ) - R ^ (β - γ)) / (β - γ) ≤ S X * X ^ (-γ) - S R * R ^ (-γ) := by
  have h := sub_le_of_ae_deriv_sub_le_rpow (S := fun x => -S x) (k := -k) hR hRX hγβ hac.neg
    (by
      filter_upwards [hder] with x hx hxI
      have h1 := hx hxI
      rw [deriv.fun_neg]
      have e : γ * -S x / x = -(γ * S x / x) := by ring
      rw [e]
      linarith)
  have e2 : -k * (X ^ (β - γ) - R ^ (β - γ)) / (β - γ)
      = -(k * (X ^ (β - γ) - R ^ (β - γ)) / (β - γ)) := by ring
  rw [e2] at h
  linarith

/-! ### The asymptotic comparison lemma -/

/-- The bound `S/r^β ≤ D r^{γ−β} + K` from an integrating-factor estimate on `[R, X]`. -/
theorem div_rpow_le_of_sub_le {S : ℝ → ℝ} {R X γ β k : ℝ} (hX0 : 0 < X)
    (h : S X * X ^ (-γ) - S R * R ^ (-γ) ≤ k * (X ^ (β - γ) - R ^ (β - γ)) / (β - γ)) :
    S X / X ^ β ≤ (S R * R ^ (-γ) - k * R ^ (β - γ) / (β - γ)) * X ^ (γ - β) + k / (β - γ) := by
  have e1 : S X / X ^ β = (S X * X ^ (-γ)) * X ^ (γ - β) := by
    rw [mul_assoc, ← Real.rpow_add hX0, show -γ + (γ - β) = -β by ring,
      Real.rpow_neg hX0.le, div_eq_mul_inv]
  have e2 : X ^ (β - γ) * X ^ (γ - β) = 1 := by
    rw [← Real.rpow_add hX0, show β - γ + (γ - β) = 0 by ring, Real.rpow_zero]
  have hpX : 0 < X ^ (γ - β) := Real.rpow_pos_of_pos hX0 _
  rw [← sub_nonneg]
  have key : (S R * R ^ (-γ) - k * R ^ (β - γ) / (β - γ)) * X ^ (γ - β) + k / (β - γ)
      - S X / X ^ β
      = (k * (X ^ (β - γ) - R ^ (β - γ)) / (β - γ) - (S X * X ^ (-γ) - S R * R ^ (-γ)))
        * X ^ (γ - β) := by
    rw [e1]
    linear_combination (-k / (β - γ)) * e2
  rw [key]
  exact mul_nonneg (sub_nonneg.2 h) hpX.le

/-- The bound `D r^{γ−β} + K ≤ S/r^β` from a lower integrating-factor estimate. -/
theorem le_div_rpow_of_le_sub {S : ℝ → ℝ} {R X γ β k : ℝ} (hX0 : 0 < X)
    (h : k * (X ^ (β - γ) - R ^ (β - γ)) / (β - γ) ≤ S X * X ^ (-γ) - S R * R ^ (-γ)) :
    (S R * R ^ (-γ) - k * R ^ (β - γ) / (β - γ)) * X ^ (γ - β) + k / (β - γ) ≤ S X / X ^ β := by
  have h' := div_rpow_le_of_sub_le (S := fun x => -S x) (R := R) (k := -k) hX0
    (by
      have e : -k * (X ^ (β - γ) - R ^ (β - γ)) / (β - γ)
          = -(k * (X ^ (β - γ) - R ^ (β - γ)) / (β - γ)) := by ring
      rw [e]
      linarith)
  have e3 : -S X / X ^ β = -(S X / X ^ β) := by ring
  have e4 : (-S R * R ^ (-γ) - -k * R ^ (β - γ) / (β - γ)) * X ^ (γ - β) + -k / (β - γ)
      = -((S R * R ^ (-γ) - k * R ^ (β - γ) / (β - γ)) * X ^ (γ - β) + k / (β - γ)) := by ring
  rw [e3, e4] at h'
  linarith

/-- `D r^{γ−β} + K → K` when `γ < β`. -/
theorem tendsto_mul_rpow_add_of_lt {D K γ β : ℝ} (hγβ : γ < β) :
    Tendsto (fun X : ℝ => D * X ^ (γ - β) + K) atTop (𝓝 K) := by
  have h := tendsto_rpow_neg_atTop (sub_pos.2 hγβ)
  rw [show -(β - γ) = γ - β by ring] at h
  simpa using (h.const_mul D).add_const K

/-- **Asymptotic comparison for a linear differential equation.** Let `0 < r₀`, `q < β`, and
let `S ≥ 0` be absolutely continuous on every `[r₀, R]` with `S' = u S + g` a.e. on `[r₀, ∞)`.
If `r u(r) → q` and `g(r)/r^{β−1} → c`, then `S(r)/r^β → c/(β − q)`. -/
theorem tendsto_div_rpow_of_ae_deriv {S u g : ℝ → ℝ} {r₀ q β c : ℝ} (hr₀ : 0 < r₀)
    (hqβ : q < β) (hac : ∀ R, r₀ ≤ R → AbsolutelyContinuousOnInterval S r₀ R)
    (hnn : ∀ r, r₀ ≤ r → 0 ≤ S r)
    (hder : ∀ᵐ r, r₀ ≤ r → deriv S r = u r * S r + g r)
    (hu : Tendsto (fun r => r * u r) atTop (𝓝 q))
    (hg : Tendsto (fun r => g r / r ^ (β - 1)) atTop (𝓝 c)) :
    Tendsto (fun r => S r / r ^ β) atTop (𝓝 (c / (β - q))) := by
  have key : ∀ η, 0 < η → η < β - q →
      (∀ᶠ r in atTop, S r / r ^ β < (c + η) / (β - (q + η)) + η) ∧
      (∀ᶠ r in atTop, (c - η) / (β - (q - η)) - η < S r / r ^ β) := by
    intro η hη hηβ
    obtain ⟨R₁, hR₁⟩ := eventually_atTop.1
      ((hu.eventually (Icc_mem_nhds (by linarith : q - η < q) (by linarith : q < q + η))).and
        (hg.eventually (Icc_mem_nhds (by linarith : c - η < c) (by linarith : c < c + η))))
    set R := max R₁ r₀ with hRdef
    have hR0 : 0 < R := lt_of_lt_of_le hr₀ (le_max_right _ _)
    have hRr₀ : r₀ ≤ R := le_max_right _ _
    have hpt : ∀ᵐ x, R ≤ x →
        (q - η) * S x / x + (c - η) * x ^ (β - 1) ≤ deriv S x ∧
          deriv S x ≤ (q + η) * S x / x + (c + η) * x ^ (β - 1) := by
      filter_upwards [hder] with x hx hRx
      have hx0 : 0 < x := hR0.trans_le hRx
      have hxr : r₀ ≤ x := hRr₀.trans hRx
      obtain ⟨⟨hu1, hu2⟩, hg1, hg2⟩ := hR₁ x ((le_max_left _ _).trans hRx)
      have hSx := hnn x hxr
      have hpw : 0 < x ^ (β - 1) := Real.rpow_pos_of_pos hx0 _
      rw [hx hxr]
      have e1 : u x * S x = (x * u x) * S x / x := by
        rw [eq_div_iff hx0.ne']
        ring
      have hg1' : (c - η) * x ^ (β - 1) ≤ g x := by rwa [le_div_iff₀ hpw] at hg1
      have hg2' : g x ≤ (c + η) * x ^ (β - 1) := by rwa [div_le_iff₀ hpw] at hg2
      have hm1 : (q - η) * S x / x ≤ (x * u x) * S x / x :=
        (div_le_div_iff_of_pos_right hx0).2 (mul_le_mul_of_nonneg_right hu1 hSx)
      have hm2 : (x * u x) * S x / x ≤ (q + η) * S x / x :=
        (div_le_div_iff_of_pos_right hx0).2 (mul_le_mul_of_nonneg_right hu2 hSx)
      constructor <;> linarith
    have hacR : ∀ X, R ≤ X → AbsolutelyContinuousOnInterval S R X := fun X hRX =>
      (hac X (hRr₀.trans hRX)).mono (by
        rw [uIcc_of_le hRX, uIcc_of_le (hRr₀.trans hRX)]
        exact Icc_subset_Icc_left hRr₀)
    constructor
    · have hγ : q + η < β := by linarith
      have hbd : ∀ X, R ≤ X → S X / X ^ β ≤
          (S R * R ^ (-(q + η)) - (c + η) * R ^ (β - (q + η)) / (β - (q + η)))
            * X ^ ((q + η) - β) + (c + η) / (β - (q + η)) := by
        intro X hRX
        refine div_rpow_le_of_sub_le (hR0.trans_le hRX) ?_
        refine sub_le_of_ae_deriv_sub_le_rpow hR0 hRX hγ (hacR X hRX) ?_
        filter_upwards [hpt] with x hx hxI
        have := (hx hxI.1).2
        linarith
      filter_upwards [eventually_ge_atTop R, (tendsto_mul_rpow_add_of_lt hγ).eventually
        (gt_mem_nhds (lt_add_of_pos_right ((c + η) / (β - (q + η))) hη))] with X hX hlim
      exact (hbd X hX).trans_lt hlim
    · have hγ : q - η < β := by linarith
      have hbd : ∀ X, R ≤ X →
          (S R * R ^ (-(q - η)) - (c - η) * R ^ (β - (q - η)) / (β - (q - η)))
            * X ^ ((q - η) - β) + (c - η) / (β - (q - η)) ≤ S X / X ^ β := by
        intro X hRX
        refine le_div_rpow_of_le_sub (hR0.trans_le hRX) ?_
        refine le_sub_of_ae_le_deriv_sub_rpow hR0 hRX hγ (hacR X hRX) ?_
        filter_upwards [hpt] with x hx hxI
        have := (hx hxI.1).1
        linarith
      filter_upwards [eventually_ge_atTop R, (tendsto_mul_rpow_add_of_lt hγ).eventually
        (lt_mem_nhds (sub_lt_self ((c - η) / (β - (q - η))) hη))] with X hX hlim
      exact hlim.trans_le (hbd X hX)
  have hb : 0 < β - q := sub_pos.2 hqβ
  have hU : Tendsto (fun η => (c + η) / (β - (q + η)) + η) (𝓝 0) (𝓝 (c / (β - q))) := by
    have : ContinuousAt (fun η : ℝ => (c + η) / (β - (q + η)) + η) 0 := by
      refine ContinuousAt.add (ContinuousAt.div (by fun_prop) (by fun_prop) ?_) continuousAt_id
      simp only [add_zero]
      exact hb.ne'
    simpa using this.tendsto
  have hL : Tendsto (fun η => (c - η) / (β - (q - η)) - η) (𝓝 0) (𝓝 (c / (β - q))) := by
    have : ContinuousAt (fun η : ℝ => (c - η) / (β - (q - η)) - η) 0 := by
      refine ContinuousAt.sub (ContinuousAt.div (by fun_prop) (by fun_prop) ?_) continuousAt_id
      simp only [sub_zero]
      exact hb.ne'
    simpa using this.tendsto
  rw [tendsto_order]
  constructor
  · intro a' ha'
    obtain ⟨η, h1, h2, h3⟩ :=
      (((hL.eventually (lt_mem_nhds ha')).filter_mono nhdsWithin_le_nhds).and
        (Ioo_mem_nhdsGT hb)).exists
    filter_upwards [(key η h2 h3).2] with r hr
    linarith
  · intro a' ha'
    obtain ⟨η, h1, h2, h3⟩ :=
      (((hU.eventually (gt_mem_nhds ha')).filter_mono nhdsWithin_le_nhds).and
        (Ioo_mem_nhdsGT hb)).exists
    filter_upwards [(key η h2 h3).1] with r hr
    linarith

/-! ### Ratios and asymptotic equivalence -/

/-- If `f ~ k r^γ`, then `f(r)/r^γ → k`. -/
theorem tendsto_div_rpow_of_isEquivalent {f : ℝ → ℝ} {k γ : ℝ}
    (h : f ~[atTop] fun r => k * r ^ γ) : Tendsto (fun r => f r / r ^ γ) atTop (𝓝 k) := by
  have h2 := h.div (IsEquivalent.refl (u := fun r : ℝ => r ^ γ))
  refine h2.symm.tendsto_nhds (tendsto_const_nhds.congr' ?_)
  filter_upwards [eventually_gt_atTop 0] with r hr
  simp only [Pi.div_apply]
  rw [mul_div_assoc, div_self (Real.rpow_pos_of_pos hr _).ne', mul_one]

/-- Two functions with the same nonzero limit of `·/r^γ` are asymptotically equivalent. -/
theorem isEquivalent_of_tendsto_div_rpow {f h : ℝ → ℝ} {k γ : ℝ} (hk : k ≠ 0)
    (hf : Tendsto (fun r => f r / r ^ γ) atTop (𝓝 k))
    (hh : Tendsto (fun r => h r / r ^ γ) atTop (𝓝 k)) : f ~[atTop] h := by
  apply isEquivalent_of_tendsto_one
  have h1 := hf.div hh hk
  rw [div_self hk] at h1
  refine h1.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with r hr
  simp only [Pi.div_apply]
  rw [div_div_div_cancel_right₀ (Real.rpow_pos_of_pos hr γ).ne']

/-- The middle terms of Lemma I.4.23: for `n = k + 3`,
`∑_{ℓ<k+1} C(k+3, ℓ+1) (2ℓ+1)‼ (2k+1−2ℓ)‼ = (k+1)(2k+3)‼`. -/
theorem sum_choose_doubleFactorial_middle (k : ℕ) :
    ∑ ℓ ∈ Finset.range (k + 1), (k + 3).choose (ℓ + 1) * (2 * (ℓ + 1 + 1) - 3)‼ *
      (2 * (k + 3 - (ℓ + 1)) - 3)‼ = (k + 1) * (2 * (k + 3) - 3)‼ := by
  have h := PercLib.Combinatorics.lemma_I_4_23 (k + 3) (by omega)
  rw [Finset.sum_range_succ, Finset.sum_range_succ'] at h
  have hmid : ∑ ℓ ∈ Finset.range (k + 1), (k + 3).choose (ℓ + 1) * (2 * (ℓ + 1 + 1) - 3)‼ *
      (2 * (k + 3 - (ℓ + 1)) - 3)‼ = ∑ ℓ ∈ Finset.range (k + 1), (k + 3).choose (ℓ + 1) *
      (2 * (ℓ + 1) - 1)‼ * (2 * (k + 3) - 2 * (ℓ + 1) - 3)‼ := by
    refine Finset.sum_congr rfl fun ℓ hℓ => ?_
    have := Finset.mem_range.1 hℓ
    rw [show 2 * (ℓ + 1 + 1) - 3 = 2 * (ℓ + 1) - 1 by omega,
      show 2 * (k + 3 - (ℓ + 1)) - 3 = 2 * (k + 3) - 2 * (ℓ + 1) - 3 by omega]
  have hA : (k + 3).choose 0 * (2 * 0 - 1)‼ * (2 * (k + 3) - 2 * 0 - 3)‼ = (2 * k + 3)‼ := by
    rw [show 2 * (k + 3) - 2 * 0 - 3 = 2 * k + 3 by omega]
    simp
  have hch : (k + 3).choose (k + 2) = k + 3 := Nat.choose_succ_self_right (k + 2)
  have hB : (k + 3).choose (k + 2) * (2 * (k + 2) - 1)‼ * (2 * (k + 3) - 2 * (k + 2) - 3)‼
      = (k + 3) * (2 * k + 3)‼ := by
    rw [show 2 * (k + 2) - 1 = 2 * k + 3 by omega,
      show 2 * (k + 3) - 2 * (k + 2) - 3 = 0 by omega, hch]
    simp
  have hC : (2 * (k + 3) - 1)‼ = (2 * k + 3 + 2) * (2 * k + 3)‼ := by
    rw [show 2 * (k + 3) - 1 = 2 * k + 3 + 2 by omega, Nat.doubleFactorial_add_two]
  rw [hA, hB, hC, ← hmid] at h
  rw [show 2 * (k + 3) - 3 = 2 * k + 3 by omega]
  have h2 : (∑ ℓ ∈ Finset.range (k + 1), (k + 3).choose (ℓ + 1) * (2 * (ℓ + 1 + 1) - 3)‼ *
      (2 * (k + 3 - (ℓ + 1)) - 3)‼) + ((2 * k + 3)‼ + (k + 3) * (2 * k + 3)‼)
      = (k + 1) * (2 * k + 3)‼ + ((2 * k + 3)‼ + (k + 3) * (2 * k + 3)‼) := by
    rw [← add_assoc, h]
    ring
  exact Nat.add_right_cancel h2

/-! ### The moment hierarchy -/

/-- **Double-factorial asymptotics from a closed moment hierarchy (5O1G).** Let `r₀, α, B, C > 0`
and let `m₁, …, m_P > 0` on `[r₀, ∞)` be absolutely continuous on every `[r₀, R]`. Suppose
`m₁ ~ B r^α`, `m₂ ~ C r^{3α}`, `a ~ (α/B) r^{−α−1}`, and for `3 ≤ p ≤ P` there are `ε_p → 0`
with `m_p' = (1 + ε_p) a ∑_{ℓ=0}^{p−1} C(p,ℓ) m_{ℓ+1} m_{p−ℓ}` a.e. on `[r₀, ∞)`. Then
`m_p ~ (2p−3)‼ (m₂/m₁)^{p−1} m₁` for every `1 ≤ p ≤ P` (with `(−1)‼ = 1`). -/
@[tag "5O1G"]
theorem isEquivalent_moment_hierarchy {P : ℕ} {r₀ α B C : ℝ} (hr₀ : 0 < r₀) (hα : 0 < α)
    (hB : 0 < B) (hC : 0 < C) {m : ℕ → ℝ → ℝ} {a : ℝ → ℝ} {ε : ℕ → ℝ → ℝ}
    (hm_pos : ∀ p, 1 ≤ p → p ≤ P → ∀ r, r₀ ≤ r → 0 < m p r)
    (hm_ac : ∀ p, 1 ≤ p → p ≤ P → ∀ R, r₀ ≤ R → AbsolutelyContinuousOnInterval (m p) r₀ R)
    (hm1 : m 1 ~[atTop] fun r => B * r ^ α)
    (hm2 : m 2 ~[atTop] fun r => C * r ^ (3 * α))
    (ha : a ~[atTop] fun r => α / B * r ^ (-α - 1))
    (hε : ∀ p, 3 ≤ p → p ≤ P → Tendsto (ε p) atTop (𝓝 0))
    (hder : ∀ p, 3 ≤ p → p ≤ P → ∀ᵐ r, r₀ ≤ r →
      deriv (m p) r = (1 + ε p r) * a r *
        ∑ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ) * m (ℓ + 1) r * m (p - ℓ) r) :
    ∀ p, 1 ≤ p → p ≤ P →
      m p ~[atTop] fun r => ((2 * p - 3)‼ : ℝ) * (m 2 r / m 1 r) ^ (p - 1) * m 1 r := by
  set e : ℕ → ℝ := fun n => (2 * (n : ℝ) - 1) * α with he
  set c : ℕ → ℝ := fun n => ((2 * n - 3)‼ : ℝ) * C ^ (n - 1) * B / B ^ (n - 1) with hc
  have hc_pos : ∀ n, 0 < c n := fun n => by
    simp only [hc]
    have := Nat.doubleFactorial_pos (2 * n - 3)
    positivity
  have hA := tendsto_div_rpow_of_isEquivalent ha
  have claim : ∀ p, 1 ≤ p → p ≤ P → Tendsto (fun r => m p r / r ^ e p) atTop (𝓝 (c p)) := by
    intro p
    induction p using Nat.strong_induction_on with
    | _ p ih =>
    intro hp1 hpP
    obtain rfl | rfl | ⟨k, rfl⟩ : p = 1 ∨ p = 2 ∨ ∃ k, p = k + 3 := by
      rcases p with _ | _ | _ | k
      · omega
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr ⟨k, by omega⟩)
    · have h1e : e 1 = α := by simp only [he]; norm_num
      have h1c : c 1 = B := by simp only [hc]; norm_num
      rw [h1e, h1c]
      exact tendsto_div_rpow_of_isEquivalent hm1
    · have h2e : e 2 = 3 * α := by simp only [he]; norm_num
      have h2c : c 2 = C := by simp only [hc]; norm_num; field_simp
      rw [h2e, h2c]
      exact tendsto_div_rpow_of_isEquivalent hm2
    · have hP : k + 3 ≤ P := hpP
      have hM1 := ih 1 (by omega) le_rfl (by omega)
      have h1e : e 1 = α := by simp only [he]; norm_num
      have h1c : c 1 = B := by simp only [hc]; norm_num
      rw [h1e, h1c] at hM1
      -- the coefficient `u` and the source `g`
      have hrel : Tendsto (fun r => r * a r * m 1 r) atTop (𝓝 α) := by
        have h := hA.mul hM1
        rw [div_mul_cancel₀ α hB.ne'] at h
        refine h.congr' ?_
        filter_upwards [eventually_gt_atTop 0] with r hr
        have hpw : r ^ (-α - 1) * r ^ α * r = 1 := by
          rw [← Real.rpow_add hr, show -α - 1 + α = -1 by ring, Real.rpow_neg_one,
            inv_mul_cancel₀ hr.ne']
        have hA0 := (Real.rpow_pos_of_pos hr (-α - 1)).ne'
        have hM0 := (Real.rpow_pos_of_pos hr α).ne'
        rw [div_mul_div_comm, div_eq_iff (mul_ne_zero hA0 hM0)]
        linear_combination (-(a r * m 1 r)) * hpw
      have hu : Tendsto (fun r => r * ((1 + ε (k + 3) r) * a r * (((k : ℝ) + 4) * m 1 r)))
          atTop (𝓝 (((k : ℝ) + 4) * α)) := by
        have h := (((tendsto_const_nhds (x := (1 : ℝ))).add (hε (k + 3) (by omega) hP)).mul_const
          ((k : ℝ) + 4)).mul hrel
        rw [add_zero, one_mul] at h
        refine h.congr' (Eventually.of_forall fun r => ?_)
        ring
      set c' : ℝ := (1 + 0) * (α / B) * ∑ ℓ ∈ Finset.range (k + 1),
        ((k + 3).choose (ℓ + 1) : ℝ) * c (ℓ + 1 + 1) * c (k + 3 - (ℓ + 1)) with hc'
      have hg : Tendsto (fun r => ((1 + ε (k + 3) r) * a r * ∑ ℓ ∈ Finset.range (k + 1),
          ((k + 3).choose (ℓ + 1) : ℝ) * m (ℓ + 1 + 1) r * m (k + 3 - (ℓ + 1)) r) /
            r ^ (e (k + 3) - 1)) atTop (𝓝 c') := by
        have hsum : Tendsto (fun r => ∑ ℓ ∈ Finset.range (k + 1),
            ((k + 3).choose (ℓ + 1) : ℝ) * (m (ℓ + 1 + 1) r / r ^ e (ℓ + 1 + 1)) *
              (m (k + 3 - (ℓ + 1)) r / r ^ e (k + 3 - (ℓ + 1)))) atTop
            (𝓝 (∑ ℓ ∈ Finset.range (k + 1),
              ((k + 3).choose (ℓ + 1) : ℝ) * c (ℓ + 1 + 1) * c (k + 3 - (ℓ + 1)))) := by
          refine tendsto_finsetSum _ fun ℓ hℓ => ?_
          have hℓ' := Finset.mem_range.1 hℓ
          exact (tendsto_const_nhds.mul (ih (ℓ + 1 + 1) (by omega) (by omega) (by omega))).mul
            (ih (k + 3 - (ℓ + 1)) (by omega) (by omega) (by omega))
        have h := (((tendsto_const_nhds (x := (1 : ℝ))).add (hε (k + 3) (by omega) hP)).mul
            hA).mul hsum
        refine h.congr' ?_
        filter_upwards [eventually_gt_atTop 0] with r hr
        simp only [Finset.mul_sum, Finset.sum_div]
        refine Finset.sum_congr rfl fun ℓ hℓ => ?_
        have hℓ' := Finset.mem_range.1 hℓ
        have hexp : e (k + 3) - 1 = (-α - 1) + e (ℓ + 1 + 1) + e (k + 3 - (ℓ + 1)) := by
          simp only [he]
          rw [Nat.cast_sub (by omega)]
          push_cast
          ring
        have h1 := (Real.rpow_pos_of_pos hr (-α - 1)).ne'
        have h2 := (Real.rpow_pos_of_pos hr (e (ℓ + 1 + 1))).ne'
        have h3 := (Real.rpow_pos_of_pos hr (e (k + 3 - (ℓ + 1)))).ne'
        rw [hexp, Real.rpow_add hr, Real.rpow_add hr]
        field_simp
      have hqβ : ((k : ℝ) + 4) * α < e (k + 3) := by
        simp only [he]
        push_cast
        nlinarith
      have hkey := tendsto_div_rpow_of_ae_deriv (S := m (k + 3)) hr₀ hqβ
        (hm_ac (k + 3) (by omega) hP) (fun r hr => (hm_pos (k + 3) (by omega) hP r hr).le)
        (by
          filter_upwards [hder (k + 3) (by omega) hP] with r hr hr0
          rw [hr hr0, Finset.sum_range_succ, Finset.sum_range_succ']
          have hch : ((k + 3).choose (k + 2) : ℝ) = (k : ℝ) + 3 := by
            rw [show (k + 3).choose (k + 2) = k + 3 from Nat.choose_succ_self_right (k + 2)]
            push_cast
            ring
          rw [hch, show k + 3 - (k + 2) = 1 by omega, show k + 2 + 1 = k + 3 by omega]
          simp only [Nat.choose_zero_right, Nat.cast_one, zero_add, Nat.sub_zero]
          ring) hu hg
      have hconst : c' / (e (k + 3) - ((k : ℝ) + 4) * α) = c (k + 3) := by
        have hterm : ∀ ℓ ∈ Finset.range (k + 1),
            ((k + 3).choose (ℓ + 1) : ℝ) * c (ℓ + 1 + 1) * c (k + 3 - (ℓ + 1))
              = (C ^ (k + 2) * B ^ 2 / B ^ (k + 2)) * (((k + 3).choose (ℓ + 1) *
                (2 * (ℓ + 1 + 1) - 3)‼ * (2 * (k + 3 - (ℓ + 1)) - 3)‼ : ℕ) : ℝ) := by
          intro ℓ hℓ
          have hℓ' := Finset.mem_range.1 hℓ
          obtain ⟨j, rfl⟩ : ∃ j, k = ℓ + j := ⟨k - ℓ, by omega⟩
          rw [show ℓ + j + 3 - (ℓ + 1) = j + 2 by omega]
          simp only [hc]
          rw [show ℓ + 1 + 1 - 1 = ℓ + 1 by omega, show j + 2 - 1 = j + 1 by omega,
            show ℓ + j + 2 = (ℓ + 1) + (j + 1) by omega]
          push_cast
          rw [pow_add, pow_add]
          field_simp
          ring
        rw [hc', Finset.sum_congr rfl hterm, ← Finset.mul_sum, ← Nat.cast_sum,
          sum_choose_doubleFactorial_middle]
        have hden : e (k + 3) - ((k : ℝ) + 4) * α = ((k : ℝ) + 1) * α := by
          simp only [he]
          push_cast
          ring
        rw [hden]
        simp only [hc]
        rw [show k + 3 - 1 = k + 2 by omega]
        push_cast
        field_simp
        norm_num
      rw [hconst] at hkey
      exact hkey
  intro p hp1 hpP
  obtain rfl | hp2 := eq_or_lt_of_le hp1
  · simp only [Nat.sub_self, pow_zero, mul_one]
    norm_num
    exact IsEquivalent.refl
  refine isEquivalent_of_tendsto_div_rpow (hc_pos p).ne' (claim p hp1 hpP) ?_
  have h1 := claim 1 le_rfl (by omega)
  have h2 := claim 2 (by omega) (by omega)
  have h := (tendsto_const_nhds (x := ((2 * p - 3)‼ : ℝ))).mul
    (((h2.div h1 (hc_pos 1).ne').pow (p - 1)).mul h1)
  have hval : ((2 * p - 3)‼ : ℝ) * ((c 2 / c 1) ^ (p - 1) * c 1) = c p := by
    simp only [hc]
    norm_num
    field_simp
    rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero _ hB.ne')]
  rw [hval] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with r hr
  have hX : r ^ e p = (r ^ e 2 / r ^ e 1) ^ (p - 1) * r ^ e 1 := by
    rw [← Real.rpow_sub hr, ← Real.rpow_natCast, ← Real.rpow_mul hr.le, ← Real.rpow_add hr]
    congr 1
    simp only [he]
    rw [Nat.cast_sub hp1]
    push_cast
    ring
  simp only [Pi.div_apply]
  rw [hX, div_div_div_comm, div_pow]
  ring

/-! ### Slowly varying corrections (OBTO) -/

/-- If `f ~ k w` and `w ≠ 0` eventually, then `f/w → k`. -/
theorem tendsto_div_of_isEquivalent_const_mul {f w : ℝ → ℝ} {k : ℝ}
    (hw : ∀ᶠ r in atTop, w r ≠ 0) (h : f ~[atTop] fun r => k * w r) :
    Tendsto (fun r => f r / w r) atTop (𝓝 k) := by
  have h2 := h.div (IsEquivalent.refl (u := w))
  refine h2.symm.tendsto_nhds (tendsto_const_nhds.congr' ?_)
  filter_upwards [hw] with r hr
  simp only [Pi.div_apply]
  rw [mul_div_assoc, div_self hr, mul_one]

/-- Two functions with the same nonzero limit of `·/w` are asymptotically equivalent. -/
theorem isEquivalent_of_tendsto_div {f h w : ℝ → ℝ} {k : ℝ} (hk : k ≠ 0)
    (hw : ∀ᶠ r in atTop, w r ≠ 0)
    (hf : Tendsto (fun r => f r / w r) atTop (𝓝 k))
    (hh : Tendsto (fun r => h r / w r) atTop (𝓝 k)) : f ~[atTop] h := by
  apply isEquivalent_of_tendsto_one
  have h1 := hf.div hh hk
  rw [div_self hk] at h1
  refine h1.congr' ?_
  filter_upwards [hw] with r hr
  simp only [Pi.div_apply]
  rw [div_div_div_cancel_right₀ hr]

/-- **Asymptotic comparison with a slowly varying factor.** As
`tendsto_div_rpow_of_ae_deriv`, with a positive factor `Λ` that is `C¹` on `[R_L, ∞)` and
satisfies `r Λ'(r)/Λ(r) → 0`: if `g(r)/(r^{β−1} Λ(r)) → c`, then
`S(r)/(r^β Λ(r)) → c/(β − q)`. -/
theorem tendsto_div_rpow_mul_of_ae_deriv {S u g Λ : ℝ → ℝ} {r₀ R_L q β c : ℝ} (hr₀ : 0 < r₀)
    (hqβ : q < β) (hac : ∀ R, r₀ ≤ R → AbsolutelyContinuousOnInterval S r₀ R)
    (hnn : ∀ r, r₀ ≤ r → 0 ≤ S r)
    (hder : ∀ᵐ r, r₀ ≤ r → deriv S r = u r * S r + g r)
    (hΛ : ContDiffOn ℝ 1 Λ (Ici R_L)) (hΛpos : ∀ r, 0 < Λ r)
    (hΛslow : Tendsto (fun r => r * deriv Λ r / Λ r) atTop (𝓝 0))
    (hu : Tendsto (fun r => r * u r) atTop (𝓝 q))
    (hg : Tendsto (fun r => g r / (r ^ (β - 1) * Λ r)) atTop (𝓝 c)) :
    Tendsto (fun r => S r / (r ^ β * Λ r)) atTop (𝓝 (c / (β - q))) := by
  set r₁ := max r₀ (R_L + 1) with hr₁eq
  have hr₁ : 0 < r₁ := hr₀.trans_le (le_max_left _ _)
  have hr₀₁ : r₀ ≤ r₁ := le_max_left _ _
  have hL₁ : R_L + 1 ≤ r₁ := le_max_right _ _
  have hdiff : ∀ᵐ x, r₀ ≤ x → DifferentiableAt ℝ S x := by
    have h : ∀ n : ℕ, ∀ᵐ x, x ∈ uIcc r₀ (max r₀ n) → DifferentiableAt ℝ S x :=
      fun n => (hac _ (le_max_left _ _)).ae_differentiableAt
    filter_upwards [ae_all_iff.2 h] with x hx hx0
    apply hx ⌈x⌉₊
    rw [uIcc_of_le (le_max_left _ _)]
    exact ⟨hx0, le_max_of_le_right (Nat.le_ceil x)⟩
  have hΛd : ∀ x, R_L < x → HasDerivAt Λ (deriv Λ x) x := fun x hx =>
    ((hΛ.contDiffAt (Ici_mem_nhds hx)).differentiableAt one_ne_zero).hasDerivAt
  have key := tendsto_div_rpow_of_ae_deriv (S := fun r => S r * (Λ r)⁻¹)
    (u := fun r => u r - deriv Λ r / Λ r) (g := fun r => g r / Λ r) (c := c) hr₁ hqβ
    (fun R hR => by
      have hsub : uIcc r₁ R ⊆ uIcc r₀ R := by
        rw [uIcc_of_le hR, uIcc_of_le (hr₀₁.trans hR)]
        exact Icc_subset_Icc_left hr₀₁
      have hS := (hac R (hr₀₁.trans hR)).mono hsub
      have hinv : AbsolutelyContinuousOnInterval (fun r => (Λ r)⁻¹) r₁ R := by
        apply ContDiffOn.absolutelyContinuousOnInterval
        refine (hΛ.mono ?_).inv fun x _ => (hΛpos x).ne'
        rw [uIcc_of_le hR]
        intro x hx
        exact (show R_L ≤ x by linarith [hx.1])
      exact hS.mul hinv)
    (fun r hr => mul_nonneg (hnn r (hr₀₁.trans hr)) (inv_nonneg.2 (hΛpos r).le))
    (by
      filter_upwards [hder, hdiff] with x h1 h2 hx
      have hS := (h2 (hr₀₁.trans hx)).hasDerivAt
      have hL := hΛd x (by linarith)
      have hx0 := (hΛpos x).ne'
      have hd : HasDerivAt (fun r => S r * (Λ r)⁻¹)
          (deriv S x * (Λ x)⁻¹ + S x * (-deriv Λ x / Λ x ^ 2)) x := hS.mul (hL.inv hx0)
      rw [hd.deriv, h1 (hr₀₁.trans hx)]
      field_simp
      ring)
    (by
      have h := hu.sub hΛslow
      rw [sub_zero] at h
      exact h.congr' (Eventually.of_forall fun r => by ring))
    (hg.congr' (Eventually.of_forall fun r => by
      change _ = g r / Λ r / r ^ (β - 1)
      rw [div_div, mul_comm]))
  exact key.congr' (Eventually.of_forall fun r => by simp only; ring)

/-- The constant of the hierarchy: with `c n = (2n−3)‼ C^{n−1} B / B^{n−1}`,
`(α/B) ∑_{ℓ<k+1} C(k+3, ℓ+1) c(ℓ+2) c(k+2−ℓ) / ((k+1)α) = c(k+3)`. -/
theorem moment_hierarchy_constant (k : ℕ) {α B C : ℝ} (hα : α ≠ 0) (hB : B ≠ 0)
    (c : ℕ → ℝ) (hc : ∀ n, c n = ((2 * n - 3)‼ : ℝ) * C ^ (n - 1) * B / B ^ (n - 1)) :
    (1 + 0) * (α / B) * (∑ ℓ ∈ Finset.range (k + 1),
        ((k + 3).choose (ℓ + 1) : ℝ) * c (ℓ + 1 + 1) * c (k + 3 - (ℓ + 1))) /
      ((2 * ((k + 3 : ℕ) : ℝ) - 1) * α - ((k : ℝ) + 4) * α) = c (k + 3) := by
  have hterm : ∀ ℓ ∈ Finset.range (k + 1),
      ((k + 3).choose (ℓ + 1) : ℝ) * c (ℓ + 1 + 1) * c (k + 3 - (ℓ + 1))
        = (C ^ (k + 2) * B ^ 2 / B ^ (k + 2)) * (((k + 3).choose (ℓ + 1) *
          (2 * (ℓ + 1 + 1) - 3)‼ * (2 * (k + 3 - (ℓ + 1)) - 3)‼ : ℕ) : ℝ) := by
    intro ℓ hℓ
    have hℓ' := Finset.mem_range.1 hℓ
    obtain ⟨j, rfl⟩ : ∃ j, k = ℓ + j := ⟨k - ℓ, by omega⟩
    rw [show ℓ + j + 3 - (ℓ + 1) = j + 2 by omega, hc, hc]
    rw [show ℓ + 1 + 1 - 1 = ℓ + 1 by omega, show j + 2 - 1 = j + 1 by omega,
      show ℓ + j + 2 = (ℓ + 1) + (j + 1) by omega]
    push_cast
    rw [pow_add, pow_add]
    field_simp
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, ← Nat.cast_sum,
    sum_choose_doubleFactorial_middle]
  have hden : (2 * ((k + 3 : ℕ) : ℝ) - 1) * α - ((k : ℝ) + 4) * α = ((k : ℝ) + 1) * α := by
    push_cast
    ring
  rw [hden, hc, show k + 3 - 1 = k + 2 by omega]
  push_cast
  field_simp
  norm_num

/-- **Moment hierarchy with a slowly varying correction.** As
`isEquivalent_moment_hierarchy`, but with `m₂ ~ C r^{3α} L(r)`, where `L > 0` is `C¹` on
`[R_L, ∞)` and `r L'(r)/L(r) → 0`. Then for every `1 ≤ p ≤ P`,
`m_p ~ (2p−3)‼ C^{p−1} B^{2−p} r^{(2p−1)α} L(r)^{p−1}`. -/
theorem isEquivalent_moment_hierarchy_slowlyVarying {P : ℕ} {r₀ α B C R_L : ℝ} (hr₀ : 0 < r₀)
    (hα : 0 < α) (hB : 0 < B) (hC : 0 < C) {m : ℕ → ℝ → ℝ} {a L : ℝ → ℝ} {ε : ℕ → ℝ → ℝ}
    (hm_pos : ∀ p, 1 ≤ p → p ≤ P → ∀ r, r₀ ≤ r → 0 < m p r)
    (hm_ac : ∀ p, 1 ≤ p → p ≤ P → ∀ R, r₀ ≤ R → AbsolutelyContinuousOnInterval (m p) r₀ R)
    (hL_pos : ∀ r, 0 < L r) (hL : ContDiffOn ℝ 1 L (Ici R_L))
    (hL_slow : Tendsto (fun r => r * deriv L r / L r) atTop (𝓝 0))
    (hm1 : m 1 ~[atTop] fun r => B * r ^ α)
    (hm2 : m 2 ~[atTop] fun r => C * r ^ (3 * α) * L r)
    (ha : a ~[atTop] fun r => α / B * r ^ (-α - 1))
    (hε : ∀ p, 3 ≤ p → p ≤ P → Tendsto (ε p) atTop (𝓝 0))
    (hder : ∀ p, 3 ≤ p → p ≤ P → ∀ᵐ r, r₀ ≤ r →
      deriv (m p) r = (1 + ε p r) * a r *
        ∑ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ) * m (ℓ + 1) r * m (p - ℓ) r) :
    ∀ p, 1 ≤ p → p ≤ P →
      m p ~[atTop] fun r => ((2 * p - 3)‼ : ℝ) * C ^ (p - 1) * B ^ (2 - (p : ℤ)) *
        r ^ ((2 * (p : ℝ) - 1) * α) * L r ^ (p - 1) := by
  set e : ℕ → ℝ := fun n => (2 * (n : ℝ) - 1) * α with he
  set c : ℕ → ℝ := fun n => ((2 * n - 3)‼ : ℝ) * C ^ (n - 1) * B / B ^ (n - 1) with hc
  have hc_pos : ∀ n, 0 < c n := fun n => by
    simp only [hc]
    have := Nat.doubleFactorial_pos (2 * n - 3)
    positivity
  have hA := tendsto_div_rpow_of_isEquivalent ha
  have hw : ∀ n : ℕ, ∀ᶠ r in atTop, r ^ e n * L r ^ (n - 1) ≠ 0 := fun n => by
    filter_upwards [eventually_gt_atTop 0] with r hr
    exact mul_ne_zero (Real.rpow_pos_of_pos hr _).ne' (pow_pos (hL_pos r) _).ne'
  have claim : ∀ p, 1 ≤ p → p ≤ P →
      Tendsto (fun r => m p r / (r ^ e p * L r ^ (p - 1))) atTop (𝓝 (c p)) := by
    intro p
    induction p using Nat.strong_induction_on with
    | _ p ih =>
    intro hp1 hpP
    obtain rfl | rfl | ⟨k, rfl⟩ : p = 1 ∨ p = 2 ∨ ∃ k, p = k + 3 := by
      rcases p with _ | _ | _ | k
      · omega
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr ⟨k, by omega⟩)
    · have h1e : e 1 = α := by simp only [he]; norm_num
      have h1c : c 1 = B := by simp only [hc]; norm_num
      rw [h1e, h1c]
      simpa using tendsto_div_rpow_of_isEquivalent hm1
    · have h2e : e 2 = 3 * α := by simp only [he]; norm_num
      have h2c : c 2 = C := by simp only [hc]; norm_num; field_simp
      rw [h2e, h2c]
      have hw2 := hw 2
      rw [h2e] at hw2
      simpa using tendsto_div_of_isEquivalent_const_mul hw2
        (hm2.congr_right (Eventually.of_forall fun r => by simp only; ring))
    · have hP : k + 3 ≤ P := hpP
      have hM1 := ih 1 (by omega) le_rfl (by omega)
      have h1e : e 1 = α := by simp only [he]; norm_num
      have h1c : c 1 = B := by simp only [hc]; norm_num
      rw [h1e, h1c] at hM1
      simp only [Nat.sub_self, pow_zero, mul_one] at hM1
      have hrel : Tendsto (fun r => r * a r * m 1 r) atTop (𝓝 α) := by
        have h := hA.mul hM1
        rw [div_mul_cancel₀ α hB.ne'] at h
        refine h.congr' ?_
        filter_upwards [eventually_gt_atTop 0] with r hr
        have hpw : r ^ (-α - 1) * r ^ α * r = 1 := by
          rw [← Real.rpow_add hr, show -α - 1 + α = -1 by ring, Real.rpow_neg_one,
            inv_mul_cancel₀ hr.ne']
        have hA0 := (Real.rpow_pos_of_pos hr (-α - 1)).ne'
        have hM0 := (Real.rpow_pos_of_pos hr α).ne'
        rw [div_mul_div_comm, div_eq_iff (mul_ne_zero hA0 hM0)]
        linear_combination (-(a r * m 1 r)) * hpw
      have hu : Tendsto (fun r => r * ((1 + ε (k + 3) r) * a r * (((k : ℝ) + 4) * m 1 r)))
          atTop (𝓝 (((k : ℝ) + 4) * α)) := by
        have h := (((tendsto_const_nhds (x := (1 : ℝ))).add (hε (k + 3) (by omega) hP)).mul_const
          ((k : ℝ) + 4)).mul hrel
        rw [add_zero, one_mul] at h
        refine h.congr' (Eventually.of_forall fun r => ?_)
        ring
      set c' : ℝ := (1 + 0) * (α / B) * ∑ ℓ ∈ Finset.range (k + 1),
        ((k + 3).choose (ℓ + 1) : ℝ) * c (ℓ + 1 + 1) * c (k + 3 - (ℓ + 1)) with hc'
      have hg : Tendsto (fun r => ((1 + ε (k + 3) r) * a r * ∑ ℓ ∈ Finset.range (k + 1),
          ((k + 3).choose (ℓ + 1) : ℝ) * m (ℓ + 1 + 1) r * m (k + 3 - (ℓ + 1)) r) /
            (r ^ (e (k + 3) - 1) * L r ^ (k + 2))) atTop (𝓝 c') := by
        have hsum : Tendsto (fun r => ∑ ℓ ∈ Finset.range (k + 1),
            ((k + 3).choose (ℓ + 1) : ℝ) *
              (m (ℓ + 1 + 1) r / (r ^ e (ℓ + 1 + 1) * L r ^ (ℓ + 1 + 1 - 1))) *
              (m (k + 3 - (ℓ + 1)) r /
                (r ^ e (k + 3 - (ℓ + 1)) * L r ^ (k + 3 - (ℓ + 1) - 1)))) atTop
            (𝓝 (∑ ℓ ∈ Finset.range (k + 1),
              ((k + 3).choose (ℓ + 1) : ℝ) * c (ℓ + 1 + 1) * c (k + 3 - (ℓ + 1)))) := by
          refine tendsto_finsetSum _ fun ℓ hℓ => ?_
          have hℓ' := Finset.mem_range.1 hℓ
          exact (tendsto_const_nhds.mul (ih (ℓ + 1 + 1) (by omega) (by omega) (by omega))).mul
            (ih (k + 3 - (ℓ + 1)) (by omega) (by omega) (by omega))
        have h := (((tendsto_const_nhds (x := (1 : ℝ))).add
          (hε (k + 3) (by omega) hP)).mul hA).mul hsum
        refine h.congr' ?_
        filter_upwards [eventually_gt_atTop 0] with r hr
        simp only [Finset.mul_sum, Finset.sum_div]
        refine Finset.sum_congr rfl fun ℓ hℓ => ?_
        have hℓ' := Finset.mem_range.1 hℓ
        have hexp : e (k + 3) - 1 = (-α - 1) + e (ℓ + 1 + 1) + e (k + 3 - (ℓ + 1)) := by
          simp only [he]
          rw [Nat.cast_sub (by omega)]
          push_cast
          ring
        have hLp : L r ^ (k + 2) = L r ^ (ℓ + 1 + 1 - 1) * L r ^ (k + 3 - (ℓ + 1) - 1) := by
          rw [← pow_add]
          congr 1
          omega
        have h1 := (Real.rpow_pos_of_pos hr (-α - 1)).ne'
        have h2 := (Real.rpow_pos_of_pos hr (e (ℓ + 1 + 1))).ne'
        have h3 := (Real.rpow_pos_of_pos hr (e (k + 3 - (ℓ + 1)))).ne'
        have h4 := (pow_pos (hL_pos r) (ℓ + 1 + 1 - 1)).ne'
        have h5 := (pow_pos (hL_pos r) (k + 3 - (ℓ + 1) - 1)).ne'
        rw [hexp, Real.rpow_add hr, Real.rpow_add hr, hLp]
        field_simp
      have hqβ : ((k : ℝ) + 4) * α < e (k + 3) := by
        simp only [he]
        push_cast
        nlinarith
      have hLd : ∀ r, R_L < r → HasDerivAt L (deriv L r) r := fun r hr =>
        ((hL.contDiffAt (Ici_mem_nhds hr)).differentiableAt one_ne_zero).hasDerivAt
      have hkey := tendsto_div_rpow_mul_of_ae_deriv (S := m (k + 3))
        (Λ := fun r => L r ^ (k + 2)) hr₀ hqβ
        (hm_ac (k + 3) (by omega) hP) (fun r hr => (hm_pos (k + 3) (by omega) hP r hr).le)
        (by
          filter_upwards [hder (k + 3) (by omega) hP] with r hr hr0
          rw [hr hr0, Finset.sum_range_succ, Finset.sum_range_succ']
          have hch : ((k + 3).choose (k + 2) : ℝ) = (k : ℝ) + 3 := by
            rw [show (k + 3).choose (k + 2) = k + 3 from Nat.choose_succ_self_right (k + 2)]
            push_cast
            ring
          rw [hch, show k + 3 - (k + 2) = 1 by omega, show k + 2 + 1 = k + 3 by omega]
          simp only [Nat.choose_zero_right, Nat.cast_one, zero_add, Nat.sub_zero]
          ring)
        (hL.pow (k + 2)) (fun r => pow_pos (hL_pos r) _)
        (by
          have h := hL_slow.const_mul ((k : ℝ) + 2)
          rw [mul_zero] at h
          refine h.congr' ?_
          filter_upwards [eventually_gt_atTop R_L] with r hr
          have hd : HasDerivAt (fun r => L r ^ (k + 2))
              (((k + 2 : ℕ) : ℝ) * L r ^ (k + 2 - 1) * deriv L r) r := (hLd r hr).pow (k + 2)
          rw [hd.deriv]
          have hL0 := (hL_pos r).ne'
          rw [show k + 2 - 1 = k + 1 by omega, pow_succ (L r) (k + 1)]
          push_cast
          field_simp)
        hu hg
      rw [moment_hierarchy_constant k hα.ne' hB.ne' c (fun n => rfl)] at hkey
      simpa using hkey
  intro p hp1 hpP
  refine isEquivalent_of_tendsto_div (hc_pos p).ne' (hw p) (claim p hp1 hpP) ?_
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [hw p] with r hr
  have hz : B ^ (2 - (p : ℤ)) = B / B ^ (p - 1) := by
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    rw [show (2 : ℤ) - ((q + 1 : ℕ) : ℤ) = 1 - (q : ℤ) by push_cast; ring,
      zpow_sub₀ hB.ne', zpow_one, zpow_natCast, Nat.add_sub_cancel]
  rw [hz]
  simp only [hc, he] at hr ⊢
  field_simp
  exact (div_self hr).symm

/-! ### Non-vacuity witness: the exact solution -/

/-- The power-law moments `m_p(r) = (2p−3)‼ r^{(2p−1)α}` solve the hierarchy exactly with
`B = C = 1`, `ε_p ≡ 0` and `a(r) = α r^{−α−1}`; here is the derivative identity. -/
theorem hasDerivAt_moment_hierarchy_witness {α r : ℝ} (hr : 0 < r) {p : ℕ} (hp : 1 ≤ p) :
    deriv (fun r : ℝ => ((2 * p - 3)‼ : ℝ) * r ^ ((2 * (p : ℝ) - 1) * α)) r
      = (1 + 0) * (α / 1 * r ^ (-α - 1)) * ∑ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ) *
        (((2 * (ℓ + 1) - 3)‼ : ℝ) * r ^ ((2 * ((ℓ + 1 : ℕ) : ℝ) - 1) * α)) *
        (((2 * (p - ℓ) - 3)‼ : ℝ) * r ^ ((2 * ((p - ℓ : ℕ) : ℝ) - 1) * α)) := by
  have hd := ((Real.hasDerivAt_rpow_const (p := (2 * (p : ℝ) - 1) * α)
    (Or.inl hr.ne')).const_mul ((2 * p - 3)‼ : ℝ)).deriv
  rw [hd]
  have hnat : ∑ ℓ ∈ Finset.range p, p.choose ℓ * (2 * (ℓ + 1) - 3)‼ * (2 * (p - ℓ) - 3)‼
      = (2 * p - 1)‼ := by
    rw [← PercLib.Combinatorics.lemma_I_4_23 p hp]
    refine Finset.sum_congr rfl fun ℓ hℓ => ?_
    have := Finset.mem_range.1 hℓ
    rw [show 2 * (ℓ + 1) - 3 = 2 * ℓ - 1 by omega,
      show 2 * (p - ℓ) - 3 = 2 * p - 2 * ℓ - 3 by omega]
  have hsum : ∑ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ) *
      (((2 * (ℓ + 1) - 3)‼ : ℝ) * r ^ ((2 * ((ℓ + 1 : ℕ) : ℝ) - 1) * α)) *
      (((2 * (p - ℓ) - 3)‼ : ℝ) * r ^ ((2 * ((p - ℓ : ℕ) : ℝ) - 1) * α))
      = ((2 * p - 1)‼ : ℝ) * r ^ (2 * (p : ℝ) * α) := by
    rw [← hnat, Nat.cast_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun ℓ hℓ => ?_
    have hℓ' := Finset.mem_range.1 hℓ
    have hx : r ^ ((2 * ((ℓ + 1 : ℕ) : ℝ) - 1) * α) * r ^ ((2 * ((p - ℓ : ℕ) : ℝ) - 1) * α)
        = r ^ (2 * (p : ℝ) * α) := by
      rw [← Real.rpow_add hr, Nat.cast_sub hℓ'.le]
      congr 1
      push_cast
      ring
    rw [← hx]
    push_cast
    ring
  rw [hsum]
  have hfac : ((2 * p - 1)‼ : ℝ) = (2 * (p : ℝ) - 1) * ((2 * p - 3)‼ : ℝ) := by
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    rcases q with _ | q
    · norm_num [Nat.doubleFactorial]
    · rw [show 2 * (q + 1 + 1) - 1 = 2 * q + 1 + 2 by omega, Nat.doubleFactorial_add_two,
        show 2 * (q + 1 + 1) - 3 = 2 * q + 1 by omega]
      push_cast
      ring
  rw [hfac, show (2 * (p : ℝ) - 1) * α - 1 = (-α - 1) + 2 * (p : ℝ) * α by ring,
    Real.rpow_add hr]
  ring

/-- Non-vacuity witness for `isEquivalent_moment_hierarchy`: every hypothesis holds for the exact
solution `m_p(r) = (2p−3)‼ r^{(2p−1)α}`, `B = C = 1`, `ε_p ≡ 0`, `a(r) = α r^{−α−1}`,
`r₀ = 1`, for every `P` and every `α > 0`. -/
example (P : ℕ) {α : ℝ} (hα : 0 < α) : ∀ p, 1 ≤ p → p ≤ P →
    (fun r : ℝ => ((2 * p - 3)‼ : ℝ) * r ^ ((2 * (p : ℝ) - 1) * α)) ~[atTop]
      fun r => ((2 * p - 3)‼ : ℝ) *
        ((((2 * 2 - 3)‼ : ℝ) * r ^ ((2 * ((2 : ℕ) : ℝ) - 1) * α)) /
          (((2 * 1 - 3)‼ : ℝ) * r ^ ((2 * ((1 : ℕ) : ℝ) - 1) * α))) ^ (p - 1) *
        (((2 * 1 - 3)‼ : ℝ) * r ^ ((2 * ((1 : ℕ) : ℝ) - 1) * α)) := by
  refine isEquivalent_moment_hierarchy (m := fun n r => ((2 * n - 3)‼ : ℝ) *
      r ^ ((2 * (n : ℝ) - 1) * α)) (a := fun r => α / 1 * r ^ (-α - 1)) (ε := fun _ _ => 0)
    (r₀ := 1) (B := 1) (C := 1) one_pos hα one_pos one_pos ?_ ?_ ?_ ?_ IsEquivalent.refl
    (fun _ _ _ => tendsto_const_nhds) ?_
  · intro n _ _ r hr
    have := Nat.doubleFactorial_pos (2 * n - 3)
    have := Real.rpow_pos_of_pos (one_pos.trans_le hr) ((2 * (n : ℝ) - 1) * α)
    positivity
  · intro n _ _ R hR
    apply ContDiffOn.absolutelyContinuousOnInterval
    intro x hx
    rw [uIcc_of_le hR] at hx
    exact (contDiffAt_const.mul (Real.contDiffAt_rpow_const_of_ne (n := 1)
      (one_pos.trans_le hx.1).ne')).contDiffWithinAt
  · have h : (fun r : ℝ => ((2 * 1 - 3)‼ : ℝ) * r ^ ((2 * ((1 : ℕ) : ℝ) - 1) * α))
        = fun r => 1 * r ^ α := by
      funext r
      norm_num
    exact h ▸ IsEquivalent.refl
  · have h : (fun r : ℝ => ((2 * 2 - 3)‼ : ℝ) * r ^ ((2 * ((2 : ℕ) : ℝ) - 1) * α))
        = fun r => 1 * r ^ (3 * α) := by
      funext r
      norm_num [Nat.doubleFactorial]
    exact h ▸ IsEquivalent.refl
  · intro n hn _
    refine Eventually.of_forall fun r hr => ?_
    exact hasDerivAt_moment_hierarchy_witness (one_pos.trans_le hr) (by omega)

/-- Non-vacuity witness for `isEquivalent_moment_hierarchy_slowlyVarying`: the exact solution with
`L ≡ 1` (`R_L = 0`), `B = C = 1`, `ε_p ≡ 0`, `a(r) = α r^{−α−1}`, `r₀ = 1`, for every `P` and
every `α > 0`. -/
example (P : ℕ) {α : ℝ} (hα : 0 < α) : ∀ p, 1 ≤ p → p ≤ P →
    (fun r : ℝ => ((2 * p - 3)‼ : ℝ) * r ^ ((2 * (p : ℝ) - 1) * α)) ~[atTop]
      fun r => ((2 * p - 3)‼ : ℝ) * 1 ^ (p - 1) * (1 : ℝ) ^ (2 - (p : ℤ)) *
        r ^ ((2 * (p : ℝ) - 1) * α) * (1 : ℝ) ^ (p - 1) := by
  refine isEquivalent_moment_hierarchy_slowlyVarying (m := fun n r => ((2 * n - 3)‼ : ℝ) *
      r ^ ((2 * (n : ℝ) - 1) * α)) (a := fun r => α / 1 * r ^ (-α - 1)) (ε := fun _ _ => 0)
    (L := fun _ => 1) (R_L := 0) (r₀ := 1) (B := 1) (C := 1) one_pos hα one_pos one_pos
    ?_ ?_ (fun _ => one_pos) contDiffOn_const ?_ ?_ ?_ IsEquivalent.refl
    (fun _ _ _ => tendsto_const_nhds) ?_
  · intro n _ _ r hr
    have := Nat.doubleFactorial_pos (2 * n - 3)
    have := Real.rpow_pos_of_pos (one_pos.trans_le hr) ((2 * (n : ℝ) - 1) * α)
    positivity
  · intro n _ _ R hR
    apply ContDiffOn.absolutelyContinuousOnInterval
    intro x hx
    rw [uIcc_of_le hR] at hx
    exact (contDiffAt_const.mul (Real.contDiffAt_rpow_const_of_ne (n := 1)
      (one_pos.trans_le hx.1).ne')).contDiffWithinAt
  · simp
  · have h : (fun r : ℝ => ((2 * 1 - 3)‼ : ℝ) * r ^ ((2 * ((1 : ℕ) : ℝ) - 1) * α))
        = fun r => 1 * r ^ α := by
      funext r
      norm_num
    exact h ▸ IsEquivalent.refl
  · have h : (fun r : ℝ => ((2 * 2 - 3)‼ : ℝ) * r ^ ((2 * ((2 : ℕ) : ℝ) - 1) * α))
        = fun r => 1 * r ^ (3 * α) * 1 := by
      funext r
      norm_num [Nat.doubleFactorial]
    exact h ▸ IsEquivalent.refl
  · intro n hn _
    refine Eventually.of_forall fun r hr => ?_
    exact hasDerivAt_moment_hierarchy_witness (one_pos.trans_le hr) (by omega)

end PercLib.Analysis
