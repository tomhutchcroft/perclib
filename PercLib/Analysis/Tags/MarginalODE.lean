/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrappers for the marginal-ODE assertions DUWG and OBTO, proved from
`RiccatiComparison.lean` and `MomentHierarchy.lean`. No new definitions.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Analysis.RiccatiComparison
public import PercLib.Analysis.MomentHierarchy

/-!
# Marginal ODE: correspondence

Wiki correspondence for the Riccati comparison and the moment hierarchy with a slowly varying
correction.

## Main results

* `riccati_comparison_hasDerivWithinAt`
* `isEquivalent_moment_hierarchy_slowlyVarying_eventually`
-/

@[expose] public section
noncomputable section

open Filter Set MeasureTheory Asymptotics
open scoped Topology Nat

namespace PercLib.Analysis

/-- **DUWG.** For `A, α, r₀ > 0` and `f > 0` differentiable on `[r₀, ∞)` (one-sided at `r₀`):
`A x^{-α-1} f² ≤ f'` on `[r₀, ∞)` gives `f r ≤ (α/A) r^α`, and if `f → ∞`,
`f' ≤ A x^{-α-1} f²` gives `(α/A) r^α ≤ f r`, for every `r ≥ r₀`. -/
@[tag "DUWG"]
theorem riccati_comparison_hasDerivWithinAt {f f' : ℝ → ℝ} {A α r₀ : ℝ} (hA : 0 < A)
    (hα : 0 < α) (hr₀ : 0 < r₀)
    (hderiv : ∀ x, r₀ ≤ x → HasDerivWithinAt f (f' x) (Ici r₀) x)
    (hpos : ∀ x, r₀ ≤ x → 0 < f x) :
    ((∀ x, r₀ ≤ x → A * x ^ (-α - 1) * f x ^ 2 ≤ f' x) → ∀ r, r₀ ≤ r → f r ≤ α / A * r ^ α) ∧
    ((∀ x, r₀ ≤ x → f' x ≤ A * x ^ (-α - 1) * f x ^ 2) → Tendsto f atTop atTop →
      ∀ r, r₀ ≤ r → α / A * r ^ α ≤ f r) := by
  -- derivatives at points `x > r₀` are two-sided
  have hd : ∀ x, r₀ < x → HasDerivAt f (f' x) x := fun x hx =>
    (hderiv x hx.le).hasDerivAt (Ici_mem_nhds hx)
  -- continuity at the endpoint from the right
  have hfc : Tendsto f (𝓝[>] r₀) (𝓝 (f r₀)) :=
    ((hderiv r₀ le_rfl).continuousWithinAt.mono Ioi_subset_Ici_self).tendsto
  have hgc : Tendsto (fun r : ℝ => α / A * r ^ α) (𝓝[>] r₀) (𝓝 (α / A * r₀ ^ α)) :=
    ((Real.continuousAt_rpow_const r₀ α (Or.inl hr₀.ne')).const_mul (α / A)).tendsto.mono_left
      nhdsWithin_le_nhds
  refine ⟨fun hineq r hr => ?_, fun hineq hinf r hr => ?_⟩
  · have key : ∀ r, r₀ < r → f r ≤ α / A * r ^ α := fun r hr =>
      lemma_I_4_5_one_nocont hA hα (hr₀.trans hr) (fun x hx => hd x (hr.trans_le hx))
        (fun x hx => hpos x (hr.le.trans hx)) (fun x hx => hineq x (hr.le.trans hx)) r le_rfl
    rcases hr.eq_or_lt with rfl | hlt
    · exact le_of_tendsto_of_tendsto hfc hgc
        (eventually_nhdsWithin_of_forall fun x hx => key x hx)
    · exact key r hlt
  · have key : ∀ r, r₀ < r → α / A * r ^ α ≤ f r := fun r hr =>
      lemma_I_4_5_two_nocont hA hα (hr₀.trans hr) (fun x hx => hd x (hr.trans_le hx))
        (fun x hx => hpos x (hr.le.trans hx)) hinf (fun x hx => hineq x (hr.le.trans hx)) r
        le_rfl
    rcases hr.eq_or_lt with rfl | hlt
    · exact le_of_tendsto_of_tendsto hgc hfc
        (eventually_nhdsWithin_of_forall fun x hx => key x hx)
    · exact key r hlt

/-- **OBTO.** The hypotheses of `isEquivalent_moment_hierarchy`, with `m₂ ~ C r^{3α} L(r)`
for an `L` that is positive and `C¹` on `[R_L, ∞)` with `r L'(r)/L(r) → 0`. Then for every
`1 ≤ p ≤ P`, `m_p ~ (2p−3)‼ C^{p−1} B^{2−p} r^{(2p−1)α} L(r)^{p−1}`, and this is
`~ (2p−3)‼ (m₂/m₁)^{p−1} m₁`. -/
@[tag "OBTO"]
theorem isEquivalent_moment_hierarchy_slowlyVarying_eventually {P : ℕ} {r₀ α B C R_L : ℝ}
    (hr₀ : 0 < r₀) (hα : 0 < α) (hB : 0 < B) (hC : 0 < C) {m : ℕ → ℝ → ℝ} {a L : ℝ → ℝ}
    {ε : ℕ → ℝ → ℝ}
    (hm_pos : ∀ p, 1 ≤ p → p ≤ P → ∀ r, r₀ ≤ r → 0 < m p r)
    (hm_ac : ∀ p, 1 ≤ p → p ≤ P → ∀ R, r₀ ≤ R → AbsolutelyContinuousOnInterval (m p) r₀ R)
    (hL_pos : ∀ r, R_L ≤ r → 0 < L r) (hL : ContDiffOn ℝ 1 L (Ici R_L))
    (hL_slow : Tendsto (fun r => r * deriv L r / L r) atTop (𝓝 0))
    (hm1 : m 1 ~[atTop] fun r => B * r ^ α)
    (hm2 : m 2 ~[atTop] fun r => C * r ^ (3 * α) * L r)
    (ha : a ~[atTop] fun r => α / B * r ^ (-α - 1))
    (hε : ∀ p, 3 ≤ p → p ≤ P → Tendsto (ε p) atTop (𝓝 0))
    (hder : ∀ p, 3 ≤ p → p ≤ P → ∀ᵐ r, r₀ ≤ r →
      deriv (m p) r = (1 + ε p r) * a r *
        ∑ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ) * m (ℓ + 1) r * m (p - ℓ) r) :
    ∀ p, 1 ≤ p → p ≤ P →
      (m p ~[atTop] fun r => ((2 * p - 3)‼ : ℝ) * C ^ (p - 1) * B ^ (2 - (p : ℤ)) *
        r ^ ((2 * (p : ℝ) - 1) * α) * L r ^ (p - 1)) ∧
      ((fun r => ((2 * p - 3)‼ : ℝ) * C ^ (p - 1) * B ^ (2 - (p : ℤ)) *
          r ^ ((2 * (p : ℝ) - 1) * α) * L r ^ (p - 1)) ~[atTop]
        fun r => ((2 * p - 3)‼ : ℝ) * (m 2 r / m 1 r) ^ (p - 1) * m 1 r) := by
  intro p hp hpP
  -- the modification `L̃ r = L (max r (R_L + 1))`, positive everywhere
  set L' : ℝ → ℝ := fun r => L (max r (R_L + 1)) with hL'
  have hLL' : ∀ r, R_L + 1 ≤ r → L' r = L r := fun r hr => by
    simp only [hL', max_eq_left hr]
  have hevL : L' =ᶠ[atTop] L := (eventually_ge_atTop (R_L + 1)).mono hLL'
  have hL'_pos : ∀ r, 0 < L' r := fun r => hL_pos _ (by linarith [le_max_right r (R_L + 1)])
  have hL'_C1 : ContDiffOn ℝ 1 L' (Ici (R_L + 2)) :=
    (hL.mono (Ici_subset_Ici.2 (by linarith))).congr fun x hx =>
      hLL' x (by have := mem_Ici.1 hx; linarith)
  have hderiv_eq : ∀ᶠ r in atTop, deriv L' r = deriv L r := by
    filter_upwards [eventually_gt_atTop (R_L + 1)] with r hr
    exact Filter.EventuallyEq.deriv_eq
      ((eventually_ge_nhds hr).mono fun x hx => hLL' x hx)
  have hL'_slow : Tendsto (fun r => r * deriv L' r / L' r) atTop (𝓝 0) := by
    refine hL_slow.congr' ?_
    filter_upwards [hderiv_eq, hevL] with r h1 h2
    rw [h1, h2]
  have hm2' : m 2 ~[atTop] fun r => C * r ^ (3 * α) * L' r :=
    hm2.congr_right (hevL.mono fun r hr => by simp only [hr])
  have hmain := isEquivalent_moment_hierarchy_slowlyVarying (R_L := R_L + 2) hr₀ hα hB hC hm_pos
    hm_ac hL'_pos hL'_C1 hL'_slow hm1 hm2' ha hε hder p hp hpP
  refine ⟨hmain.congr_right (hevL.mono fun r hr => by simp only [hr]), ?_⟩
  -- the second equivalence: algebra of equivalents
  have h : (fun r => ((2 * p - 3)‼ : ℝ) * (m 2 r / m 1 r) ^ (p - 1) * m 1 r) ~[atTop]
      fun r => ((2 * p - 3)‼ : ℝ) * ((C * r ^ (3 * α) * L r) / (B * r ^ α)) ^ (p - 1) *
        (B * r ^ α) :=
    ((IsEquivalent.refl (u := fun _ : ℝ => ((2 * p - 3)‼ : ℝ))).mul
      ((hm2.div hm1).pow (p - 1))).mul hm1
  refine (h.congr_right ?_).symm
  filter_upwards [eventually_gt_atTop 0] with r hr
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, by omega⟩
  have hy : 0 < r ^ α := Real.rpow_pos_of_pos hr α
  have h3 : r ^ (3 * α) = (r ^ α) ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le]; push_cast; ring_nf
  have h2n : r ^ ((2 * ((n + 1 : ℕ) : ℝ) - 1) * α) = (r ^ α) ^ (2 * n + 1) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le]; push_cast; ring_nf
  have hz : B ^ (2 - ((n + 1 : ℕ) : ℤ)) = B / B ^ n := by
    rw [show (2 : ℤ) - ((n + 1 : ℕ) : ℤ) = 1 - (n : ℤ) by push_cast; ring,
      zpow_sub₀ hB.ne', zpow_one, zpow_natCast]
  simp only [Nat.add_sub_cancel, h3, h2n, hz]
  have hBn : 0 < B ^ n := pow_pos hB n
  have hyn : 0 < (r ^ α) ^ n := pow_pos hy n
  simp only [div_pow, mul_pow, ← pow_mul]
  field_simp
  ring

end PercLib.Analysis
