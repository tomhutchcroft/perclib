/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New proofs for this project; no upstream Lean code is copied.
-/
module

public import PercLib.Analysis.InverseSquareBlock
public import PercLib.Analysis.LogarithmicCorrections
public import PercLib.Percolation.Bond.Lace.Bootstrap.SusceptibilityLowerDerivative
public import PercLib.Percolation.Bond.SusceptibilityDerivative

/-!
# Susceptibility bounds from an actual constant triangle cap

## Main results

On an open interval with finite susceptibility and actual triangle at most `D`, the
susceptibility is at most `D + 3 * beta * b * D² / (b - beta)`. Applying the proved ODE
comparison to `chi - D` retains the additive constant `D`. No divergence or finiteness
assumption at the excluded endpoint `b` is needed. The uniform inverse-gap coefficient
is the maximum of the two endpoint values of an affine numerator.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set Filter PercLib.Analysis
open scoped ENNReal NNReal Topology

namespace PercLib.Percolation.Bond.Lace

private theorem inv_integral_inv_three_sq_mul_sq_const {s b D : ℝ}
    (hs : 0 < s) (hsb : s < b) (hD : 0 < D) :
    (∫ t in s..b, 1 / (3 * t ^ 2 * D ^ 2))⁻¹ = 3 * s * b * D ^ 2 / (b - s) := by
  have hbase := integral_one_div_add_sq hs (sub_nonneg.mpr hsb.le)
  rw [intervalIntegral.integral_comp_add_left (fun t : ℝ => 1 / t ^ 2) s] at hbase
  have he : s + (b - s) = b := by ring
  simp only [add_zero, he] at hbase
  have hf (t : ℝ) : 1 / (3 * t ^ 2 * D ^ 2) = (3 * D ^ 2)⁻¹ * (1 / t ^ 2) := by
    simp only [one_div, mul_inv_rev]
    ring
  simp_rw [hf]
  rw [intervalIntegral.integral_const_mul, hbase]
  have hb : b ≠ 0 := (hs.trans hsb).ne'
  have hgap : b - s ≠ 0 := (sub_pos.mpr hsb).ne'
  field_simp [hs.ne', hD.ne', hb, hgap]

/-- An actual constant triangle cap gives the shifted susceptibility bound with
additive constant `D`. The upper endpoint is excluded from every finiteness hypothesis. -/
theorem chi_le_triangle_cap_add_div_gap {d : ℕ}
    (J : Sym2 (Fin d → ℤ) → ℝ≥0)
    (hJ : ∀ x y g : Fin d → ℤ, J s(x + g, y + g) = J s(x, y))
    (hrow : ∀ u, rowSum (fun e => (J e : ℝ≥0∞)) u ≤ 1)
    {a b : ℝ} (ha : 0 ≤ a)
    (hfin : ∀ t ∈ Ioo a b, chi (intensityProfile J t.toNNReal) 0 ≠ ⊤)
    (D : ℝ) (hD : 1 ≤ D)
    (htriangle : ∀ t ∈ Ioo a b,
      (∑' u, ∑' v, tau (intensityProfile J t.toNNReal) 0 u *
        tau (intensityProfile J t.toNNReal) u v *
        tau (intensityProfile J t.toNNReal) v 0) ≤ ENNReal.ofReal D)
    {β : ℝ} (hβ : β ∈ Ioo a b) :
    (chi (intensityProfile J β.toNNReal) 0).toReal ≤
      D + 3 * β * b * D ^ 2 / (b - β) := by
  let χ := fun t : ℝ => (chi (intensityProfile J t.toNNReal) 0).toReal
  have hβ0 : 0 < β := ha.trans_lt hβ.1
  have hb : 0 < b := hβ0.trans hβ.2
  have hD0 : 0 < D := zero_lt_one.trans_le hD
  have hgap : 0 < b - β := sub_pos.mpr hβ.2
  change χ β ≤ _
  by_cases hsmall : χ β ≤ D
  · exact hsmall.trans (le_add_of_nonneg_right (by positivity))
  have hlarge : D < χ β := lt_of_not_ge hsmall
  have htrans (x y : Fin d → ℤ) : ∃ σ : (Fin d → ℤ) ≃ (Fin d → ℤ),
      σ x = y ∧ ∀ e, J (Sym2.map σ e) = J e := by
    refine ⟨Equiv.addRight (y - x), by simp, ?_⟩
    intro e
    induction e using Sym2.inductionOn with
    | _ u v => exact hJ u v (y - x)
  have hR : rowSum (fun e => (J e : ℝ≥0∞)) 0 ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (hrow 0)
  have hmono : MonotoneOn χ (Ioo a b) := monotoneOn_toReal_chi J 0 hfin
  have hcont : ContinuousAt χ β :=
    (PercLib.Models.NormalizedSmallIntensity.locallyLipschitzOn_chi
      J htrans 0 hR ha hfin).continuousOn.continuousAt (Ioo_mem_nhds hβ.1 hβ.2)
  have hpos (t : ℝ) (ht : t ∈ Ioo β b) : 0 < χ t - D := by
    have hle := hmono hβ ⟨hβ.1.trans ht.1, ht.2⟩ ht.1.le
    linarith
  have hmonof : MonotoneOn (fun t => χ t - D) (Ioo β b) := by
    intro s hs t ht hst
    exact sub_le_sub_right
      (hmono ⟨hβ.1.trans hs.1, hs.2⟩ ⟨hβ.1.trans ht.1, ht.2⟩ hst) D
  have hac (s t : ℝ) (hs : β < s) (hst : s ≤ t) (ht : t < b) :
      AbsolutelyContinuousOnInterval (fun u => χ u - D) s t := by
    have hlip := lipschitzOnWith_chi J htrans 0 hR ha hfin (hβ.1.trans hs) ht
    rw [← uIcc_of_le hst] at hlip
    exact hlip.absolutelyContinuousOnInterval.sub
      (LipschitzWith.const D).lipschitzOnWith.absolutelyContinuousOnInterval
  have hder : ∀ᵐ t, t ∈ Ioo β b →
      (χ t - D) ^ 2 / (3 * t ^ 2 * D ^ 2) ≤ deriv (fun u => χ u - D) t := by
    filter_upwards [ae_deriv_chi_ge_triangle_cap J hJ hrow ha hfin D hD htriangle]
      with t ht htab
    have h := ht ⟨hβ.1.trans htab.1, htab.2⟩
    change max (χ t - D) 0 ^ 2 / (3 * t ^ 2 * D ^ 2) ≤ deriv χ t at h
    simpa only [max_eq_left (hpos t htab).le, deriv_sub_const] using h
  have hbound (γ : ℝ) (hγ : γ ∈ Ioo β b) :
      χ γ ≤ D + 3 * γ * b * D ^ 2 / (b - γ) := by
    have h := le_of_deriv_ge_sq_sub_mul_div (χ := fun t => χ t - D)
      (D := fun _ => D) (κ := 0) hβ0.le le_rfl hpos hmonof hac measurable_const
      (fun _ _ => hD) (by simpa only [zero_mul, sub_zero] using hder) hγ
    simp only [zero_mul, zero_div, add_zero, one_mul] at h
    rw [inv_integral_inv_three_sq_mul_sq_const (hβ0.trans hγ.1) hγ.2 hD0] at h
    linarith
  have hlimit : ContinuousAt (fun γ : ℝ => D + 3 * γ * b * D ^ 2 / (b - γ)) β := by
    fun_prop (disch := exact (sub_pos.mpr hβ.2).ne')
  have hev : ∀ᶠ γ in 𝓝[>] β, γ ∈ Ioo β b := Ioo_mem_nhdsGT hβ.2
  exact le_of_tendsto_of_tendsto
    (hcont.tendsto.mono_left nhdsWithin_le_nhds)
    (hlimit.tendsto.mono_left nhdsWithin_le_nhds)
    (hev.mono fun γ hγ => hbound γ hγ)

/-- A uniform inverse-gap bound retaining the better of the two endpoint maxima.
The numerator of the shifted bound is affine in the intensity, so its uniform
coefficient is `max (D*b) (3*b²*D²)`, without adding those two quantities. -/
theorem chi_le_triangle_cap_div_gap {d : ℕ}
    (J : Sym2 (Fin d → ℤ) → ℝ≥0)
    (hJ : ∀ x y g : Fin d → ℤ, J s(x + g, y + g) = J s(x, y))
    (hrow : ∀ u, rowSum (fun e => (J e : ℝ≥0∞)) u ≤ 1)
    {a b : ℝ} (ha : 0 ≤ a)
    (hfin : ∀ t ∈ Ioo a b, chi (intensityProfile J t.toNNReal) 0 ≠ ⊤)
    (D : ℝ) (hD : 1 ≤ D)
    (htriangle : ∀ t ∈ Ioo a b,
      (∑' u, ∑' v, tau (intensityProfile J t.toNNReal) 0 u *
        tau (intensityProfile J t.toNNReal) u v *
        tau (intensityProfile J t.toNNReal) v 0) ≤ ENNReal.ofReal D)
    {β : ℝ} (hβ : β ∈ Ioo a b) :
    (chi (intensityProfile J β.toNNReal) 0).toReal ≤
      max (D * b) (3 * b ^ 2 * D ^ 2) / (b - β) := by
  refine (chi_le_triangle_cap_add_div_gap J hJ hrow ha hfin D hD htriangle hβ).trans ?_
  have hβ0 : 0 ≤ β := ha.trans hβ.1.le
  have hgap : 0 < b - β := sub_pos.mpr hβ.2
  rw [le_div_iff₀ hgap]
  have he : (D + 3 * β * b * D ^ 2 / (b - β)) * (b - β) =
      D * b + β * (3 * b * D ^ 2 - D) := by field_simp [hgap.ne']; ring
  rw [he]
  by_cases hs : 0 ≤ 3 * b * D ^ 2 - D
  · calc
      _ ≤ D * b + b * (3 * b * D ^ 2 - D) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_right hβ.2.le hs)
      _ = 3 * b ^ 2 * D ^ 2 := by ring
      _ ≤ _ := le_max_right _ _
  · have hn : β * (3 * b * D ^ 2 - D) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hβ0 (le_of_not_ge hs)
    exact (add_le_of_nonpos_right hn).trans (le_max_left _ _)

end PercLib.Percolation.Bond.Lace
