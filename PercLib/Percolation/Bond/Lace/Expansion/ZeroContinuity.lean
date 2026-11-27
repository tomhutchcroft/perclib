/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Original consequences of finite double-connection witnesses and monotone
product-profile regularity. No upstream proof is copied.
-/
module

public import PercLib.Percolation.Bond.Lace.Coefficients.Coefficients
public import PercLib.Percolation.Bond.ProfileRegularity
public import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Endpoint continuity of the zeroth lace coefficient

## Main results

Double-connection probability is lower semicontinuous in the full product
profile, and is continuous from smaller profiles at every upper profile.
The zeroth lace coefficient has the same continuity. Its endpoint row converges
in real `ℓ¹` whenever the upper row has finite mass; in particular, a finite
upper-profile bubble suffices. No finite-cluster hypothesis is needed.
-/

@[expose] public section
noncomputable section

open Set MeasureTheory Filter Topology PercLib.Probability
open scoped ENNReal

namespace PercLib.Percolation.Bond.Lace

variable {V : Type*}

/-- A double connection contains a finite double-connection witness. -/
theorem exists_finset_of_mem_doubleConn {ω : Config V} {x y : V}
    (hω : ω ∈ doubleConn x y) :
    ∃ F : Finset (Sym2 V), (F : Config V) ⊆ ω ∧ (F : Config V) ∈ doubleConn x y := by
  classical
  obtain ⟨F, H, hFfin, hHfin, hd, hFω, hHω, hF, hH⟩ :=
    (mem_doubleConn_iff ω x y).mp hω
  refine ⟨(hFfin.union hHfin).toFinset, ?_, ?_⟩
  · simpa only [Set.Finite.coe_toFinset] using union_subset hFω hHω
  · rw [Set.Finite.coe_toFinset, mem_doubleConn_iff]
    exact ⟨F, H, hFfin, hHfin, hd, subset_union_left, subset_union_right, hF, hH⟩

/-- Double-connection probability is lower semicontinuous in the product profile. -/
theorem lowerSemicontinuous_law_doubleConn [Countable V] (x y : V) :
    LowerSemicontinuous (fun q : Sym2 V → unitInterval => law q (doubleConn x y)) := by
  have heq := eq_iUnion_finite_witness (isUpperSet_doubleConn x y)
    (fun _ h => exists_finset_of_mem_doubleConn h)
  change LowerSemicontinuous (fun q : Sym2 V → unitInterval =>
    prodBernoulli q (doubleConn x y))
  rw [heq]
  exact lowerSemicontinuous_prodBernoulli_iUnion_witness _

/-- Double-connection probability is continuous from smaller profiles, including
at profiles with infinite clusters. -/
theorem continuousWithinAt_law_doubleConn_Iic [Countable V]
    (q₀ : Sym2 V → unitInterval) (x y : V) :
    ContinuousWithinAt (fun q : Sym2 V → unitInterval => law q (doubleConn x y))
      (Iic q₀) q₀ := by
  apply continuousWithinAt_Iic_of_lowerSemicontinuous_of_monotone
    (lowerSemicontinuous_law_doubleConn x y)
  intro q q' hq
  exact prodBernoulli_mono_event q q' hq (measurableSet_doubleConn x y)
    (isUpperSet_doubleConn x y)

/-- The diagonal-removed zeroth coefficient is continuous from smaller profiles. -/
theorem continuousWithinAt_piZero_Iic [Countable V]
    (q₀ : Sym2 V → unitInterval) (x y : V) :
    ContinuousWithinAt (fun q : Sym2 V → unitInterval => piZero q x y) (Iic q₀) q₀ := by
  classical
  by_cases hxy : x = y
  · subst y
    simpa only [piZero_self] using
      (continuousWithinAt_const : ContinuousWithinAt
        (fun _ : Sym2 V → unitInterval => (0 : ℝ≥0∞)) (Iic q₀) q₀)
  · simpa only [piZero_of_ne _ hxy] using continuousWithinAt_law_doubleConn_Iic q₀ x y

/-- A finite upper zeroth-coefficient row gives joint endpoint `ℓ¹` continuity
from smaller profiles. Monotonicity supplies the upper row itself as a dominator. -/
theorem tendsto_tsum_abs_piZero_sub_Iic [Countable V]
    (q₀ : Sym2 V → unitInterval) (x : V)
    (hmass : (∑' y : V, piZero q₀ x y) ≠ ⊤) :
    Tendsto (fun q : Sym2 V → unitInterval =>
      ∑' y : V, |(piZero q x y).toReal - (piZero q₀ x y).toReal|)
      (𝓝[Iic q₀] q₀) (𝓝 0) := by
  have hsum : Summable (fun y : V => (piZero q₀ x y).toReal) :=
    ENNReal.summable_toReal hmass
  have hpoint (y : V) : Tendsto (fun q : Sym2 V → unitInterval =>
      |(piZero q x y).toReal - (piZero q₀ x y).toReal|)
      (𝓝[Iic q₀] q₀) (𝓝 (0 : ℝ)) := by
    have ht := (ENNReal.continuousAt_toReal (piZero_ne_top q₀ x y)).comp_continuousWithinAt
      (f := fun q : Sym2 V → unitInterval => piZero q x y)
      (continuousWithinAt_piZero_Iic q₀ x y)
    simpa only [Function.comp_apply, sub_self, abs_zero] using
      (ht.tendsto.sub_const (piZero q₀ x y).toReal).abs
  have hbound : ∀ᶠ q in 𝓝[Iic q₀] q₀, ∀ y : V,
      ‖|(piZero q x y).toReal - (piZero q₀ x y).toReal|‖ ≤ (piZero q₀ x y).toReal := by
    filter_upwards [self_mem_nhdsWithin] with q hq y
    have hle := ENNReal.toReal_mono (piZero_ne_top q₀ x y) (piZero_mono hq x y)
    have hnonneg := ENNReal.toReal_nonneg (a := piZero q x y)
    have hupper := ENNReal.toReal_nonneg (a := piZero q₀ x y)
    simp only [Real.norm_eq_abs, abs_abs]
    exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
  simpa only [tsum_zero] using
    (tendsto_tsum_of_dominated_convergence (g := fun _ : V => (0 : ℝ))
      hsum hpoint hbound)

/-- A finite bubble gives endpoint `ℓ¹` continuity of the zeroth coefficient
without requiring almost surely finite clusters. -/
theorem tendsto_tsum_abs_piZero_sub_Iic_of_bubble [Countable V]
    (q₀ : Sym2 V → unitInterval) (x : V)
    (hbubble : (∑' y : V, tau q₀ x y ^ 2) ≠ ⊤) :
    Tendsto (fun q : Sym2 V → unitInterval =>
      ∑' y : V, |(piZero q x y).toReal - (piZero q₀ x y).toReal|)
      (𝓝[Iic q₀] q₀) (𝓝 0) :=
  tendsto_tsum_abs_piZero_sub_Iic q₀ x
    (ne_top_of_le_ne_top hbubble (ENNReal.tsum_le_tsum fun y => piZero_le_tau_sq q₀ x y))

/-- The canonical order-zero coefficient inherits the finite-bubble endpoint limit. -/
theorem tendsto_tsum_abs_laceCoefficient_zero_sub_Iic_of_bubble [Countable V]
    (q₀ : Sym2 V → unitInterval) (x : V)
    (hbubble : (∑' y : V, tau q₀ x y ^ 2) ≠ ⊤) :
    Tendsto (fun q : Sym2 V → unitInterval =>
      ∑' y : V, |(laceCoefficient q 0 x y).toReal - (laceCoefficient q₀ 0 x y).toReal|)
      (𝓝[Iic q₀] q₀) (𝓝 0) :=
  tendsto_tsum_abs_piZero_sub_Iic_of_bubble q₀ x hbubble

/-- Finite rows occur even on infinite vertex spaces, for example at the zero profile. -/
example [Countable V] (x : V) :
    Tendsto (fun q : Sym2 V → unitInterval =>
      ∑' y : V, |(piZero q x y).toReal - (piZero (fun _ => 0) x y).toReal|)
      (𝓝[Iic (fun _ : Sym2 V => (0 : unitInterval))] (fun _ => 0)) (𝓝 0) :=
  tendsto_tsum_abs_piZero_sub_Iic (fun _ => 0) x (by simp)

end PercLib.Percolation.Bond.Lace
