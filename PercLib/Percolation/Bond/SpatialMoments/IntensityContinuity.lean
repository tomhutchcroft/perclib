/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New proofs for this project; no upstream Lean code is copied.
-/
module

public import PercLib.Percolation.Bond.SpatialMoments.Continuity
public import PercLib.Percolation.Bond.IndependentLayer.IntensityForm
public import PercLib.Percolation.Bond.SusceptibilityDerivative

/-!
# Weighted continuity in a finite-range intensity family

## Main results

Finite susceptibility is right-open for a transitive intensity with finite
row sum. Local Lipschitz continuity therefore gives susceptibility continuity
at every positive finite-susceptibility parameter. At zero the explicit
small-intensity upper bound supplies continuity. A finite-range upper envelope
then gives actual weighted absolute convergence of the two-point functions.
-/

@[expose] public section
noncomputable section

open Filter Set PercLib.Models.Site
open scoped Topology ENNReal NNReal

namespace PercLib.Percolation.Bond

variable {V : Type*} [Countable V]

/-- Susceptibility is continuous at a positive finite-susceptibility intensity;
the finite-susceptibility neighborhood is obtained by independent sprinkling. -/
theorem continuousAt_toReal_chi_intensity_of_pos (J : Sym2 V → ℝ≥0)
    (hJ : ∀ x y : V, ∃ σ : V ≃ V, σ x = y ∧ ∀ e, J (Sym2.map σ e) = J e)
    (o : V) (hL : rowSum (fun e => (J e : ℝ≥0∞)) o < ⊤)
    {β : ℝ≥0} (hβ : 0 < β) (hchi : chi (intensityProfile J β) o ≠ ⊤) :
    ContinuousAt (fun b : ℝ≥0 => (chi (intensityProfile J b) o).toReal) β := by
  obtain ⟨ε, hε, hγ⟩ := exists_pos_chi_intensity_add_lt_top
    (fun x => hJ o x) hL (lt_top_iff_ne_top.mpr hchi)
  have hβγ : β < β + ε := lt_add_of_pos_right β hε
  have hfin : ∀ b ∈ Ioo (0 : ℝ) ((β + ε : ℝ≥0) : ℝ),
      chi (intensityProfile J b.toNNReal) o ≠ ⊤ := by
    intro b hb
    apply ne_top_of_le_ne_top hγ.ne
    exact chi_mono (intensityProfile_mono J
      (Real.toNNReal_le_iff_le_coe.mpr hb.2.le)) o
  have hcont := (PercLib.Models.NormalizedSmallIntensity.locallyLipschitzOn_chi
    J hJ o hL.ne (a := 0) (b := ((β + ε : ℝ≥0) : ℝ)) le_rfl hfin).continuousOn
  have hβR : (0 : ℝ) < β := by exact_mod_cast hβ
  have hβγR : (β : ℝ) < ((β + ε : ℝ≥0) : ℝ) := by exact_mod_cast hβγ
  have h := (hcont.continuousAt (Ioo_mem_nhds hβR hβγR)).comp
    NNReal.continuous_coe.continuousAt
  simpa only [Function.comp_def, Real.toNNReal_coe] using h

/-- At zero the upper bound `(1 - beta L)⁻¹` tends to the certain singleton
susceptibility. No susceptibility-convergence premise is used. -/
theorem continuousAt_toReal_chi_intensity_zero (J : Sym2 V → ℝ≥0)
    (hJ : ∀ x y : V, ∃ σ : V ≃ V, σ x = y ∧ ∀ e, J (Sym2.map σ e) = J e)
    (o : V) (hL : rowSum (fun e => (J e : ℝ≥0∞)) o < ⊤) :
    ContinuousAt (fun b : ℝ≥0 => (chi (intensityProfile J b) o).toReal) 0 := by
  let M := (rowSum (fun e => (J e : ℝ≥0∞)) o).toNNReal
  have hrow (v : V) : rowSum (fun e => (J e : ℝ≥0∞)) v ≤ (M : ℝ≥0∞) := by
    rw [rowSum_eq_root (fun x => hJ o x) v, ENNReal.coe_toNNReal hL.ne]
  have hsmall : ∀ᶠ b : ℝ≥0 in 𝓝 0, (b : ℝ) * (M : ℝ) < 1 := by
    exact (isOpen_lt (NNReal.continuous_coe.mul_const (M : ℝ)) continuous_const).mem_nhds
      (by simp)
  have hnear : ∀ᶠ b : ℝ≥0 in 𝓝 0,
      1 ≤ (chi (intensityProfile J b) o).toReal ∧
      (chi (intensityProfile J b) o).toReal ≤ (1 - (b : ℝ) * (M : ℝ))⁻¹ := by
    filter_upwards [hsmall] with b hb
    have hbM : (b : ℝ≥0∞) * M < 1 := by
      rw [← ENNReal.coe_mul, ← ENNReal.coe_one, ENNReal.coe_lt_coe]
      exact_mod_cast hb
    have hfinite := (chi_intensity_lt_top J M hrow b hbM o).ne
    constructor
    · simpa only [ENNReal.toReal_one] using
        ENNReal.toReal_mono hfinite (one_le_chi (intensityProfile J b) o)
    · have hbound := ENNReal.toReal_mono
        (ENNReal.inv_ne_top.mpr (ne_of_gt (tsub_pos_of_lt hbM)))
        (chi_intensity_le J M hrow b hbM o)
      simpa only [ENNReal.toReal_inv,
        ENNReal.toReal_sub_of_le hbM.le ENNReal.one_ne_top, ENNReal.toReal_one,
        ENNReal.toReal_mul, ENNReal.coe_toReal] using hbound
  have hupper : Tendsto (fun b : ℝ≥0 => (1 - (b : ℝ) * (M : ℝ))⁻¹)
      (𝓝 0) (𝓝 1) := by
    have h := (continuousAt_const.sub
      (NNReal.continuous_coe.continuousAt.mul_const (M : ℝ))).inv₀
        (by norm_num : (1 : ℝ) - (0 : ℝ≥0) * (M : ℝ) ≠ 0)
    change ContinuousAt (fun b : ℝ≥0 => (1 - (b : ℝ) * (M : ℝ))⁻¹) 0 at h
    simpa only [Pi.inv_apply, Pi.sub_apply, NNReal.coe_zero, zero_mul, sub_zero,
      inv_one] using h.tendsto
  have h := tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hupper (hnear.mono fun _ hb => hb.1) (hnear.mono fun _ hb => hb.2)
  simpa only [ContinuousAt, chi_intensity_zero, ENNReal.toReal_one] using h

/-- Every finite-susceptibility intensity is a point of real susceptibility
continuity, including zero. -/
theorem continuousAt_toReal_chi_intensity (J : Sym2 V → ℝ≥0)
    (hJ : ∀ x y : V, ∃ σ : V ≃ V, σ x = y ∧ ∀ e, J (Sym2.map σ e) = J e)
    (o : V) (hL : rowSum (fun e => (J e : ℝ≥0∞)) o < ⊤)
    {β : ℝ≥0} (hchi : chi (intensityProfile J β) o ≠ ⊤) :
    ContinuousAt (fun b : ℝ≥0 => (chi (intensityProfile J b) o).toReal) β := by
  by_cases hβ : β = 0
  · subst β
    exact continuousAt_toReal_chi_intensity_zero J hJ o hL
  · exact continuousAt_toReal_chi_intensity_of_pos J hJ o hL
      (lt_of_le_of_ne (zero_le : 0 ≤ β) (Ne.symm hβ)) hchi

section Lattice

variable {d : ℕ}

/-- Actual weighted absolute continuity for a transitive finite-range intensity
family at every parameter with finite susceptibility, including zero. -/
theorem tendsto_norm_sq_weighted_tau_intensity
    (J : Sym2 (LatticeSite d) → ℝ≥0)
    (hJ : ∀ x y : LatticeSite d, ∃ σ : LatticeSite d ≃ LatticeSite d,
      σ x = y ∧ ∀ e, J (Sym2.map σ e) = J e)
    (o : LatticeSite d) (hL : rowSum (fun e => (J e : ℝ≥0∞)) o < ⊤)
    {R : ℝ} (hR : 0 ≤ R)
    (hrange : ∀ x y : LatticeSite d, R < ‖x - y‖ → J s(x, y) = 0)
    {β : ℝ≥0} (hchi : chi (intensityProfile J β) o ≠ ⊤) :
    Tendsto (fun b : ℝ≥0 => ∑' x, (1 + ‖x - o‖ ^ 2) *
      |(tau (intensityProfile J b) o x).toReal - (tau (intensityProfile J β) o x).toReal|)
      (𝓝 β) (𝓝 0) := by
  obtain ⟨ε, hε, hγ⟩ := exists_pos_chi_intensity_add_lt_top
    (fun x => hJ o x) hL (lt_top_iff_ne_top.mpr hchi)
  have hβγ : β < β + ε := lt_add_of_pos_right β hε
  apply tendsto_norm_sq_weighted_tau_of_finiteRange
    (fun b => intensityProfile J b) (intensityProfile J β)
    (intensityProfile J (β + ε)) o hR
  · intro x y hxy
    apply Subtype.ext
    simp [intensityProfile, hrange x y hxy]
  · intro x y
    obtain ⟨σ, hσ, hp⟩ := hJ x y
    exact ⟨σ, hσ, intensityProfile_map_eq hp (β + ε)⟩
  · exact hγ.ne
  · exact intensityProfile_mono J hβγ.le
  · filter_upwards [Iio_mem_nhds hβγ] with b hb
    refine ⟨?_, intensityProfile_mono J hb.le⟩
    rcases le_total b β with h | h
    · exact Or.inl (intensityProfile_mono J h)
    · exact Or.inr (intensityProfile_mono J h)
  · exact (continuousAt_toReal_chi_intensity J hJ o hL hchi).tendsto

/-- The same continuity in the real parameter convention `beta.toNNReal`. -/
theorem tendsto_norm_sq_weighted_tau_intensity_toNNReal
    (J : Sym2 (LatticeSite d) → ℝ≥0)
    (hJ : ∀ x y : LatticeSite d, ∃ σ : LatticeSite d ≃ LatticeSite d,
      σ x = y ∧ ∀ e, J (Sym2.map σ e) = J e)
    (o : LatticeSite d) (hL : rowSum (fun e => (J e : ℝ≥0∞)) o < ⊤)
    {R : ℝ} (hR : 0 ≤ R)
    (hrange : ∀ x y : LatticeSite d, R < ‖x - y‖ → J s(x, y) = 0)
    {β : ℝ} (hchi : chi (intensityProfile J β.toNNReal) o ≠ ⊤) :
    Tendsto (fun b : ℝ => ∑' x, (1 + ‖x - o‖ ^ 2) *
      |(tau (intensityProfile J b.toNNReal) o x).toReal -
        (tau (intensityProfile J β.toNNReal) o x).toReal|)
      (𝓝 β) (𝓝 0) :=
  (tendsto_norm_sq_weighted_tau_intensity J hJ o hL hR hrange hchi).comp
    continuous_real_toNNReal.continuousAt.tendsto

end Lattice

end PercLib.Percolation.Bond
