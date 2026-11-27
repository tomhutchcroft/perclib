/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New proofs for this project; no upstream Lean code is copied.
-/
module

public import PercLib.Percolation.Bond.Lace.Bootstrap.Intensity.CriticalExpansion
public import PercLib.Percolation.Bond.Lace.Expansion.KernelContinuity
public import PercLib.Analysis.LatticeFourier.ExactInversion
public import PercLib.Analysis.NearestNeighborResolventCritical

/-!
# Abel limits and Fourier inversion at criticality

The critical Fourier expression is the limit of the actual subcritical transforms.
It is expressed using the absolutely summable critical signed lace kernel, rather
than an unordered Fourier sum of the critical two-point function. The singular
symbol frequencies are excluded from pointwise limits and form a null set in the
physical Fourier box.

## Main results

The actual critical normalization, off-singularity Abel limit, infrared bound,
and inverse Fourier representation follow from the proved nearest-neighbour
bootstrap and spatial continuity of the canonical signed kernel.
-/

@[expose] public section
noncomputable section

open MeasureTheory Metric Set Filter Real PercLib.Analysis PercLib.Models.Site
open scoped ENNReal NNReal Topology

namespace PercLib.Percolation.Bond.Lace

variable {d : ℕ}

private theorem critical_intensity_pos (hd : 50000 ≤ d) :
    0 < (rootCriticalIntensity (nearestNeighborIntensity d) 0).toNNReal :=
  ENNReal.toNNReal_pos
    (ne_of_gt (zero_lt_one.trans_le (one_le_rootCriticalIntensity_nearestNeighbor d)))
    (rootCriticalIntensity_nearestNeighbor_ne_top hd)

private theorem tendsto_profile_below_critical :
    let b := (rootCriticalIntensity (nearestNeighborIntensity d) 0).toNNReal
    Tendsto (intensityProfile (nearestNeighborIntensity d)) (𝓝[<] b)
      (𝓝[Iic (intensityProfile (nearestNeighborIntensity d) b)]
        (intensityProfile (nearestNeighborIntensity d) b)) := by
  dsimp only
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨(continuous_intensityProfile_pi _).continuousAt.tendsto.mono_left
    nhdsWithin_le_nhds, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with β hβ
  exact intensityProfile_mono _ hβ.le

/-- The actual signed lace kernel approaches its critical kernel in spatial `ℓ¹`. -/
theorem tendsto_tsum_abs_laceSum_nearestNeighbor_critical_sub (hd : 50000 ≤ d) :
    let b := (rootCriticalIntensity (nearestNeighborIntensity d) 0).toNNReal
    let q := intensityProfile (nearestNeighborIntensity d) b
    Tendsto (fun β : ℝ≥0 => ∑' y, |laceSum (intensityProfile (nearestNeighborIntensity d) β) 0 y -
      laceSum q 0 y|) (𝓝[<] b) (𝓝 0) := by
  let b := (rootCriticalIntensity (nearestNeighborIntensity d) 0).toNNReal
  let q := intensityProfile (nearestNeighborIntensity d) b
  have h := tendsto_tsum_abs_laceSum_sub_Iic_of_diagram_bounds q 0
    (ENNReal.ofReal (1 / 855 : ℝ)) (ENNReal.ofReal (1 / 1712 : ℝ))
    (by norm_num) ENNReal.ofReal_ne_top (nn_critical_diagramTransfer_mass_le_one_div hd)
    (nn_critical_diagramTerminal_mass_le_one_div hd)
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (nn_critical_diagramInitial_mass_le hd 0))
    (ae_finite_cluster_nearestNeighbor_critical hd)
  exact h.comp tendsto_profile_below_critical

/-- Every frequency of the signed lace correction converges to its actual
critical value; the signed kernel remains absolutely summable there. -/
theorem tendsto_laceCosineTransform_nearestNeighbor_critical (hd : 50000 ≤ d)
    (k : Fin d → ℝ) :
    let b := (rootCriticalIntensity (nearestNeighborIntensity d) 0).toNNReal
    let q := intensityProfile (nearestNeighborIntensity d) b
    Tendsto (fun β : ℝ≥0 => latticeCosineTransform
      (laceSum (intensityProfile (nearestNeighborIntensity d) β) 0) k)
      (𝓝[<] b) (𝓝 (latticeCosineTransform (laceSum q 0) k)) := by
  let b := (rootCriticalIntensity (nearestNeighborIntensity d) 0).toNNReal
  let q := intensityProfile (nearestNeighborIntensity d) b
  have h := tendstoUniformly_laceSum_character_Iic_of_diagram_bounds q 0
    (ENNReal.ofReal (1 / 855 : ℝ)) (ENNReal.ofReal (1 / 1712 : ℝ))
    (by norm_num) ENNReal.ofReal_ne_top (nn_critical_diagramTransfer_mass_le_one_div hd)
    (nn_critical_diagramTerminal_mass_le_one_div hd)
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (nn_critical_diagramInitial_mass_le hd 0))
    (ae_finite_cluster_nearestNeighbor_critical hd)
  have hc := (h.tendsto_at (latticeCharacter k)).comp tendsto_profile_below_critical
  have hr := Complex.continuous_re.continuousAt.tendsto.comp hc
  rw [re_tsum_mul_latticeCharacter (summable_laceSum_nearestNeighbor_critical hd 0)] at hr
  apply hr.congr'
  filter_upwards [self_mem_nhdsWithin] with β hβ
  have hsβ : Summable (laceSum (intensityProfile (nearestNeighborIntensity d) β) 0) := by
    apply summable_laceSum
    exact tsum_laceCoefficient_all_mass_ne_top_of_le_diagram_bounds
      (intensityProfile_mono _ hβ.le) 0
      (ENNReal.ofReal (1 / 855 : ℝ)) (ENNReal.ofReal (1 / 1712 : ℝ))
      (by norm_num) ENNReal.ofReal_ne_top (nn_critical_diagramTransfer_mass_le_one_div hd)
      (nn_critical_diagramTerminal_mass_le_one_div hd)
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (nn_critical_diagramInitial_mass_le hd 0))
  simpa only [Function.comp_apply] using re_tsum_mul_latticeCharacter hsβ k

/-- Infinite critical susceptibility makes the actual comparison-walk parameter
tend to one from below, despite totalization of `ENNReal.toReal` at infinity. -/
theorem tendsto_susceptibilityWalkParameter_nearestNeighbor_critical (hd : 50000 ≤ d) :
    let b := (rootCriticalIntensity (nearestNeighborIntensity d) 0).toNNReal
    Tendsto (fun β : ℝ≥0 => susceptibilityWalkParameter
      (intensityProfile (nearestNeighborIntensity d) β)) (𝓝[<] b) (𝓝 1) := by
  let b := (rootCriticalIntensity (nearestNeighborIntensity d) 0).toNNReal
  have hχ := tendsto_chi_intensity_nhdsLT (nearestNeighborIntensity d) 0 b
  rw [chi_nearestNeighbor_critical_eq_top hd] at hχ
  have hi := tendsto_inv_iff.mpr hχ
  rw [ENNReal.inv_top] at hi
  have hr := (ENNReal.continuousAt_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).tendsto.comp hi
  simpa only [susceptibilityWalkParameter, Function.comp_apply, ENNReal.toReal_inv,
    ENNReal.toReal_zero, sub_zero] using (tendsto_const_nhds (x := (1 : ℝ))).sub hr

private theorem tendsto_nearestNeighbor_step_critical :
    let b := (rootCriticalIntensity (nearestNeighborIntensity d) 0).toNNReal
    Tendsto (fun β : ℝ≥0 => 2 * d * (nearestNeighborProbability d β : ℝ))
      (𝓝[<] b) (𝓝 (2 * d * (nearestNeighborProbability d b : ℝ))) := by
  have h : Continuous (fun β : ℝ≥0 => 2 * d * (nearestNeighborProbability d β : ℝ)) := by
    simp_rw [nearestNeighborProbability_coe]
    fun_prop
  exact h.continuousAt.tendsto.mono_left nhdsWithin_le_nhds

/-- The actual critical signed correction remains uniformly smaller than one. -/
theorem abs_laceCosineTransform_nearestNeighbor_critical_le (hd : 50000 ≤ d)
    (k : Fin d → ℝ) :
    let b := (rootCriticalIntensity (nearestNeighborIntensity d) 0).toNNReal
    |latticeCosineTransform (laceSum (intensityProfile (nearestNeighborIntensity d) b) 0) k| ≤
      1 / 1000 := by
  let b := (rootCriticalIntensity (nearestNeighborIntensity d) 0).toNNReal
  have : NeBot (𝓝[<] b) := nhdsLT_neBot_of_exists_lt ⟨0, critical_intensity_pos hd⟩
  apply le_of_tendsto (tendsto_laceCosineTransform_nearestNeighbor_critical hd k).abs
  filter_upwards [self_mem_nhdsWithin] with β hβ
  have hχ := chi_nearestNeighborIntensity_ne_top_below_critical hd β hβ
  have hweak := fourierBootstrap_nearestNeighborIntensity_le_of_chi_ne_top hd β hχ
  have hm := laceCoefficient_mass_nearestNeighborIntensity_le_of_chi_ne_top hd β hχ
  have hs := summable_laceSum _ 0 (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hm)
  have h := abs_tsum_mul_re_addChar_le hs (latticeCharacter k)
  simp only [latticeCharacter_re] at h
  refine h.trans ?_
  rw [intensityProfile_nearestNeighborIntensity] at hχ hweak ⊢
  have hw := hweak.trans (by norm_num : (17 : ℝ) / 10 ≤ 2)
  refine (nn_tsum_abs_laceSum_le (by omega) _ hχ
    (nn_step_mass_le_of_fourierBootstrap_le _ hw)
    ((fourierBootstrap_le_iff _ _).mp hw).2.1).trans ?_
  have hdR : (50000 : ℝ) ≤ d := by exact_mod_cast hd
  apply (div_le_iff₀ (by linarith : (0 : ℝ) < d)).mpr
  linarith

/-- The critical step mass and actual signed correction satisfy the exact
zero-frequency normalization. -/
@[tag "VQ2V"]
theorem nn_critical_mass_normalization (hd : 50000 ≤ d) :
    let b := (rootCriticalIntensity (nearestNeighborIntensity d) 0).toNNReal
    let q := intensityProfile (nearestNeighborIntensity d) b
    (2 * d * (nearestNeighborProbability d b : ℝ)) * (1 + ∑' y, laceSum q 0 y) = 1 := by
  let b := (rootCriticalIntensity (nearestNeighborIntensity d) 0).toNNReal
  let q := intensityProfile (nearestNeighborIntensity d) b
  let m := ∑' y, laceSum q 0 y
  have : NeBot (𝓝[<] b) := nhdsLT_neBot_of_exists_lt ⟨0, critical_intensity_pos hd⟩
  have hm : |m| ≤ 1 / 1000 := by
    simpa only [latticeCosineTransform_at_zero] using
      abs_laceCosineTransform_nearestNeighbor_critical_le hd 0
  have hden : 1 + m ≠ 0 := by have h := (abs_le.mp hm).1; linarith
  have hmcont : Tendsto (fun β : ℝ≥0 =>
      ∑' y, laceSum (intensityProfile (nearestNeighborIntensity d) β) 0 y) (𝓝[<] b) (𝓝 m) := by
    simpa only [latticeCosineTransform_at_zero] using
      tendsto_laceCosineTransform_nearestNeighbor_critical hd 0
  have hlim := (tendsto_nearestNeighbor_step_critical (d := d)).add
    (hmcont.div (tendsto_const_nhds.add hmcont) hden)
  have heq : (1 : ℝ) = 2 * d * (nearestNeighborProbability d b : ℝ) + m / (1 + m) := by
    apply tendsto_nhds_unique (tendsto_susceptibilityWalkParameter_nearestNeighbor_critical hd)
    apply hlim.congr'
    filter_upwards [self_mem_nhdsWithin] with β hβ
    have hχ := chi_nearestNeighborIntensity_ne_top_below_critical hd β hβ
    have hw := (fourierBootstrap_nearestNeighborIntensity_le_of_chi_ne_top hd β hχ).trans
      (by norm_num : (17 : ℝ) / 10 ≤ 2)
    simp only [Pi.div_apply]
    rw [intensityProfile_nearestNeighborIntensity] at hχ hw ⊢
    exact (nn_mass_normalization (by omega) _ hχ
      (nn_step_mass_le_of_fourierBootstrap_le _ hw)
      ((fourierBootstrap_le_iff _ _).mp hw).2.1).symm
  dsimp only
  apply (eq_div_iff hden).mp
  field_simp at heq ⊢
  linarith

private theorem subcritical_fourier_quotient_data (hd : 50000 ≤ d) (β : ℝ≥0)
    (hβ : β < (rootCriticalIntensity (nearestNeighborIntensity d) 0).toNNReal)
    (k : Fin d → ℝ) :
    let q := intensityProfile (nearestNeighborIntensity d) β
    let P := latticeCosineTransform (laceSum q 0) k
    let j := 2 * d * (nearestNeighborProbability d β : ℝ)
    let den := 1 - j * nearestNeighborSymbol k * (1 + P)
    0 < den ∧ tauFourier q k = (1 + P) / den ∧
      (1 + P) * (1 - susceptibilityWalkParameter q * nearestNeighborSymbol k) ≤
        (17 / 10 : ℝ) * den := by
  let q := intensityProfile (nearestNeighborIntensity d) β
  let P := latticeCosineTransform (laceSum q 0) k
  let j := 2 * d * (nearestNeighborProbability d β : ℝ)
  let den := 1 - j * nearestNeighborSymbol k * (1 + P)
  have hχ := chi_nearestNeighborIntensity_ne_top_below_critical hd β hβ
  have hF := fourierBootstrap_nearestNeighborIntensity_le_of_chi_ne_top hd β hχ
  have hweak := hF.trans (by norm_num : (17 : ℝ) / 10 ≤ 2)
  have hK : fourierRatioSup q ≤ 17 / 10 := ((fourierBootstrap_le_iff _ _).mp hF).2.1
  have hmass := laceCoefficient_mass_nearestNeighborIntensity_le_of_chi_ne_top hd β hχ
  have hs := summable_laceSum q 0 (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hmass)
  have hPmass : |P| ≤ 44 / (d : ℝ) := by
    have h := abs_tsum_mul_re_addChar_le hs (latticeCharacter k)
    simp only [latticeCharacter_re] at h
    refine h.trans ?_
    dsimp only [q]
    rw [intensityProfile_nearestNeighborIntensity] at hχ hweak ⊢
    exact nn_tsum_abs_laceSum_le (by omega) _ hχ
      (nn_step_mass_le_of_fourierBootstrap_le _ hweak)
      ((fourierBootstrap_le_iff _ _).mp hweak).2.1
  have hdR : (50000 : ℝ) ≤ d := by exact_mod_cast hd
  have hsmall : (44 : ℝ) / d < 1 := (div_lt_one (by linarith)).mpr (by linarith)
  have hN : 0 < 1 + P := by have h := (abs_le.mp hPmass).1; linarith
  have heq : tauFourier q k = 1 + P + (1 + P) * j * nearestNeighborSymbol k *
      tauFourier q k := by
    dsimp only [q, P, j]
    rw [intensityProfile_nearestNeighborIntensity] at hχ hweak ⊢
    exact nn_actual_fourier_equation hd _ hχ hweak k
  have hT : 0 < tauFourier q k := by
    dsimp only [q]
    rw [intensityProfile_nearestNeighborIntensity] at hχ hweak ⊢
    exact nn_actual_tauFourier_pos hd _ hχ hweak k
  have hden : 0 < den := (fourier_denominator_pos hT.le hN heq).2
  have hprod : tauFourier q k * den = 1 + P := by dsimp only [den]; nlinarith [heq]
  refine ⟨hden, (eq_div_iff hden.ne').mpr hprod, ?_⟩
  have hratio : tauFourier q k * (1 - susceptibilityWalkParameter q * nearestNeighborSymbol k) ≤
      17 / 10 := (le_abs_self _).trans
    ((le_ciSup (bddAbove_fourierRatio (by omega) q hχ) k).trans hK)
  calc
    _ = (tauFourier q k * (1 - susceptibilityWalkParameter q * nearestNeighborSymbol k)) *
        den := by rw [← hprod]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hratio hden.le

private theorem critical_fourier_denominator_bound (hd : 50000 ≤ d) (k : Fin d → ℝ) :
    let b := (rootCriticalIntensity (nearestNeighborIntensity d) 0).toNNReal
    let q := intensityProfile (nearestNeighborIntensity d) b
    let P := latticeCosineTransform (laceSum q 0) k
    (1 + P) * (1 - nearestNeighborSymbol k) ≤ (17 / 10 : ℝ) *
      (1 - (2 * d * (nearestNeighborProbability d b : ℝ)) * nearestNeighborSymbol k * (1 + P)) := by
  let b := (rootCriticalIntensity (nearestNeighborIntensity d) 0).toNNReal
  have : NeBot (𝓝[<] b) := nhdsLT_neBot_of_exists_lt ⟨0, critical_intensity_pos hd⟩
  have hP := tendsto_laceCosineTransform_nearestNeighbor_critical hd k
  have hj := tendsto_nearestNeighbor_step_critical (d := d)
  have hlam := tendsto_susceptibilityWalkParameter_nearestNeighbor_critical hd
  have hW := (tendsto_const_nhds (x := (1 : ℝ))).sub (hlam.mul_const (nearestNeighborSymbol k))
  have hN := (tendsto_const_nhds (x := (1 : ℝ))).add hP
  have hden := (tendsto_const_nhds (x := (1 : ℝ))).sub
    ((hj.mul_const (nearestNeighborSymbol k)).mul hN)
  apply le_of_tendsto_of_tendsto (by simpa only [one_mul] using hN.mul hW)
    (hden.const_mul (17 / 10))
  filter_upwards [self_mem_nhdsWithin] with β hβ
  exact (subcritical_fourier_quotient_data hd β hβ k).2.2

/-- The actual critical Fourier denominator is positive away from the symbol
singularity, as a consequence of the subcritical infrared bound. -/
theorem nn_critical_fourier_denominator_pos (hd : 50000 ≤ d) (k : Fin d → ℝ)
    (hk : 0 < 1 - nearestNeighborSymbol k) :
    let b := (rootCriticalIntensity (nearestNeighborIntensity d) 0).toNNReal
    let P := latticeCosineTransform (laceSum (intensityProfile (nearestNeighborIntensity d) b) 0) k
    0 < 1 - (2 * d * (nearestNeighborProbability d b : ℝ)) * nearestNeighborSymbol k * (1 + P) := by
  have h := critical_fourier_denominator_bound hd k
  have hP := (abs_le.mp (abs_laceCosineTransform_nearestNeighbor_critical_le hd k)).1
  dsimp only at h hP ⊢
  have hN : 0 < 1 + latticeCosineTransform
      (laceSum (intensityProfile (nearestNeighborIntensity d)
        (rootCriticalIntensity (nearestNeighborIntensity d) 0).toNNReal) 0) k := by linarith
  nlinarith [mul_pos hN hk]

/-- The actual subcritical two-point transforms have the stated Abel limit at
each frequency off the symbol singularity. No critical two-point series is used. -/
@[tag "T3YO"]
theorem tendsto_tauFourier_nearestNeighbor_critical (hd : 50000 ≤ d) (k : Fin d → ℝ)
    (hk : 0 < 1 - nearestNeighborSymbol k) :
    let b := (rootCriticalIntensity (nearestNeighborIntensity d) 0).toNNReal
    let P := latticeCosineTransform (laceSum (intensityProfile (nearestNeighborIntensity d) b) 0) k
    Tendsto (fun β : ℝ≥0 => tauFourier (intensityProfile (nearestNeighborIntensity d) β) k)
      (𝓝[<] b) (𝓝 ((1 + P) /
        (1 - (2 * d * (nearestNeighborProbability d b : ℝ)) *
          nearestNeighborSymbol k * (1 + P)))) := by
  have hP := tendsto_laceCosineTransform_nearestNeighbor_critical hd k
  have hN := (tendsto_const_nhds (x := (1 : ℝ))).add hP
  have hden := (tendsto_const_nhds (x := (1 : ℝ))).sub
    (((tendsto_nearestNeighbor_step_critical (d := d)).mul_const (nearestNeighborSymbol k)).mul hN)
  apply (hN.div hden (nn_critical_fourier_denominator_pos hd k hk).ne').congr'
  filter_upwards [self_mem_nhdsWithin] with β hβ
  exact (subcritical_fourier_quotient_data hd β hβ k).2.1.symm

/-- The critical Abel quotient is positive and retains the actual improved
infrared constant `17/10`. -/
@[tag "KIPV"]
theorem nn_critical_fourier_quotient_bounds (hd : 50000 ≤ d) (k : Fin d → ℝ)
    (hk : 0 < 1 - nearestNeighborSymbol k) :
    let b := (rootCriticalIntensity (nearestNeighborIntensity d) 0).toNNReal
    let P := latticeCosineTransform (laceSum (intensityProfile (nearestNeighborIntensity d) b) 0) k
    let T := (1 + P) /
      (1 - (2 * d * (nearestNeighborProbability d b : ℝ)) * nearestNeighborSymbol k * (1 + P))
    0 < T ∧ T ≤ (17 / 10 : ℝ) / (1 - nearestNeighborSymbol k) := by
  have hden := nn_critical_fourier_denominator_pos hd k hk
  have hP := (abs_le.mp (abs_laceCosineTransform_nearestNeighbor_critical_le hd k)).1
  dsimp only at hden hP ⊢
  constructor
  · exact div_pos (by linarith) hden
  · apply (le_div_iff₀ hk).mpr
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hden).mpr
    exact critical_fourier_denominator_bound hd k

private theorem ae_positive_symbol_deficit (hd : 0 < d) :
    ∀ᵐ k ∂volume.restrict (ball (0 : Fin d → ℝ) π), 0 < 1 - nearestNeighborSymbol k := by
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hae : ∀ᵐ k ∂volume.restrict (ball (0 : Fin d → ℝ) π), k ≠ 0 :=
    ae_restrict_of_ae (compl_mem_ae_iff.mpr (measure_singleton 0))
  filter_upwards [hae, ae_restrict_mem measurableSet_ball] with k hk0 hk
  have h := le_one_sub_lazySymbol hd hk
  have he : 1 - (1 / 2 + (2 * d : ℝ)⁻¹ * ∑ i, cos (k i)) =
      (1 - nearestNeighborSymbol k) / 2 := by
    simp only [nearestNeighborSymbol, mul_inv_rev]
    ring
  rw [he] at h
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hpos : 0 < ‖k‖ ^ 2 / (d * π ^ 2) :=
    div_pos (pow_pos (norm_pos_iff.mpr hk0) _) (mul_pos hdR (pow_pos pi_pos _))
  linarith

private theorem integrableOn_critical_walk_reciprocal (hd : 50000 ≤ d) :
    IntegrableOn (fun k : Fin d → ℝ => (1 - nearestNeighborSymbol k)⁻¹) (ball 0 π) := by
  let μ : Measure (Fin d → ℝ) := Measure.pi fun _ => volume.restrict (Ioo (-π) π)
  have hsix : Integrable (fun k : Fin d → ℝ => (1 - nearestNeighborSymbol k)⁻¹ ^ 6) μ := by
    have h := integrableOn_nearestNeighborSymbol_critical_inv_six (by omega : 1000 ≤ d)
    simpa only [IntegrableOn, volume_restrict_pi_ball_eq_pi_Ioo, μ,
      nearestNeighborSymbol, one_div, inv_pow] using h
  have hmeas : Measurable (fun k : Fin d → ℝ => (1 - nearestNeighborSymbol k)⁻¹) := by
    unfold nearestNeighborSymbol
    fun_prop
  have hint : Integrable (fun k : Fin d → ℝ => (1 - nearestNeighborSymbol k)⁻¹) μ := by
    apply ((integrable_const 1).add hsix).mono_nonneg hmeas.aestronglyMeasurable
    · exact Eventually.of_forall fun k => inv_nonneg.mpr
        (sub_nonneg.mpr (abs_le.mp (nearestNeighborSymbol_abs_le_one (by omega) k)).2)
    · apply Eventually.of_forall
      intro k
      by_cases h : (1 - nearestNeighborSymbol k)⁻¹ ≤ 1
      · exact h.trans (le_add_of_nonneg_right (by positivity))
      · exact (le_self_pow₀ (le_of_not_ge h) (by norm_num : (6 : ℕ) ≠ 0)).trans
          (le_add_of_nonneg_left (by norm_num))
  simpa only [IntegrableOn, volume_restrict_pi_ball_eq_pi_Ioo, μ] using hint

/-- The actual critical Abel quotient is integrable on the physical Fourier box.
Values assigned by totalized division on the null singular set are immaterial. -/
theorem integrableOn_nn_critical_fourier_quotient (hd : 50000 ≤ d) :
    let b := (rootCriticalIntensity (nearestNeighborIntensity d) 0).toNNReal
    let P := latticeCosineTransform (laceSum (intensityProfile (nearestNeighborIntensity d) b) 0)
    IntegrableOn (fun k => (1 + P k) /
      (1 - (2 * d * (nearestNeighborProbability d b : ℝ)) * nearestNeighborSymbol k * (1 + P k)))
      (ball (0 : Fin d → ℝ) π) := by
  let b := (rootCriticalIntensity (nearestNeighborIntensity d) 0).toNNReal
  let P := latticeCosineTransform (laceSum (intensityProfile (nearestNeighborIntensity d) b) 0)
  have hP : Continuous P := continuous_latticeCosineTransform
    (summable_laceSum_nearestNeighbor_critical hd 0)
  have hD : Continuous (nearestNeighborSymbol (d := d)) := by
    unfold nearestNeighborSymbol
    fun_prop
  have hm : Measurable (fun k => (1 + P k) /
      (1 - (2 * d * (nearestNeighborProbability d b : ℝ)) *
        nearestNeighborSymbol k * (1 + P k))) := by
    fun_prop
  apply ((integrableOn_critical_walk_reciprocal hd).const_mul (17 / 10 : ℝ)).mono'
    hm.aestronglyMeasurable
  filter_upwards [ae_positive_symbol_deficit (by omega : 0 < d)] with k hk
  have h := nn_critical_fourier_quotient_bounds hd k hk
  rw [Real.norm_eq_abs, abs_of_pos h.1]
  simpa only [div_eq_mul_inv] using h.2

private theorem subcritical_fourier_dominated (hd : 50000 ≤ d) (β : ℝ≥0)
    (hβ : β < (rootCriticalIntensity (nearestNeighborIntensity d) 0).toNNReal)
    (k : Fin d → ℝ) (hk : 0 < 1 - nearestNeighborSymbol k) :
    |tauFourier (intensityProfile (nearestNeighborIntensity d) β) k| ≤
      (17 / 5 : ℝ) * (1 - nearestNeighborSymbol k)⁻¹ := by
  let q := intensityProfile (nearestNeighborIntensity d) β
  have hχ := chi_nearestNeighborIntensity_ne_top_below_critical hd β hβ
  have hF := fourierBootstrap_nearestNeighborIntensity_le_of_chi_ne_top hd β hχ
  have hK := ((fourierBootstrap_le_iff _ _).mp hF).2.1
  have hr := susceptibilityWalkParameter_mem_Ico q hχ
  have hC := walk_reciprocal_le hr.1 hr.2
    (abs_le.mp (nearestNeighborSymbol_abs_le_one (by omega) k)).1 (by linarith :
      nearestNeighborSymbol k < 1)
  have hfactor : (2 : ℝ) / (1 + susceptibilityWalkParameter q) ≤ 2 := by
    apply (div_le_iff₀ (by linarith [hr.1])).mpr
    linarith [hr.1]
  have hC' : nearestNeighborResolvent (susceptibilityWalkParameter q) k ≤
      2 * (1 - nearestNeighborSymbol k)⁻¹ :=
    hC.trans (mul_le_mul_of_nonneg_right hfactor (inv_nonneg.mpr hk.le))
  calc
    _ ≤ (17 / 10 : ℝ) * nearestNeighborResolvent (susceptibilityWalkParameter q) k :=
      abs_tauFourier_le_mul_resolvent_of_fourierRatioSup_le (by omega) q hχ hK k
    _ ≤ (17 / 10 : ℝ) * (2 * (1 - nearestNeighborSymbol k)⁻¹) :=
      mul_le_mul_of_nonneg_left hC' (by norm_num)
    _ = _ := by ring

/-- Critical connection probabilities are the inverse Fourier coefficients of
the actual Abel quotient. Critical susceptibility is infinite, so the formula
does not identify an unordered critical two-point Fourier series. -/
@[tag "ATL6"]
theorem tau_nearestNeighbor_critical_eq_inverse_fourier (hd : 50000 ≤ d) (x : Fin d → ℤ) :
    let b := (rootCriticalIntensity (nearestNeighborIntensity d) 0).toNNReal
    let q := intensityProfile (nearestNeighborIntensity d) b
    let P := latticeCosineTransform (laceSum q 0)
    (tau q 0 x).toReal = ((2 * π) ^ d)⁻¹ * ∫ k in ball (0 : Fin d → ℝ) π,
      cos (∑ i, k i * (x i : ℝ)) * ((1 + P k) /
        (1 - (2 * d * (nearestNeighborProbability d b : ℝ)) *
          nearestNeighborSymbol k * (1 + P k))) := by
  let b := (rootCriticalIntensity (nearestNeighborIntensity d) 0).toNNReal
  let q := intensityProfile (nearestNeighborIntensity d) b
  let P := latticeCosineTransform (laceSum q 0)
  let T (k : Fin d → ℝ) := (1 + P k) /
    (1 - (2 * d * (nearestNeighborProbability d b : ℝ)) * nearestNeighborSymbol k * (1 + P k))
  let F (β : ℝ≥0) (k : Fin d → ℝ) :=
    cos (∑ i, k i * (x i : ℝ)) * tauFourier (intensityProfile (nearestNeighborIntensity d) β) k
  have : NeBot (𝓝[<] b) := nhdsLT_neBot_of_exists_lt ⟨0, critical_intensity_pos hd⟩
  have hmeas : ∀ᶠ β in 𝓝[<] b, AEStronglyMeasurable (F β)
      (volume.restrict (ball (0 : Fin d → ℝ) π)) := by
    filter_upwards [self_mem_nhdsWithin] with β hβ
    have hχ := chi_nearestNeighborIntensity_ne_top_below_critical hd β hβ
    have hs : Summable (fun y =>
        (tau (intensityProfile (nearestNeighborIntensity d) β) 0 y).toReal) :=
      ENNReal.summable_toReal (by rwa [← chi_eq_tsum_tau])
    have hcont := continuous_latticeCosineTransform hs
    apply Continuous.aestronglyMeasurable
    dsimp only [F, tauFourier]
    fun_prop
  have hbound : ∀ᶠ β in 𝓝[<] b, ∀ᵐ k ∂volume.restrict (ball (0 : Fin d → ℝ) π),
      ‖F β k‖ ≤ (17 / 5 : ℝ) * (1 - nearestNeighborSymbol k)⁻¹ := by
    filter_upwards [self_mem_nhdsWithin] with β hβ
    filter_upwards [ae_positive_symbol_deficit (by omega : 0 < d)] with k hk
    calc
      _ ≤ |tauFourier (intensityProfile (nearestNeighborIntensity d) β) k| := by
        dsimp only [F]
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_of_le_one_left (abs_nonneg _) (abs_cos_le_one _)
      _ ≤ _ := subcritical_fourier_dominated hd β hβ k hk
  have hlim : ∀ᵐ k ∂volume.restrict (ball (0 : Fin d → ℝ) π),
      Tendsto (fun β => F β k) (𝓝[<] b) (𝓝 (cos (∑ i, k i * (x i : ℝ)) * T k)) := by
    filter_upwards [ae_positive_symbol_deficit (by omega : 0 < d)] with k hk
    exact (tendsto_tauFourier_nearestNeighbor_critical hd k hk).const_mul _
  have hint := tendsto_integral_filter_of_dominated_convergence
    (fun k : Fin d → ℝ => (17 / 5 : ℝ) * (1 - nearestNeighborSymbol k)⁻¹)
    hmeas hbound ((integrableOn_critical_walk_reciprocal hd).const_mul (17 / 5 : ℝ)) hlim
  have htau : Tendsto (fun β : ℝ≥0 =>
      (tau (intensityProfile (nearestNeighborIntensity d) β) 0 x).toReal)
      (𝓝[<] b) (𝓝 ((tau q 0 x).toReal)) := by
    have h := (continuousWithinAt_tau_Iic (q := intensityProfile (nearestNeighborIntensity d))
      (fun _ _ hab e => intensityProfile_mono _ hab e)
      (fun e => (continuous_intensityProfile _ e).subtype_mk _) 0 x b).tendsto.mono_left
      (nhdsWithin_mono _ Iio_subset_Iic_self)
    exact (ENNReal.continuousAt_toReal (measure_ne_top _ _)).tendsto.comp h
  apply tendsto_nhds_unique htau
  apply (hint.const_mul (((2 * π) ^ d)⁻¹)).congr'
  filter_upwards [self_mem_nhdsWithin] with β hβ
  have hχ := chi_nearestNeighborIntensity_ne_top_below_critical hd β hβ
  have hs : Summable (fun y =>
      (tau (intensityProfile (nearestNeighborIntensity d) β) 0 y).toReal) :=
    ENNReal.summable_toReal (by rwa [← chi_eq_tsum_tau])
  have heven : Function.Even (fun y =>
      (tau (intensityProfile (nearestNeighborIntensity d) β) 0 y).toReal) := by
    rw [intensityProfile_nearestNeighborIntensity]
    exact even_tau_rooted _ (homogeneous_zdGraph_add _)
  exact (eq_normalized_integral_cos_mul_cosineTransform hs heven x).symm

/-- The improved second-difference estimate passes to the critical Abel
quotient wherever all three resolvent frequencies are nonsingular. -/
@[tag "C8QY"]
theorem nn_critical_fourier_second_difference_le (hd : 50000 ≤ d) (k l : Fin d → ℝ)
    (hk : 0 < 1 - nearestNeighborSymbol k)
    (hm : 0 < 1 - nearestNeighborSymbol (l - k))
    (h0 : 0 < 1 - nearestNeighborSymbol l)
    (hp : 0 < 1 - nearestNeighborSymbol (l + k)) :
    let b := (rootCriticalIntensity (nearestNeighborIntensity d) 0).toNNReal
    let q := intensityProfile (nearestNeighborIntensity d) b
    let P := latticeCosineTransform (laceSum q 0)
    let T := fun t => (1 + P t) /
      (1 - (2 * d * (nearestNeighborProbability d b : ℝ)) * nearestNeighborSymbol t * (1 + P t))
    |T (l - k) + T (l + k) - 2 * T l| ≤ (9 / 25 : ℝ) * bootstrapMajorant 1 k l := by
  let b := (rootCriticalIntensity (nearestNeighborIntensity d) 0).toNNReal
  have : NeBot (𝓝[<] b) := nhdsLT_neBot_of_exists_lt ⟨0, critical_intensity_pos hd⟩
  have hT := (((tendsto_tauFourier_nearestNeighbor_critical hd (l - k) hm).add
    (tendsto_tauFourier_nearestNeighbor_critical hd (l + k) hp)).sub
    ((tendsto_tauFourier_nearestNeighbor_critical hd l h0).const_mul 2)).abs
  have hC (t : Fin d → ℝ) (ht : 0 < 1 - nearestNeighborSymbol t) :
      Tendsto (fun β : ℝ≥0 => nearestNeighborResolvent
        (susceptibilityWalkParameter (intensityProfile (nearestNeighborIntensity d) β)) t)
        (𝓝[<] b) (𝓝 (nearestNeighborResolvent 1 t)) := by
    have h := (tendsto_const_nhds (x := (1 : ℝ))).sub
      ((tendsto_susceptibilityWalkParameter_nearestNeighbor_critical hd).mul_const
        (nearestNeighborSymbol t))
    exact h.inv₀ (by simpa only [one_mul] using ht.ne')
  have hU : Tendsto (fun β : ℝ≥0 => bootstrapMajorant
      (susceptibilityWalkParameter (intensityProfile (nearestNeighborIntensity d) β)) k l)
      (𝓝[<] b) (𝓝 (bootstrapMajorant 1 k l)) :=
    ((((hC (l - k) hm).mul (hC l h0)).add ((hC l h0).mul (hC (l + k) hp))).add
      ((hC (l - k) hm).mul (hC (l + k) hp))).const_mul (200 * (1 - nearestNeighborSymbol k))
  apply le_of_tendsto_of_tendsto hT (hU.const_mul (9 / 25))
  filter_upwards [self_mem_nhdsWithin] with β hβ
  have hχ := chi_nearestNeighborIntensity_ne_top_below_critical hd β hβ
  have hw := (fourierBootstrap_nearestNeighborIntensity_le_of_chi_ne_top hd β hχ).trans
    (by norm_num : (17 : ℝ) / 10 ≤ 2)
  rw [intensityProfile_nearestNeighborIntensity] at hχ hw ⊢
  have hsecond := (spatialMoment_sq_lt_top_of_finiteRange_of_transitive _ 0
    (by norm_num : (0 : ℝ) ≤ 1)
    (homogeneous_zdGraph_eq_zero_of_one_lt_norm (nearestNeighborProbability d β))
    (homogeneous_zdGraph_transitive (nearestNeighborProbability d β)) hχ).ne
  have h := abs_fwdDiff_two_tauFourier_le_mul_majorant_of_fourierDifferenceSup_le
    (by omega) _ hχ hsecond (nn_fourierDifferenceSup_le_nine_twenty_fifths hd _ hχ hw) (l := l) hk
  simpa only [fwdDiff_two_at_sub] using h

end PercLib.Percolation.Bond.Lace
