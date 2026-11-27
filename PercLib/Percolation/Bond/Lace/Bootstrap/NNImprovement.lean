/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New proofs for this project; no upstream Lean code is copied.
-/
module

public import PercLib.Percolation.Bond.Lace.Bootstrap.NNWeightedCoefficient
public import PercLib.Percolation.Bond.Lace.Expansion.SecondDifferenceAlgebra
public import PercLib.Percolation.Bond.Lace.Expansion.WeightedKernel
public import PercLib.Analysis.WalkReciprocal

/-!
# Strict improvement of the actual nearest-neighbour Fourier bootstrap

The proved coefficient mass and cosine-weighted coefficient mass control the
canonical signed kernel. Its actual Fourier equation then improves the weak
bootstrap at every dimension at least `50000`.

## Main results

* `nn_fourierRatioSup_le_seventeen_tenths`: the actual ratio is at most `17/10`.
* `nn_fourierDifferenceSup_le_nine_twenty_fifths`: the actual second-difference
  ratio is at most `9/25`.
* `nn_fourierBootstrap_improves`: the complete bootstrap improves from `2` to `17/10`.

Only finite susceptibility and the canonical weak bootstrap are assumed.
The coefficient estimates and Fourier equation are proved inputs from the library.
-/

@[expose] public section
noncomputable section

open Real PercLib.Analysis PercLib.Models.Site
open scoped ENNReal

namespace PercLib.Percolation.Bond.Lace

variable {d : ℕ}

private theorem nn_total_coefficient_mass_ne_top (hd : 50000 ≤ d) (p : unitInterval)
    (hchi : chi (homogeneousProfile (zdGraph d) p) 0 ≠ ⊤)
    (hweak : fourierBootstrap (homogeneousProfile (zdGraph d) p) ≤ 2) :
    (∑' n : ℕ, ∑' y, laceCoefficient (homogeneousProfile (zdGraph d) p) n 0 y) ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (nn_laceCoefficient_total_mass_le (by omega) p hchi
      (nn_step_mass_le_of_fourierBootstrap_le p hweak)
      ((fourierBootstrap_le_iff _ _).mp hweak).2.1)

private theorem nn_signed_mass_le_small (hd : 50000 ≤ d) (p : unitInterval)
    (hchi : chi (homogeneousProfile (zdGraph d) p) 0 ≠ ⊤)
    (hweak : fourierBootstrap (homogeneousProfile (zdGraph d) p) ≤ 2) :
    (∑' y, |laceSum (homogeneousProfile (zdGraph d) p) 0 y|) ≤ 1 / 1000 := by
  apply (nn_tsum_abs_laceSum_le (by omega) p hchi
    (nn_step_mass_le_of_fourierBootstrap_le p hweak)
    ((fourierBootstrap_le_iff _ _).mp hweak).2.1).trans
  have hdR : (50000 : ℝ) ≤ d := by exact_mod_cast hd
  apply (div_le_iff₀ (by linarith : (0 : ℝ) < d)).mpr
  linarith

private theorem nn_lace_cosine_moment_le (hd : 50000 ≤ d) (p : unitInterval)
    (hchi : chi (homogeneousProfile (zdGraph d) p) 0 ≠ ⊤)
    (hweak : fourierBootstrap (homogeneousProfile (zdGraph d) p) ≤ 2) (k : Fin d → ℝ) :
    (∑' y, |laceSum (homogeneousProfile (zdGraph d) p) 0 y| *
      (1 - cos (∑ i, k i * (y i : ℝ)))) ≤ (1 / 3 : ℝ) * (1 - nearestNeighborSymbol k) := by
  have hW := nn_laceCoefficient_weighted_mass_le hd p hchi hweak k
  have hf := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hW
  have h := tsum_mul_abs_laceSum_le_weightedCoefficientMass
    (homogeneousProfile (zdGraph d) p) 0
    (fun y => 1 - cos (∑ i, k i * (y i : ℝ)))
    (fun y => sub_nonneg.mpr (cos_le_one _)) hf
  have hg : 0 ≤ 1 - nearestNeighborSymbol k :=
    sub_nonneg.mpr (abs_le.mp (nearestNeighborSymbol_abs_le_one (by omega) k)).2
  have hR := ENNReal.toReal_mono ENNReal.ofReal_ne_top hW
  rw [ENNReal.toReal_ofReal (by positivity)] at hR
  simpa only [mul_comm] using h.trans hR

private theorem nn_lace_cosine_variation_le (hd : 50000 ≤ d) (p : unitInterval)
    (hchi : chi (homogeneousProfile (zdGraph d) p) 0 ≠ ⊤)
    (hweak : fourierBootstrap (homogeneousProfile (zdGraph d) p) ≤ 2) (k : Fin d → ℝ) :
    |latticeCosineTransform (laceSum (homogeneousProfile (zdGraph d) p) 0) k -
      ∑' y, laceSum (homogeneousProfile (zdGraph d) p) 0 y| ≤
        (1 / 3 : ℝ) * (1 - nearestNeighborSymbol k) := by
  have h := abs_laceSum_cosine_sub_mass_le_weightedCoefficientMass
    (homogeneousProfile (zdGraph d) p) 0 (fun y => ∑ i, k i * (y i : ℝ))
    (nn_total_coefficient_mass_ne_top hd p hchi hweak)
  have hW := nn_laceCoefficient_weighted_mass_le hd p hchi hweak k
  have hg : 0 ≤ 1 - nearestNeighborSymbol k :=
    sub_nonneg.mpr (abs_le.mp (nearestNeighborSymbol_abs_le_one (by omega) k)).2
  have hR := ENNReal.toReal_mono ENNReal.ofReal_ne_top hW
  rw [ENNReal.toReal_ofReal (by positivity)] at hR
  exact h.trans hR

private theorem nn_lace_cosine_abs_le (hd : 50000 ≤ d) (p : unitInterval)
    (hchi : chi (homogeneousProfile (zdGraph d) p) 0 ≠ ⊤)
    (hweak : fourierBootstrap (homogeneousProfile (zdGraph d) p) ≤ 2) (k : Fin d → ℝ) :
    |latticeCosineTransform (laceSum (homogeneousProfile (zdGraph d) p) 0) k| ≤
      1 / 1000 := by
  have h := abs_tsum_mul_re_addChar_le
    (summable_laceSum _ 0 (nn_total_coefficient_mass_ne_top hd p hchi hweak))
    (latticeCharacter k)
  simp only [latticeCharacter_re] at h
  exact h.trans (nn_signed_mass_le_small hd p hchi hweak)

/-- The actual nearest-neighbour transform satisfies the canonical signed-kernel
equation throughout the weak-bootstrap regime. -/
theorem nn_actual_fourier_equation (hd : 50000 ≤ d) (p : unitInterval)
    (hchi : chi (homogeneousProfile (zdGraph d) p) 0 ≠ ⊤)
    (hweak : fourierBootstrap (homogeneousProfile (zdGraph d) p) ≤ 2) (k : Fin d → ℝ) :
    let q := homogeneousProfile (zdGraph d) p
    let P := latticeCosineTransform (laceSum q 0) k
    tauFourier q k = 1 + P + (1 + P) * (2 * d * (p : ℝ)) *
      nearestNeighborSymbol k * tauFourier q k := by
  let q := homogeneousProfile (zdGraph d) p
  have hτ : (∑' y, tau q 0 y) ≠ ⊤ := by rwa [← chi_eq_tsum_tau]
  have h := canonical_lace_real_fourier_equation q (homogeneous_zdGraph_add p)
    (nn_step_mass_ne_top p) hτ (nn_total_coefficient_mass_ne_top hd p hchi hweak)
    (latticeCharacter k)
  dsimp only at h ⊢
  simp only [q, latticeCharacter_re, nn_offDiagonal_toReal] at h
  have hJ : (∑' y, (homogeneousProfile (zdGraph d) p s(0, y) : ℝ) *
      cos (∑ i, k i * (y i : ℝ))) = 2 * d * (p : ℝ) * nearestNeighborSymbol k :=
    latticeCosineTransform_homogeneous_zdGraph (by omega) p k
  rw [hJ] at h
  simpa only [q, tauFourier_def, latticeCosineTransform, mul_assoc] using h

/-- The actual nearest-neighbour Fourier transform is strictly positive in the
finite-susceptibility weak-bootstrap regime. -/
theorem nn_actual_tauFourier_pos (hd : 50000 ≤ d) (p : unitInterval)
    (hchi : chi (homogeneousProfile (zdGraph d) p) 0 ≠ ⊤)
    (hweak : fourierBootstrap (homogeneousProfile (zdGraph d) p) ≤ 2) (k : Fin d → ℝ) :
    0 < tauFourier (homogeneousProfile (zdGraph d) p) k := by
  let q := homogeneousProfile (zdGraph d) p
  have hτ : (∑' y, tau q 0 y) ≠ ⊤ := by rwa [← chi_eq_tsum_tau]
  have h := canonical_lace_real_fourier_pos q (homogeneous_zdGraph_add p)
    (nn_step_mass_ne_top p) hτ (nn_total_coefficient_mass_ne_top hd p hchi hweak)
    ((nn_signed_mass_le_small hd p hchi hweak).trans_lt (by norm_num))
    (latticeCharacter k)
  simpa only [q, tauFourier_def, latticeCharacter_re] using h.1

private theorem nn_step_mass_le_parameter_add (hd : 50000 ≤ d) (p : unitInterval)
    (hchi : chi (homogeneousProfile (zdGraph d) p) 0 ≠ ⊤)
    (hweak : fourierBootstrap (homogeneousProfile (zdGraph d) p) ≤ 2) :
    2 * d * (p : ℝ) ≤ susceptibilityWalkParameter (homogeneousProfile (zdGraph d) p) +
      1 / 999 := by
  have hs := summable_laceSum _ 0 (nn_total_coefficient_mass_ne_top hd p hchi hweak)
  have hm : |∑' y, laceSum (homogeneousProfile (zdGraph d) p) 0 y| ≤ 1 / 1000 := by
    apply le_trans _ (nn_signed_mass_le_small hd p hchi hweak)
    simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hs.norm
  have hn := nn_mass_normalization (by omega : 1000 ≤ d) p hchi
    (nn_step_mass_le_of_fourierBootstrap_le p hweak)
    ((fourierBootstrap_le_iff _ _).mp hweak).2.1
  have h := mass_le_of_normalization (by norm_num : (1 / 1000 : ℝ) < 1) hm hn
  norm_num at h ⊢
  exact h

private theorem nn_ratio_constant_le {j lam : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hj : j ≤ lam + 1 / 999) :
    1 + (2 * (1 / 1000 : ℝ) + 2 * 2 * (1 / 1000 + j * (1 / 3)) /
      (1 + lam)) / (1 - 1 / 1000) ≤ 17 / 10 := by
  have hr : (1 / 1000 + j * (1 / 3)) / (1 + lam) ≤
      (1 / 1000 : ℝ) + (1 + 1 / 999) / 6 := by
    apply (div_le_iff₀ (by linarith)).mpr
    nlinarith
  calc
    _ = 1 + (2 * (1 / 1000 : ℝ) + 4 *
        ((1 / 1000 + j * (1 / 3)) / (1 + lam))) / (1 - 1 / 1000) := by ring
    _ ≤ 1 + (2 * (1 / 1000 : ℝ) + 4 * (1 / 1000 + (1 + 1 / 999) / 6)) /
        (1 - 1 / 1000) := by gcongr
    _ ≤ 17 / 10 := by norm_num

/-- The actual nearest-neighbour Fourier ratio strictly improves the weak bound two. -/
theorem nn_fourierRatioSup_le_seventeen_tenths (hd : 50000 ≤ d) (p : unitInterval)
    (hchi : chi (homogeneousProfile (zdGraph d) p) 0 ≠ ⊤)
    (hweak : fourierBootstrap (homogeneousProfile (zdGraph d) p) ≤ 2) :
    fourierRatioSup (homogeneousProfile (zdGraph d) p) ≤ 17 / 10 := by
  let q := homogeneousProfile (zdGraph d) p
  let m := ∑' y, laceSum q 0 y
  have hd0 : 0 < d := by omega
  have hlam := susceptibilityWalkParameter_mem_Ico q hchi
  have hj := nn_step_mass_le_of_fourierBootstrap_le p hweak
  have hK := ((fourierBootstrap_le_iff _ _).mp hweak).2.1
  have hs := summable_laceSum q 0 (nn_total_coefficient_mass_ne_top hd p hchi hweak)
  have hm : |m| ≤ 1 / 1000 := by
    apply le_trans _ (nn_signed_mass_le_small hd p hchi hweak)
    simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hs.norm
  have hn := nn_mass_normalization (by omega : 1000 ≤ d) p hchi hj hK
  rw [fourierRatioSup]
  apply ciSup_le
  intro k
  have hT := nn_actual_tauFourier_pos hd p hchi hweak k
  have hden := nearestNeighborResolvent_den_pos hd0 hlam k
  have hw : tauFourier q k * (1 - susceptibilityWalkParameter q * nearestNeighborSymbol k) ≤
      2 := by
    have h := (le_ciSup (bddAbove_fourierRatio hd0 q hchi) k).trans hK
    exact (le_abs_self _).trans h
  have h := fourier_ratio_le_of_two_errors (by norm_num : (1 / 1000 : ℝ) < 1)
    (by norm_num : (0 : ℝ) ≤ 1 / 3) hm (nn_lace_cosine_abs_le hd p hchi hweak k)
    (nn_lace_cosine_variation_le hd p hchi hweak k) (nearestNeighborSymbol_abs_le_one hd0 k)
    (mul_nonneg (by positivity) p.2.1) hlam.1 hlam.2.le hT.le hw hn
    (nn_actual_fourier_equation hd p hchi hweak k)
  rw [abs_of_nonneg (mul_nonneg hT.le hden.le)]
  exact h.trans (nn_ratio_constant_le hlam.1 hlam.2.le
    (nn_step_mass_le_parameter_add hd p hchi hweak))

private theorem nn_symbol_differences (hd : 0 < d) (l k : Fin d → ℝ) :
    |nearestNeighborSymbol (l - k) + nearestNeighborSymbol (l + k) -
        2 * nearestNeighborSymbol l| ≤ 2 * (1 - nearestNeighborSymbol k) ∧
      (nearestNeighborSymbol (l + k) - nearestNeighborSymbol (l - k)) ^ 2 ≤
        16 * (1 - nearestNeighborSymbol l) * (1 - nearestNeighborSymbol k) := by
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have ha : HasSum (fun _ : Fin d => (d : ℝ)⁻¹) 1 := by
    convert hasSum_fintype (fun _ : Fin d => (d : ℝ)⁻¹) using 1
    simp [hdR]
  have hcos (t : Fin d → ℝ) : (∑' i, (d : ℝ)⁻¹ * cos (t i)) =
      nearestNeighborSymbol t := by
    simp only [tsum_fintype, nearestNeighborSymbol, Finset.mul_sum]
  have hm (t : Fin d → ℝ) : (∑' i, |(d : ℝ)⁻¹| * (1 - cos (t i))) =
      1 - nearestNeighborSymbol t := by
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (d : ℝ)⁻¹),
      tsum_mul_one_sub_cos_eq_one_sub_tsum_mul_cos ha t, hcos]
  constructor
  · simpa only [hcos, hm, nearestNeighborSymbol, Pi.sub_apply, Pi.add_apply] using
      abs_tsum_cos_second_difference_le ha.summable l k
  · simpa only [hcos, hm, nearestNeighborSymbol, Pi.sub_apply, Pi.add_apply] using
      tsum_cos_antisymmetric_difference_sq_le ha.summable l k

private theorem nn_lace_cosine_differences (hd : 50000 ≤ d) (p : unitInterval)
    (hchi : chi (homogeneousProfile (zdGraph d) p) 0 ≠ ⊤)
    (hweak : fourierBootstrap (homogeneousProfile (zdGraph d) p) ≤ 2) (l k : Fin d → ℝ) :
    let P := latticeCosineTransform (laceSum (homogeneousProfile (zdGraph d) p) 0)
    |P (l - k) + P (l + k) - 2 * P l| ≤ 2 * (1 / 3 : ℝ) * (1 - nearestNeighborSymbol k) ∧
      (P (l + k) - P (l - k)) ^ 2 ≤
        16 * (1 / 3 : ℝ) ^ 2 * (1 - nearestNeighborSymbol l) * (1 - nearestNeighborSymbol k) := by
  let q := homogeneousProfile (zdGraph d) p
  let P := latticeCosineTransform (laceSum q 0)
  let M (t : Fin d → ℝ) := ∑' y, |laceSum q 0 y| * (1 - cos (∑ i, t i * (y i : ℝ)))
  have hs := summable_laceSum q 0 (nn_total_coefficient_mass_ne_top hd p hchi hweak)
  have hM (t : Fin d → ℝ) : M t ≤ (1 / 3 : ℝ) * (1 - nearestNeighborSymbol t) :=
    nn_lace_cosine_moment_le hd p hchi hweak t
  have hM0 (t : Fin d → ℝ) : 0 ≤ M t :=
    tsum_nonneg fun y => mul_nonneg (abs_nonneg _) (sub_nonneg.mpr (cos_le_one _))
  have hg (t : Fin d → ℝ) : 0 ≤ 1 - nearestNeighborSymbol t :=
    sub_nonneg.mpr (abs_le.mp (nearestNeighborSymbol_abs_le_one (by omega) t)).2
  have hsecond : |P (l - k) + P (l + k) - 2 * P l| ≤ 2 * M k := by
    simpa only [P, M, latticeCosineTransform, Pi.sub_apply, Pi.add_apply, sub_mul,
      add_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib] using
      abs_tsum_cos_second_difference_le hs (fun y => ∑ i, l i * (y i : ℝ))
        (fun y => ∑ i, k i * (y i : ℝ))
  have hfirst : (P (l + k) - P (l - k)) ^ 2 ≤ 16 * M l * M k := by
    simpa only [P, M, latticeCosineTransform, Pi.sub_apply, Pi.add_apply, sub_mul,
      add_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib] using
      tsum_cos_antisymmetric_difference_sq_le hs (fun y => ∑ i, l i * (y i : ℝ))
        (fun y => ∑ i, k i * (y i : ℝ))
  constructor
  · exact hsecond.trans (by nlinarith [hM k])
  · apply hfirst.trans
    calc
      _ ≤ 16 * ((1 / 3 : ℝ) * (1 - nearestNeighborSymbol l)) *
          ((1 / 3 : ℝ) * (1 - nearestNeighborSymbol k)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (hM l) (by norm_num)) (hM k)
          (hM0 k) (mul_nonneg (by norm_num) (mul_nonneg (by norm_num) (hg l)))
      _ = _ := by ring

private theorem nn_difference_constants_le {j lam : ℝ}
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) (hj0 : 0 ≤ j) (hj : j ≤ lam + 1 / 999) :
    (17 / 10 : ℝ) ^ 2 *
        (j + (1 / 3) / (1 - 1 / 1000) ^ 2 + 8 * (1 / 3) ^ 2 / (1 - 1 / 1000) ^ 3) ≤ 72 ∧
      16 * (17 / 10 : ℝ) ^ 3 * (j + (1 / 3) / (1 - 1 / 1000) ^ 2) ^ 2 /
        (1 + lam) ≤ 72 := by
  constructor
  · norm_num at hj ⊢
    linarith
  · have hL : j + (1 / 3 : ℝ) / (1 - 1 / 1000) ^ 2 ≤ lam + 17 / 50 := by
      norm_num at hj ⊢
      linarith
    have hsq := pow_le_pow_left₀
      (show 0 ≤ j + (1 / 3 : ℝ) / (1 - 1 / 1000) ^ 2 by positivity) hL 2
    have hquot := (div_le_div_of_nonneg_right hsq
      (show 0 ≤ 1 + lam by linarith)).trans
      (sq_normalized_step_le hlam0 hlam1 (by norm_num : (0 : ℝ) ≤ 17 / 50) (by norm_num))
    calc
      _ = (16 * (17 / 10 : ℝ) ^ 3) *
          ((j + (1 / 3 : ℝ) / (1 - 1 / 1000) ^ 2) ^ 2 / (1 + lam)) := by ring
      _ ≤ (16 * (17 / 10 : ℝ) ^ 3) * ((1 + 17 / 50) ^ 2 / 2) :=
        mul_le_mul_of_nonneg_left hquot (by norm_num)
      _ ≤ 72 := by norm_num

private theorem nn_tauFourier_second_difference_le (hd : 50000 ≤ d) (p : unitInterval)
    (hchi : chi (homogeneousProfile (zdGraph d) p) 0 ≠ ⊤)
    (hweak : fourierBootstrap (homogeneousProfile (zdGraph d) p) ≤ 2) (k l : Fin d → ℝ) :
    let q := homogeneousProfile (zdGraph d) p
    |tauFourier q (l - k) + tauFourier q (l + k) - 2 * tauFourier q l| ≤
      (9 / 25 : ℝ) * bootstrapMajorant (susceptibilityWalkParameter q) k l := by
  let q := homogeneousProfile (zdGraph d) p
  let lam := susceptibilityWalkParameter q
  let P := latticeCosineTransform (laceSum q 0)
  let j := 2 * d * (p : ℝ)
  let E (t : Fin d → ℝ) := j * nearestNeighborSymbol t + P t / (1 + P t)
  let C := nearestNeighborResolvent (d := d) lam
  have hd0 : 0 < d := by omega
  have hlam : lam ∈ Set.Ico (0 : ℝ) 1 := susceptibilityWalkParameter_mem_Ico q hchi
  have hC (t : Fin d → ℝ) : 0 < C t := nearestNeighborResolvent_pos hd0 hlam t
  have hj0 : 0 ≤ j := mul_nonneg (by positivity) p.2.1
  have hj : j ≤ lam + 1 / 999 := nn_step_mass_le_parameter_add hd p hchi hweak
  have hP (t : Fin d → ℝ) : |P t| ≤ 1 / 1000 := nn_lace_cosine_abs_le hd p hchi hweak t
  have hrecip (t : Fin d → ℝ) : tauFourier q t = (1 - E t)⁻¹ := by
    apply (eq_effective_reciprocal (P := P t) ?_
      (nn_actual_fourier_equation hd p hchi hweak t)).2
    have h := (abs_le.mp (hP t)).1
    linarith
  have hE (t : Fin d → ℝ) : 0 < 1 - E t := by
    have h := nn_actual_tauFourier_pos hd p hchi hweak t
    rw [hrecip t] at h
    exact inv_pos.mp h
  have hK := nn_fourierRatioSup_le_seventeen_tenths hd p hchi hweak
  have hcomparison (t : Fin d → ℝ) : (1 - E t)⁻¹ ≤ (17 / 10 : ℝ) * C t := by
    rw [← hrecip t]
    exact (le_abs_self _).trans
      (abs_tauFourier_le_mul_resolvent_of_fourierRatioSup_le hd0 q hchi hK t)
  have hg (t : Fin d → ℝ) : 0 ≤ 1 - nearestNeighborSymbol t :=
    sub_nonneg.mpr (abs_le.mp (nearestNeighborSymbol_abs_le_one hd0 t)).2
  have hgl2 : 1 - nearestNeighborSymbol l ≤ 2 := by
    have h := (abs_le.mp (nearestNeighborSymbol_abs_le_one hd0 l)).1
    linarith
  have hD := nn_symbol_differences hd0 l k
  have hPd := nn_lace_cosine_differences hd p hchi hweak l k
  have hEd := effective_denominator_difference_bounds
    (by norm_num : (1 / 1000 : ℝ) < 1) (by norm_num : (0 : ℝ) ≤ 1 / 3) hj0
    (hP (l - k)) (hP l) (hP (l + k)) (hg l) hgl2 (hg k) hD.1 hD.2 hPd.1 hPd.2
  have hcancel : C l * (1 - nearestNeighborSymbol l) ≤ 2 / (1 + lam) := by
    have hwalk := walk_denominator_comparison hlam.2.le
      (abs_le.mp (nearestNeighborSymbol_abs_le_one hd0 l)).1
    have hden : C l * (1 - lam * nearestNeighborSymbol l) = 1 :=
      inv_mul_cancel₀ (nearestNeighborResolvent_den_pos hd0 hlam l).ne'
    apply (le_div_iff₀ (by linarith)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hwalk (hC l).le]
  have hraw := abs_effective_reciprocal_second_difference_le
    (hE (l - k)) (hE l) (hE (l + k)) (hC (l - k)).le (hC l).le (hC (l + k)).le
    (by norm_num : (0 : ℝ) ≤ 17 / 10) (hg k)
    (hcomparison (l - k)) (hcomparison l) (hcomparison (l + k)) hcancel hEd.1 hEd.2
  have hconstants := nn_difference_constants_le hlam.1 hlam.2.le hj0 hj
  change |tauFourier q (l - k) + tauFourier q (l + k) - 2 * tauFourier q l| ≤ _
  rw [hrecip (l - k), hrecip (l + k), hrecip l]
  apply hraw.trans
  calc
    _ ≤ (1 - nearestNeighborSymbol k) *
        (72 * (C (l - k) * C l + C l * C (l + k)) + 72 * (C (l - k) * C (l + k))) := by
      apply mul_le_mul_of_nonneg_left _ (hg k)
      exact add_le_add
        (mul_le_mul_of_nonneg_right hconstants.1
          (add_nonneg (mul_nonneg (hC (l - k)).le (hC l).le)
            (mul_nonneg (hC l).le (hC (l + k)).le)))
        (mul_le_mul_of_nonneg_right hconstants.2 (mul_nonneg (hC (l - k)).le (hC (l + k)).le))
    _ = _ := by dsimp only [bootstrapMajorant, bootstrapTripleProduct, C]; ring

/-- The actual second-difference ratio is at most `9/25`, after using the improved
Fourier ratio in the three reciprocal factors. -/
theorem nn_fourierDifferenceSup_le_nine_twenty_fifths (hd : 50000 ≤ d) (p : unitInterval)
    (hchi : chi (homogeneousProfile (zdGraph d) p) 0 ≠ ⊤)
    (hweak : fourierBootstrap (homogeneousProfile (zdGraph d) p) ≤ 2) :
    fourierDifferenceSup (homogeneousProfile (zdGraph d) p) ≤ 9 / 25 := by
  let q := homogeneousProfile (zdGraph d) p
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  have : Nonempty {t : (Fin d → ℝ) × (Fin d → ℝ) //
      0 < 1 - nearestNeighborSymbol t.1} :=
    ⟨⟨((fun _ => π), 0), by simp [nearestNeighborSymbol, hdR]⟩⟩
  rw [fourierDifferenceSup_def]
  apply ciSup_le
  intro t
  have hpos := bootstrapMajorant_pos (by omega : 0 < d)
    (susceptibilityWalkParameter_mem_Ico q hchi) (l := t.1.2) t.2
  apply (div_le_iff₀ hpos).mpr
  exact nn_tauFourier_second_difference_le hd p hchi hweak t.1.1 t.1.2

/-- In dimension at least `50000`, finite susceptibility and the canonical weak
bootstrap imply the strict improvement `F ≤ 17/10 < 2`. -/
theorem nn_fourierBootstrap_improves (hd : 50000 ≤ d) (p : unitInterval)
    (hchi : chi (homogeneousProfile (zdGraph d) p) 0 ≠ ⊤)
    (hweak : fourierBootstrap (homogeneousProfile (zdGraph d) p) ≤ 2) :
    fourierBootstrap (homogeneousProfile (zdGraph d) p) ≤ 17 / 10 := by
  apply (fourierBootstrap_le_iff _ _).mpr
  refine ⟨?_, nn_fourierRatioSup_le_seventeen_tenths hd p hchi hweak, ?_⟩
  · rw [rowSum_homogeneous_zdGraph,
      ENNReal.toReal_ofReal (mul_nonneg (by positivity) p.2.1)]
    exact (nn_step_mass_le_1001_div_1000 hd p hchi
      (nn_step_mass_le_of_fourierBootstrap_le p hweak)
      ((fourierBootstrap_le_iff _ _).mp hweak).2.1).trans (by norm_num)
  · exact (nn_fourierDifferenceSup_le_nine_twenty_fifths hd p hchi hweak).trans (by norm_num)

end PercLib.Percolation.Bond.Lace
