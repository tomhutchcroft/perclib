/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New proofs for this project; no upstream Lean code is copied.
-/
module

public import PercLib.Percolation.Bond.Lace.Bootstrap.NNScalarBounds
public import PercLib.Percolation.Bond.Lace.Diagrams.Convergence
public import PercLib.Percolation.Bond.Lace.Expansion.BootstrapAlgebra
public import PercLib.Percolation.Bond.Lace.Expansion.RealFourier

/-!
# Nearest-neighbour coefficient mass and step-mass improvement

The actual scalar diagram bounds imply summability of every lace coefficient
and a total mass at most `44/d`. Summing the proved canonical lace equation at
zero frequency then improves the actual step mass, without a weighted estimate.

## Main results

* `nn_laceCoefficient_total_mass_le`: the actual total coefficient mass is at most `44/d`.
* `nn_mass_normalization`: the canonical zero-frequency normalization.
* `nn_step_mass_le_250_div_239`: strict improvement below `21/20` for `d ≥ 1000`.
-/

@[expose] public section
noncomputable section

open PercLib.Analysis PercLib.Models.Site
open scoped ENNReal

namespace PercLib.Percolation.Bond.Lace

/-- The absolute mass of the canonical signed kernel is bounded by the total
nonnegative coefficient mass. No cancellation estimate is assumed. -/
theorem tsum_abs_laceSum_le_totalCoefficientMass {V : Type*}
    (q : Sym2 V → unitInterval) (x : V)
    (hmass : (∑' n : ℕ, ∑' y, laceCoefficient q n x y) ≠ ⊤) :
    (∑' y, |laceSum q x y|) ≤ (∑' n : ℕ, ∑' y, laceCoefficient q n x y).toReal := by
  have hswap : (∑' y, ∑' n : ℕ, laceCoefficient q n x y) ≠ ⊤ := by
    rwa [ENNReal.tsum_comm]
  have hrow (y : V) : (∑' n : ℕ, laceCoefficient q n x y) ≠ ⊤ :=
    ENNReal.ne_top_of_tsum_ne_top hswap y
  have hpoint (y : V) : |laceSum q x y| ≤
      (∑' n : ℕ, laceCoefficient q n x y).toReal := by
    have h := norm_tsum_le_tsum_norm (summable_signed_laceCoefficient q x y hmass).norm
    rw [ENNReal.tsum_toReal_eq (ENNReal.ne_top_of_tsum_ne_top (hrow y))]
    simpa only [laceSum, Real.norm_eq_abs, abs_mul, abs_pow, abs_neg, abs_one,
      one_pow, one_mul, abs_of_nonneg ENNReal.toReal_nonneg] using h
  have h := Summable.tsum_le_tsum hpoint (summable_laceSum q x hmass).abs
    (ENNReal.summable_toReal hswap)
  rw [← ENNReal.tsum_toReal_eq (ENNReal.ne_top_of_tsum_ne_top hswap),
    ENNReal.tsum_comm] at h
  exact h

variable {d : ℕ}

/-- The sharp factor-four zeroth diagram bound gives the explicit mass constant. -/
theorem nn_piZero_mass_le (hd : 1000 ≤ d) (p : unitInterval)
    (hchi : chi (homogeneousProfile (zdGraph d) p) 0 ≠ ⊤)
    (hj : 2 * d * (p : ℝ) ≤ 2)
    (hK : fourierRatioSup (homogeneousProfile (zdGraph d) p) ≤ 2) :
    (∑' y, piZero (homogeneousProfile (zdGraph d) p) 0 y) ≤
      ENNReal.ofReal (4441 / (420 * (d : ℝ))) := by
  let q := homogeneousProfile (zdGraph d) p
  have ht := nn_triangle_le hd p hchi hj hK
  have hfinite : (∑' y, piZero q 0 y) ≠ ⊤ :=
    (tsum_piZero_lt_top_of_triangle_lt_top q 0
      (lt_of_le_of_lt ht ENNReal.ofReal_lt_top)).ne
  apply (ENNReal.le_ofReal_iff_toReal_le hfinite (by positivity)).mpr
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    ((one_add_four_mul_tsum_piZero_le_triangle q 0).trans ht)
  rw [ENNReal.toReal_add ENNReal.one_ne_top
      (ENNReal.mul_ne_top (by norm_num) hfinite),
    ENNReal.toReal_mul, ENNReal.toReal_one, ENNReal.toReal_ofNat,
    ENNReal.toReal_ofReal (by positivity)] at h
  have he : (4441 : ℝ) / (105 * d) = 4 * (4441 / (420 * d)) := by ring
  rw [he] at h
  linarith

/-- The total mass of the actual nonnegative coefficients is at most `44/d`.
The estimate retains the sharp zeroth factor and the separate terminal norm. -/
theorem nn_laceCoefficient_total_mass_le (hd : 1000 ≤ d) (p : unitInterval)
    (hchi : chi (homogeneousProfile (zdGraph d) p) 0 ≠ ⊤)
    (hj : 2 * d * (p : ℝ) ≤ 2)
    (hK : fourierRatioSup (homogeneousProfile (zdGraph d) p) ≤ 2) :
    (∑' n : ℕ, ∑' y, laceCoefficient (homogeneousProfile (zdGraph d) p) n 0 y) ≤
      ENNReal.ofReal (44 / (d : ℝ)) := by
  let q := homogeneousProfile (zdGraph d) p
  have hdR : (1000 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by linarith
  have hα : (∑' a, diagramInitial q 0 a) ≤ ENNReal.ofReal (103 / 100 : ℝ) := by
    apply (nn_diagramInitial_mass_le hd p hchi hj hK).trans (ENNReal.ofReal_le_ofReal ?_)
    have hdiv : (8882 : ℝ) / (315 * d) ≤ 3 / 100 := by
      apply (div_le_iff₀ (by positivity)).mpr
      linarith
    linarith
  have hκ (a) : (∑' y, diagramTerminal q a y) ≤
      ENNReal.ofReal ((9197 / (315 * (d : ℝ))) * (203 / 200)) := by
    apply (nn_diagramTerminal_mass_le hd p hchi hj hK a).trans
      (ENNReal.ofReal_le_ofReal ?_)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hdiv : (4441 : ℝ) / (315 * d) ≤ 3 / 200 := by
      apply (div_le_iff₀ (by positivity)).mpr
      linarith
    linarith
  have h := tsum_laceCoefficient_all_mass_le_diagram q 0
    (ENNReal.ofReal (63 / 1000 : ℝ))
    (ENNReal.ofReal ((9197 / (315 * (d : ℝ))) * (203 / 200)))
    (nn_diagramTransfer_mass_le hd p hchi hj hK) hκ
  apply h.trans
  apply (add_le_add (nn_piZero_mass_le hd p hchi hj hK)
    (mul_le_mul' (mul_le_mul' hα le_rfl) le_rfl)).trans
  have hr : (1 - ENNReal.ofReal (63 / 1000 : ℝ))⁻¹ =
      ENNReal.ofReal (1000 / 937 : ℝ) := by
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 (by norm_num),
      ← ENNReal.ofReal_inv_of_pos (by norm_num)]
    norm_num
  rw [hr, ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have he : (4441 : ℝ) / (420 * d) + (103 / 100 * (1000 / 937)) *
      (9197 / (315 * d) * (203 / 200)) = (63679582 / 1475775) / d := by ring
  rw [he]
  exact div_le_div_of_nonneg_right (by norm_num) hdpos.le

/-- The actual coefficient estimate bounds the absolute mass of the canonical
infinite signed kernel by the same readable constant. -/
theorem nn_tsum_abs_laceSum_le (hd : 1000 ≤ d) (p : unitInterval)
    (hchi : chi (homogeneousProfile (zdGraph d) p) 0 ≠ ⊤)
    (hj : 2 * d * (p : ℝ) ≤ 2)
    (hK : fourierRatioSup (homogeneousProfile (zdGraph d) p) ≤ 2) :
    (∑' y, |laceSum (homogeneousProfile (zdGraph d) p) 0 y|) ≤ 44 / (d : ℝ) := by
  have hm := nn_laceCoefficient_total_mass_le hd p hchi hj hK
  have hf := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hm
  apply (tsum_abs_laceSum_le_totalCoefficientMass _ 0 hf).trans
  simpa only [ENNReal.toReal_ofReal (show 0 ≤ 44 / (d : ℝ) by positivity)] using
    ENNReal.toReal_mono ENNReal.ofReal_ne_top hm

/-- The zero-frequency equation gives the actual susceptibility normalization.
The denominator is nonzero because the proved coefficient mass is less than one. -/
theorem nn_mass_normalization (hd : 1000 ≤ d) (p : unitInterval)
    (hchi : chi (homogeneousProfile (zdGraph d) p) 0 ≠ ⊤)
    (hj : 2 * d * (p : ℝ) ≤ 2)
    (hK : fourierRatioSup (homogeneousProfile (zdGraph d) p) ≤ 2) :
    let q := homogeneousProfile (zdGraph d) p
    let m := ∑' y, laceSum q 0 y
    susceptibilityWalkParameter q = 2 * d * (p : ℝ) + m / (1 + m) := by
  let q := homogeneousProfile (zdGraph d) p
  let m := ∑' y, laceSum q 0 y
  have hd0 : 0 < d := by omega
  have hdR : (1000 : ℝ) ≤ d := by exact_mod_cast hd
  have heps : (44 : ℝ) / d < 1 := (div_lt_one (by linarith)).mpr (by linarith)
  have hmass := ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (nn_laceCoefficient_total_mass_le hd p hchi hj hK)
  have hm : |m| ≤ 44 / (d : ℝ) := by
    calc
      _ ≤ ∑' y, |laceSum q 0 y| := by
        simpa only [m, Real.norm_eq_abs] using
          norm_tsum_le_tsum_norm (summable_laceSum q 0 hmass).norm
      _ ≤ _ := nn_tsum_abs_laceSum_le hd p hchi hj hK
  have hmpos : 0 < 1 + m := by linarith [(abs_le.mp hm).1]
  have hτ : (∑' y, tau q 0 y) ≠ ⊤ := by rwa [← chi_eq_tsum_tau]
  have hχone : (1 : ℝ) ≤ (chi q 0).toReal := by
    simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono hchi (one_le_chi q 0)
  have hstep : (∑' y, (offDiagonal (fun a b : Fin d → ℤ =>
      (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) 0 y).toReal) = 2 * d * (p : ℝ) := by
    have h := latticeCosineTransform_homogeneous_zdGraph hd0 p 0
    simp only [q, nn_offDiagonal_toReal]
    simpa only [latticeCosineTransform_at_zero, nearestNeighborSymbol_at_zero hd0,
      mul_one] using h
  have heq := canonical_lace_real_fourier_equation q (homogeneous_zdGraph_add p)
    (nn_step_mass_ne_top p) hτ hmass (1 : AddChar (Fin d → ℤ) Circle)
  dsimp only at heq
  simp only [AddChar.one_apply, Circle.coe_one, Complex.one_re, mul_one] at heq
  rw [← ENNReal.tsum_toReal_eq (fun y =>
      ((tau_le_one q 0 y).trans_lt ENNReal.one_lt_top).ne),
    ← chi_eq_tsum_tau, hstep] at heq
  exact mass_normalization_of_lace_equation (ne_of_gt (lt_of_lt_of_le zero_lt_one hχone))
    hmpos.ne' heq

/-- The actual first bootstrap component keeps the susceptibility parameter and
its exact rational correction from the coefficient-mass estimate. -/
theorem nn_step_mass_le_normalization (hd : 1000 ≤ d) (p : unitInterval)
    (hchi : chi (homogeneousProfile (zdGraph d) p) 0 ≠ ⊤)
    (hj : 2 * d * (p : ℝ) ≤ 2)
    (hK : fourierRatioSup (homogeneousProfile (zdGraph d) p) ≤ 2) :
    2 * d * (p : ℝ) ≤ susceptibilityWalkParameter (homogeneousProfile (zdGraph d) p) +
      44 / ((d : ℝ) - 44) := by
  let q := homogeneousProfile (zdGraph d) p
  have hdR : (1000 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by linarith
  have heps : (44 : ℝ) / d < 1 := (div_lt_one hdpos).mpr (by linarith)
  have hmass := ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (nn_laceCoefficient_total_mass_le hd p hchi hj hK)
  have hm : |∑' y, laceSum q 0 y| ≤ 44 / (d : ℝ) := by
    calc
      _ ≤ ∑' y, |laceSum q 0 y| := by
        simpa only [Real.norm_eq_abs] using
          norm_tsum_le_tsum_norm (summable_laceSum q 0 hmass).norm
      _ ≤ _ := nn_tsum_abs_laceSum_le hd p hchi hj hK
  have h := mass_le_of_normalization heps hm (nn_mass_normalization hd p hchi hj hK)
  have he : (44 / (d : ℝ)) / (1 - 44 / d) = 44 / ((d : ℝ) - 44) := by
    field_simp
  rwa [he] at h

/-- The actual nearest-neighbour step mass is uniformly at most `250/239` at
all dimensions in the proved walk regime, strictly improving the weak bound two. -/
theorem nn_step_mass_le_250_div_239 (hd : 1000 ≤ d) (p : unitInterval)
    (hchi : chi (homogeneousProfile (zdGraph d) p) 0 ≠ ⊤)
    (hj : 2 * d * (p : ℝ) ≤ 2)
    (hK : fourierRatioSup (homogeneousProfile (zdGraph d) p) ≤ 2) :
    2 * d * (p : ℝ) ≤ 250 / 239 := by
  have hdR : (1000 : ℝ) ≤ d := by exact_mod_cast hd
  have hfrac : (44 : ℝ) / ((d : ℝ) - 44) ≤ 11 / 239 := by
    apply (div_le_iff₀ (by linarith)).mpr
    linarith
  have hlam := (susceptibilityWalkParameter_mem_Ico (homogeneousProfile (zdGraph d) p) hchi).2
  have h := nn_step_mass_le_normalization hd p hchi hj hK
  linarith

/-- A simple strict target for the first bootstrap component. -/
theorem nn_step_mass_lt_twenty_one_twentieths (hd : 1000 ≤ d) (p : unitInterval)
    (hchi : chi (homogeneousProfile (zdGraph d) p) 0 ≠ ⊤)
    (hj : 2 * d * (p : ℝ) ≤ 2)
    (hK : fourierRatioSup (homogeneousProfile (zdGraph d) p) ≤ 2) :
    2 * d * (p : ℝ) < 21 / 20 :=
  (nn_step_mass_le_250_div_239 hd p hchi hj hK).trans_lt (by norm_num)

end PercLib.Percolation.Bond.Lace
