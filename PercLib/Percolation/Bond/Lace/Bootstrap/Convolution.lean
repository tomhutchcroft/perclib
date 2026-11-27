/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New proofs for this project; no upstream Lean code is copied.
-/
module

public import PercLib.Analysis.LatticeFourier.PhysicalInversion
public import PercLib.Percolation.Bond.Lace.Expansion.ConvolutionWeight

/-!
# Physical-frequency integrals for discrete convolution

## Main results

The actual cosine transform sends convolution to multiplication when the first
factor is even. For two summable even real kernels, coefficient recovery bounds
the convolution by the normalized integral of the absolute transform product.
-/

@[expose] public section
noncomputable section

open MeasureTheory Metric Real
open PercLib.Analysis

namespace PercLib.Percolation.Bond.Lace

/-- The cosine transform of a convolution factors when its first kernel is even. -/
theorem latticeCosineTransform_addRingConvolution {d : ℕ}
    {f g : (Fin d → ℤ) → ℝ} (hf : Summable f) (hg : Summable g)
    (heven : Function.Even f) (k : Fin d → ℝ) :
    latticeCosineTransform (DiscreteConvolution.addRingConvolution f g) k =
      latticeCosineTransform f k * latticeCosineTransform g k := by
  simpa only [latticeCharacter_re, latticeCosineTransform] using
    tsum_addRingConvolution_mul_re_addChar_of_even hf hg heven (latticeCharacter k)

/-- The exact physical normalization in a convolution coefficient bound. -/
theorem abs_addRingConvolution_le_normalized_integral {d : ℕ}
    {f g : (Fin d → ℤ) → ℝ} (hf : Summable f) (hg : Summable g)
    (hfeven : Function.Even f) (hgeven : Function.Even g) (x : Fin d → ℤ) :
    |DiscreteConvolution.addRingConvolution f g x| ≤ ((2 * π) ^ d)⁻¹ *
      ∫ k in ball (0 : Fin d → ℝ) π,
        |latticeCosineTransform f k * latticeCosineTransform g k| := by
  have hfC : Summable (fun n => ‖(f n : ℂ)‖) := by simpa using hf.norm
  have hgC : Summable (fun n => ‖(g n : ℂ)‖) := by simpa using hg.norm
  have h := norm_le_integral_norm_tsum_mFourier
    (DiscreteConvolution.addRingConvolution (fun n => (f n : ℂ)) (fun n => (g n : ℂ)))
    (summable_norm_addRingConvolution _ _ hfC hgC) x
  rw [integral_unitTorus_eq_normalized_box] at h
  simp_rw [mFourier_div_two_pi_eq_latticeCharacter,
    tsum_addRingConvolution_mul_addChar _ _ _ hfC hgC,
    tsum_mul_latticeCharacter_eq_cosineTransform hf hfeven,
    tsum_mul_latticeCharacter_eq_cosineTransform hg hgeven,
    ← Complex.ofReal_mul, Complex.norm_real, Real.norm_eq_abs] at h
  simpa only [← ofReal_addRingConvolution, Complex.norm_real, Real.norm_eq_abs,
    smul_eq_mul] using h

end PercLib.Percolation.Bond.Lace
