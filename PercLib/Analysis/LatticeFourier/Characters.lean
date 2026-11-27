/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New proofs for this project; no upstream Lean code is copied.
-/
module

public import PercLib.Analysis.LatticeFourier.Defs
public import PercLib.Analysis.CharacterSeries
public import Mathlib.Analysis.Fourier.AddCircleMulti
public import Mathlib.Tactic.FieldSimp

/-!
# Lattice characters, cosine transforms, and torus monomials

## Main results

* `tsum_mul_latticeCharacter_eq_cosineTransform`: the complex transform of a summable
  even real kernel is its real cosine transform.
* `mFourier_div_two_pi_eq_latticeCharacter`: mathlib's torus monomial in physical frequencies.
* `tsum_mul_mFourier_div_two_pi_eq_cosineTransform`: the resulting real torus series formula.

Physical frequencies use the character `exp(i k·x)`; the normalized torus coordinate
is `k / (2 pi)`. No choice of frequency representatives is required.
-/

@[expose] public section

noncomputable section

open UnitAddTorus

namespace PercLib.Analysis

variable {ι : Type*} [Fintype ι]

/-- The real part of the canonical character series is the existing cosine transform. -/
theorem re_tsum_mul_latticeCharacter {f : (ι → ℤ) → ℝ} (hf : Summable f) (k : ι → ℝ) :
    (∑' x, (f x : ℂ) * (latticeCharacter k x : ℂ)).re = latticeCosineTransform f k := by
  rw [re_tsum_ofReal_mul_addChar hf]
  simp only [latticeCharacter_re, latticeCosineTransform]

/-- For summable even real kernels, the canonical complex character series is real
and agrees with the existing cosine transform. -/
theorem tsum_mul_latticeCharacter_eq_cosineTransform {f : (ι → ℤ) → ℝ}
    (hf : Summable f) (heven : Function.Even f) (k : ι → ℝ) :
    (∑' x, (f x : ℂ) * (latticeCharacter k x : ℂ)) =
      (latticeCosineTransform f k : ℂ) := by
  apply Complex.ext
  · simpa only [Complex.ofReal_re] using re_tsum_mul_latticeCharacter hf k
  · simpa only [Complex.ofReal_im] using
      im_tsum_ofReal_mul_addChar_eq_zero_of_even heven (latticeCharacter k)

/-- Mathlib's normalized-torus monomial is the canonical lattice character after
the exact physical-frequency rescaling by `2 pi`. -/
theorem mFourier_div_two_pi_eq_latticeCharacter (x : ι → ℤ) (k : ι → ℝ) :
    mFourier x (fun i => ((k i / (2 * Real.pi) : ℝ) : UnitAddCircle)) =
      (latticeCharacter k x : ℂ) := by
  simp only [mFourier, ContinuousMap.coe_mk, fourier_coe_apply,
    latticeCharacter_coe_apply]
  rw [← Complex.exp_sum]
  congr 1
  rw [Complex.ofReal_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  push_cast
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp

/-- The physical-frequency torus series of a summable even real kernel is the
complex embedding of its cosine transform. -/
theorem tsum_mul_mFourier_div_two_pi_eq_cosineTransform {f : (ι → ℤ) → ℝ}
    (hf : Summable f) (heven : Function.Even f) (k : ι → ℝ) :
    (∑' x, (f x : ℂ) *
      mFourier x (fun i => ((k i / (2 * Real.pi) : ℝ) : UnitAddCircle))) =
        (latticeCosineTransform f k : ℂ) := by
  simp_rw [mFourier_div_two_pi_eq_latticeCharacter]
  exact tsum_mul_latticeCharacter_eq_cosineTransform hf heven k

end PercLib.Analysis
