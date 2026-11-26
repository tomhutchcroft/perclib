/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New proofs for this project; no upstream Lean code is copied.
-/
module

public import PercLib.Percolation.Bond.Lace.Expansion.Fourier
public import Mathlib.Algebra.Group.EvenFunction

/-!
# Exact character-deficit moments of convolution

The real part of a unitary character gives the cosine weight without a choice of phase.
For real summable kernels, evenness of one factor makes its Fourier transform real.
The convolution moment identity retains that signed real Fourier multiplier.

## Main results

* `im_tsum_ofReal_mul_addChar_eq_zero_of_even`: an even real kernel has a real transform.
* `tsum_addRingConvolution_mul_one_sub_re_addChar`: the general moment identity.
* `tsum_addRingConvolution_mul_one_sub_re_addChar_of_hasSum_one`: normalization gives
  the probability-kernel form. Nonnegative even kernels are included without extra hypotheses.
-/

@[expose] public section
noncomputable section

open scoped ComplexConjugate

namespace PercLib.Percolation.Bond.Lace

variable {G : Type*} [AddCommGroup G]

/-- Real embedding commutes with the existing discrete convolution. -/
theorem ofReal_addRingConvolution (f b : G → ℝ) (x : G) :
    ((DiscreteConvolution.addRingConvolution f b x : ℝ) : ℂ) =
      DiscreteConvolution.addRingConvolution (fun y => (f y : ℂ))
        (fun y => (b y : ℂ)) x := by
  simp only [DiscreteConvolution.addRingConvolution_apply,
    Complex.ofReal_tsum, Complex.ofReal_mul]

/-- Real summable kernels have a summable convolution. -/
theorem summable_addRingConvolution_real {f b : G → ℝ} (hf : Summable f) (hb : Summable b) :
    Summable (DiscreteConvolution.addRingConvolution f b) := by
  have hfC : Summable (fun x => ‖(f x : ℂ)‖) := by simpa using hf.norm
  have hbC : Summable (fun x => ‖(b x : ℂ)‖) := by simpa using hb.norm
  apply Complex.summable_ofReal.mp
  simpa only [ofReal_addRingConvolution] using
    (summable_norm_addRingConvolution (fun x => (f x : ℂ))
      (fun x => (b x : ℂ)) hfC hbC).of_norm

/-- A summable real kernel remains summable after multiplication by a unitary character. -/
theorem summable_ofReal_mul_addChar {f : G → ℝ} (hf : Summable f) (ψ : AddChar G Circle) :
    Summable (fun x => (f x : ℂ) * (ψ x : ℂ)) := by
  apply hf.norm.of_norm_bounded
  intro x
  simp only [norm_mul, Circle.norm_coe, mul_one, Complex.norm_real, le_refl]

/-- Taking the real part of a character transform commutes with summation. -/
theorem re_tsum_ofReal_mul_addChar {f : G → ℝ} (hf : Summable f) (ψ : AddChar G Circle) :
    (∑' x, (f x : ℂ) * (ψ x : ℂ)).re = ∑' x, f x * (ψ x : ℂ).re := by
  rw [Complex.re_tsum (summable_ofReal_mul_addChar hf ψ)]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

/-- The imaginary part of the transform of an even real kernel vanishes. Summability
is not needed for this symmetry identity because the character has unit modulus. -/
theorem im_tsum_ofReal_mul_addChar_eq_zero_of_even {f : G → ℝ}
    (heven : Function.Even f) (ψ : AddChar G Circle) :
    (∑' x, (f x : ℂ) * (ψ x : ℂ)).im = 0 := by
  have hconj : conj (∑' x, (f x : ℂ) * (ψ x : ℂ)) =
      ∑' x, (f x : ℂ) * (ψ x : ℂ) := by
    rw [Complex.conj_tsum]
    calc
      _ = ∑' x, (f (-x) : ℂ) * (ψ (-x) : ℂ) := by
        apply tsum_congr
        intro x
        rw [heven x, AddChar.map_neg_eq_inv, Circle.coe_inv_eq_conj]
        simp
      _ = _ := (Equiv.neg G).tsum_eq (fun x => (f x : ℂ) * (ψ x : ℂ))
  have hi : -(∑' x, (f x : ℂ) * (ψ x : ℂ)).im =
      (∑' x, (f x : ℂ) * (ψ x : ℂ)).im := by
    simpa using congrArg Complex.im hconj
  linarith

/-- The character-deficit moment is the mass minus the real Fourier transform. -/
theorem tsum_mul_one_sub_re_addChar_eq_sub {f : G → ℝ}
    (hf : Summable f) (ψ : AddChar G Circle) :
    (∑' x, f x * (1 - (ψ x : ℂ).re)) =
      (∑' x, f x) - (∑' x, (f x : ℂ) * (ψ x : ℂ)).re := by
  have hre : Summable (fun x => f x * (ψ x : ℂ).re) := by
    simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      using (Complex.hasSum_re (summable_ofReal_mul_addChar hf ψ).hasSum).summable
  simp_rw [mul_sub, mul_one]
  rw [hf.tsum_sub hre, re_tsum_ofReal_mul_addChar hf ψ]

variable [Countable G]

/-- If one real convolution factor is even, the real Fourier transforms multiply exactly. -/
theorem tsum_addRingConvolution_mul_re_addChar_of_even {f b : G → ℝ}
    (hf : Summable f) (hb : Summable b) (heven : Function.Even f) (ψ : AddChar G Circle) :
    (∑' x, DiscreteConvolution.addRingConvolution f b x * (ψ x : ℂ).re) =
      (∑' x, f x * (ψ x : ℂ).re) * ∑' x, b x * (ψ x : ℂ).re := by
  have hfC : Summable (fun x => ‖(f x : ℂ)‖) := by simpa using hf.norm
  have hbC : Summable (fun x => ‖(b x : ℂ)‖) := by simpa using hb.norm
  have h := congrArg Complex.re (tsum_addRingConvolution_mul_addChar
    (fun x => (f x : ℂ)) (fun x => (b x : ℂ)) ψ hfC hbC)
  simp_rw [← ofReal_addRingConvolution] at h
  rw [Complex.mul_re, im_tsum_ofReal_mul_addChar_eq_zero_of_even heven ψ,
    zero_mul, sub_zero, re_tsum_ofReal_mul_addChar (summable_addRingConvolution_real hf hb) ψ,
    re_tsum_ofReal_mul_addChar hf ψ, re_tsum_ofReal_mul_addChar hb ψ] at h
  exact h

/-- The exact deficit moment of a convolution. Only the first factor needs to be even,
and neither factor needs to be nonnegative. The real Fourier multiplier keeps its sign. -/
theorem tsum_addRingConvolution_mul_one_sub_re_addChar {f b : G → ℝ}
    (hf : Summable f) (hb : Summable b) (heven : Function.Even f) (ψ : AddChar G Circle) :
    (∑' x, DiscreteConvolution.addRingConvolution f b x * (1 - (ψ x : ℂ).re)) =
      (∑' x, f x * (1 - (ψ x : ℂ).re)) * (∑' x, b x) +
        (∑' x, (f x : ℂ) * (ψ x : ℂ)).re * (∑' x, b x * (1 - (ψ x : ℂ).re)) := by
  have hmass := tsum_addRingConvolution_mul_re_addChar_of_even hf hb heven (1 : AddChar G Circle)
  simp only [AddChar.one_apply, Circle.coe_one, Complex.one_re, mul_one] at hmass
  rw [tsum_mul_one_sub_re_addChar_eq_sub (summable_addRingConvolution_real hf hb) ψ,
    tsum_mul_one_sub_re_addChar_eq_sub hf ψ, tsum_mul_one_sub_re_addChar_eq_sub hb ψ,
    re_tsum_ofReal_mul_addChar (summable_addRingConvolution_real hf hb) ψ,
    tsum_addRingConvolution_mul_re_addChar_of_even hf hb heven ψ, hmass,
    re_tsum_ofReal_mul_addChar hf ψ, re_tsum_ofReal_mul_addChar hb ψ]
  ring

/-- For a normalized even first factor, the convolution moment consists of its deficit
times the second mass, plus its signed real transform times the second moment. -/
theorem tsum_addRingConvolution_mul_one_sub_re_addChar_of_hasSum_one {D b : G → ℝ}
    (hD : HasSum D 1) (hb : Summable b) (heven : Function.Even D) (ψ : AddChar G Circle) :
    (∑' x, DiscreteConvolution.addRingConvolution D b x * (1 - (ψ x : ℂ).re)) =
      (1 - (∑' x, (D x : ℂ) * (ψ x : ℂ)).re) * (∑' x, b x) +
        (∑' x, (D x : ℂ) * (ψ x : ℂ)).re * (∑' x, b x * (1 - (ψ x : ℂ).re)) := by
  rw [tsum_addRingConvolution_mul_one_sub_re_addChar hD.summable hb heven ψ,
    tsum_mul_one_sub_re_addChar_eq_sub hD.summable ψ, hD.tsum_eq]

end PercLib.Percolation.Bond.Lace
