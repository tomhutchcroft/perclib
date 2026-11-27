/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Original proofs moved from the lace-expansion character moment module.
-/
module

public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Algebra.Group.EvenFunction
public import Mathlib.Tactic.Linarith

/-!
# Real kernels and unitary character series

## Main results

* `summable_ofReal_mul_addChar`: a unitary character preserves absolute summability.
* `re_tsum_ofReal_mul_addChar`: the real part commutes with a summable character series.
* `im_tsum_ofReal_mul_addChar_eq_zero_of_even`: even real kernels have real transforms.

These group-level facts are independent of the percolation model.
-/

@[expose] public section

noncomputable section

open scoped ComplexConjugate

namespace PercLib.Analysis

variable {G : Type*} [AddCommGroup G]

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

end PercLib.Analysis
