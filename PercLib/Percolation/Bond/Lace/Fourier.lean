/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

New proofs for this project; no upstream Lean code is copied.
-/
module

public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Topology.Algebra.InfiniteSum.DiscreteConvolution
public import Mathlib.Tactic.LinearCombination

/-!
# Discrete Fourier algebra for an absolutely summable lace equation

## Main results

The Fourier sums are written inline using a unitary additive character, and
convolution is mathlib's existing `DiscreteConvolution.addRingConvolution`.
Absolute summability justifies grouping the product series by the sum of its
indices. No Fourier transform or convolution definition is introduced here.

The scalar quotient lemmas assume an already established transformed equation.
They do not assert that the canonical lace coefficients satisfy that equation.
-/

@[expose] public section
noncomputable section

open scoped BigOperators

namespace PercLib.Percolation.Bond.Lace

/-- A unitary character sends discrete convolution to multiplication of Fourier
sums. The two kernels are absolutely summable; no positivity is required. -/
theorem tsum_addRingConvolution_mul_addChar {G : Type*} [AddCommGroup G] [Countable G]
    (f g : G → ℂ) (ψ : AddChar G Circle)
    (hf : Summable fun x => ‖f x‖) (hg : Summable fun x => ‖g x‖) :
    (∑' x, DiscreteConvolution.addRingConvolution f g x * (ψ x : ℂ)) =
      (∑' x, f x * (ψ x : ℂ)) * (∑' x, g x * (ψ x : ℂ)) := by
  have hfψ : Summable fun x => ‖f x * (ψ x : ℂ)‖ := by
    simpa only [norm_mul, Circle.norm_coe, mul_one] using hf
  have hgψ : Summable fun x => ‖g x * (ψ x : ℂ)‖ := by
    simpa only [norm_mul, Circle.norm_coe, mul_one] using hg
  have hprod := summable_mul_of_summable_norm hfψ hgψ
  have hsum := (hfψ.of_norm.hasSum.mul hgψ.of_norm.hasSum hprod).tsum_fiberwise
    (fun p : G × G => p.1 + p.2)
  have hfiber (x : G) :
      (∑' p : (fun p : G × G => p.1 + p.2) ⁻¹' {x},
        (f p.val.1 * (ψ p.val.1 : ℂ)) * (g p.val.2 * (ψ p.val.2 : ℂ))) =
        DiscreteConvolution.addRingConvolution f g x * (ψ x : ℂ) := by
    have hset : (fun p : G × G => p.1 + p.2) ⁻¹' {x} =
        DiscreteConvolution.addFiber x := by
      ext p
      simp only [Set.mem_preimage, Set.mem_singleton_iff, DiscreteConvolution.mem_addFiber]
    rw [hset, DiscreteConvolution.addRingConvolution_apply, ← tsum_mul_right]
    apply tsum_congr
    intro p
    have hp : p.val.1 + p.val.2 = x := DiscreteConvolution.mem_addFiber.mp p.property
    have hψ : (ψ p.val.1 : ℂ) * (ψ p.val.2 : ℂ) = (ψ x : ℂ) := by
      simpa only [AddChar.map_add_eq_mul, Circle.coe_mul] using
        congrArg (fun z => (ψ z : ℂ)) hp
    rw [← hψ]
    ring
  simp_rw [hfiber] at hsum
  exact hsum.tsum_eq

/-- The lace denominator is nonzero whenever the transformed scalar equation
holds. This conclusion needs no independent nonvanishing assumption. -/
theorem lace_fourier_denominator_ne_zero {T P J : ℂ}
    (h : T = 1 + P + (1 + P) * J * T) : 1 - (1 + P) * J ≠ 0 := by
  have hlin : (1 - (1 + P) * J) * T = 1 + P := by
    linear_combination h
  intro hzero
  have hp : 1 + P = 0 := by
    simpa only [hzero, zero_mul] using hlin.symm
  simp only [hp, zero_mul, sub_zero, one_ne_zero] at hzero

/-- Solving an established transformed lace equation gives the usual quotient.
The premise is scalar algebra, not a claim of a canonical lace expansion. -/
theorem eq_lace_fourier_quotient {T P J : ℂ}
    (h : T = 1 + P + (1 + P) * J * T) :
    T = (1 + P) / (1 - (1 + P) * J) := by
  apply (eq_div_iff (lace_fourier_denominator_ne_zero h)).2
  linear_combination h

end PercLib.Percolation.Bond.Lace
