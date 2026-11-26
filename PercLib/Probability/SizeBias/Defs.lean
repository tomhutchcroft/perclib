/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
The size-biased law of a nonnegative random variable. New for this project against pinned
mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; no upstream code is copied. The law is
mathlib's `Measure.withDensity` with density `X / E X`. Mathematical reference: the standard
size-biased (length-biased) law, e.g. Lyons and Peres, *Probability on Trees and Networks*,
Chapter 12.
-/
module

public import PercLib.Meta.Tag
public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Size-biased laws

For a measure `P` and a random variable `X : Ω → ℝ≥0∞`, `sizeBiased P X` is the measure with
density `X / E X` with respect to `P`, so that `P̂(A) = E[X 𝟙_A] / E X`. Random variables are
`ℝ≥0∞`-valued and expectations are lower Lebesgue integrals.

## Main definitions

* `sizeBiased P X`: the size-biased law of `X` under `P`.

## Main results

* `sizeBiased_apply`: `P̂(A) = E[X; A] / E X`.
* `isProbabilityMeasure_sizeBiased`: if `0 < E X < ∞` then `P̂` is a probability measure.
* `lintegral_sizeBiased`: `Ê F = E[X F] / E X` for measurable `F ≥ 0`.
* `lintegral_self_sizeBiased`: `Ê X = E X² / E X`, with `E X²` allowed to be infinite.
* `sizeBiased_zero`, `sizeBiased_one`: the trivial cases.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace PercLib.Probability

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Size-biased law.** The size-biased law of a random variable `X ≥ 0` under `P` is
`P̂(A) = E[X 𝟙_A] / E X`, the measure with density `X / E X`. It is a probability measure
when `0 < E X < ∞` (`isProbabilityMeasure_sizeBiased`); otherwise the formula supplies no
normalisation (for `E X = ∞` the density vanishes and `P̂ = 0`). -/
@[tag "6L9Z"]
def sizeBiased (P : Measure Ω) (X : Ω → ℝ≥0∞) : Measure Ω :=
  P.withDensity fun ω => X ω / ∫⁻ ω, X ω ∂P

theorem sizeBiased_def (P : Measure Ω) (X : Ω → ℝ≥0∞) :
    sizeBiased P X = P.withDensity fun ω => X ω / ∫⁻ ω, X ω ∂P :=
  rfl

/-- `P̂(A) = E[X; A] / E X` for a measurable set `A`. -/
theorem sizeBiased_apply (P : Measure Ω) {X : Ω → ℝ≥0∞} (hX : Measurable X) {s : Set Ω}
    (hs : MeasurableSet s) :
    sizeBiased P X s = (∫⁻ ω in s, X ω ∂P) / ∫⁻ ω, X ω ∂P := by
  rw [sizeBiased, withDensity_apply _ hs]
  simp_rw [div_eq_mul_inv]
  exact lintegral_mul_const _ hX

theorem sizeBiased_absolutelyContinuous (P : Measure Ω) (X : Ω → ℝ≥0∞) :
    sizeBiased P X ≪ P :=
  withDensity_absolutelyContinuous _ _

/-- The size-biased law of `X ≥ 0` with `0 < E X < ∞` is a probability measure. -/
theorem isProbabilityMeasure_sizeBiased (P : Measure Ω) {X : Ω → ℝ≥0∞}
    (hX : Measurable X) (h0 : ∫⁻ ω, X ω ∂P ≠ 0) (htop : ∫⁻ ω, X ω ∂P ≠ ∞) :
    IsProbabilityMeasure (sizeBiased P X) := by
  constructor
  rw [sizeBiased_apply P hX MeasurableSet.univ, Measure.restrict_univ, ENNReal.div_self h0 htop]

/-- Expectations under the size-biased law: `Ê F = E[X F] / E X` for measurable `F ≥ 0`. -/
theorem lintegral_sizeBiased (P : Measure Ω) {X F : Ω → ℝ≥0∞} (hX : Measurable X)
    (hF : Measurable F) :
    ∫⁻ ω, F ω ∂sizeBiased P X = (∫⁻ ω, X ω * F ω ∂P) / ∫⁻ ω, X ω ∂P := by
  rw [sizeBiased, lintegral_withDensity_eq_lintegral_mul _ (hX.div_const _) hF]
  simp_rw [div_eq_mul_inv]
  rw [← lintegral_mul_const _ (show Measurable fun ω => X ω * F ω from hX.mul hF)]
  congr 1 with ω
  simp only [Pi.mul_apply]
  ring

/-- The size-biased mean: `Ê X = E X² / E X`, with `E X²` allowed to be infinite. -/
theorem lintegral_self_sizeBiased (P : Measure Ω) {X : Ω → ℝ≥0∞} (hX : Measurable X) :
    ∫⁻ ω, X ω ∂sizeBiased P X = (∫⁻ ω, X ω ^ 2 ∂P) / ∫⁻ ω, X ω ∂P := by
  rw [lintegral_sizeBiased P hX hX]
  simp_rw [pow_two]

@[simp]
theorem sizeBiased_zero (P : Measure Ω) : sizeBiased P 0 = 0 := by
  simp [sizeBiased]

/-- Size bias by the constant `1` does not change a probability measure. -/
@[simp]
theorem sizeBiased_one (P : Measure Ω) [IsProbabilityMeasure P] : sizeBiased P 1 = P := by
  simp only [sizeBiased, Pi.one_apply, lintegral_const, measure_univ, mul_one, div_one]
  exact withDensity_one

end PercLib.Probability
